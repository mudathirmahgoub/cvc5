/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include "theory/bags/bags_rewriter.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <unordered_set>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/node_algorithm.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/rewriter.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"
#include "util/statistics_registry.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

/*
 * Notation. The comments of this file write terms in SMT-LIB, with cvc5's
 * operators for tuples, nullables, bags and tables:
 *
 *   (tuple a b)                     a row of sort (Tuple Int Int)
 *   ((_ tuple.select 1) t)          column 1 of the row t
 *   ((_ tuple.project 0 2) t)       the row of columns 0 and 2 of t
 *   (nullable.some 5)               a value of sort (Nullable Int)
 *   (as nullable.null (Nullable Int))
 *   (nullable.is_some x), (nullable.val x)
 *   (bag e 2)                       the bag with e twice (Kind::BAG_MAKE)
 *   (as bag.empty (Bag Int))
 *   (bag.count e X)                 the multiplicity of e in X
 *   (bag.union_disjoint X Y)        multiplicities added
 *   (bag.inter_min X Y)             the smaller multiplicity of the two
 *   (bag.difference_subtract X Y)   multiplicities subtracted, down to 0
 *   (bag.setof X)                   X with every multiplicity cut to 1
 *   (bag.map f X)                   (f t) for every row t of X,
 *                                   multiplicities of equal images added
 *   (bag.filter p X)                the rows t of X with (p t)
 *   (bag.fold f i X)                f folded over the rows of X, from i
 *   (table.product X Y)             the rows of X followed by those of Y
 *   ((_ table.project 0 2) X)       the map of X by tuple.project 0 2
 *   ((_ table.aggr 0) f i X)        X split into the groups of its rows
 *                                   with the same column 0, each group
 *                                   folded as by bag.fold from i
 *
 * X, Y and Z are tables (bags of tuples), t and s rows bound by a lambda, acc
 * an accumulator, and a, b, c terms. The examples of the rules, with the sorts
 * of their symbols, are at their Rewrite ids in rewrites.h; the comments here
 * say how a rule is implemented. The rewriter makes its own bound variables,
 * named row_N, t_N and acc_N. SQL's three-valued logic is encoded with
 * (Nullable Bool): a predicate p holds of a row when p is (nullable.some true),
 * see truthOf.
 */

/**
 * The keys of a table constant X: an SEXPR of SEXPRs of column indices, one per
 * key, recorded by recordKey from the key's assertion. For
 * X : (Bag (Tuple Int Int Int)), the assertion that columns 0 and 2 are a key
 * is
 *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
 * and X then gets the attribute (SEXPR (SEXPR 0 2)).
 *
 * A key of a table is a set of columns that no two rows of the table agree
 * on, a row that occurs twice counting as two rows; so a table with a key has
 * no row twice. A table constant is a free constant of a table sort, as
 * X above, declared by (declare-const X (Bag (Tuple Int Int Int))); the code
 * tests for one with isVar(). The attribute is stored on the node X, and
 * keysOf reads it back, as {{0, 2}} for the example above.
 */
struct BagsKeysAttributeId
{
};
typedef expr::Attribute<BagsKeysAttributeId, Node> BagsKeysAttribute;
/**
 * A term of an assertion that the rewriter reads a fact from: the bag.setof of
 * a key assertion, or the bag.filter of a NOT NULL assertion (see recordFacts).
 * Such a term is never rewritten: the fact it states would justify rewriting it
 * away (the set of the projection onto a key is the projection itself), and the
 * assertion would become true and the fact lost.
 *
 * For instance, once column 1 of X is known never null, NOT_NULL_COLUMNS
 * would rewrite the predicate of the NOT NULL assertion below,
 * (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))), to false,
 * the filter to the empty bag, and the assertion to true: the solver would
 * no longer be told the fact that the rewrites rely on. The attribute is true
 * on such a term; rewriteSetof and postRewriteFilter return a term that has
 * it unchanged.
 */
struct BagsKeyTermAttributeId
{
};
typedef expr::Attribute<BagsKeyTermAttributeId, bool> BagsKeyTermAttribute;
/**
 * The columns of a table constant X that hold no null: an SEXPR of column
 * indices, recorded by recordNotNull. For X : (Bag (Tuple Int (Nullable Int))),
 * the assertion that column 1 is NOT NULL is
 *   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
 *                    (= ((_ tuple.select 1) t)
 *                       (as nullable.null (Nullable Int))))
 *                  X)
 *      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
 * and X then gets the attribute (SEXPR 1).
 *
 * nonNullColumns reads it, for a table constant and for the terms built
 * over one.
 */
struct BagsNotNullAttributeId
{
};
typedef expr::Attribute<BagsNotNullAttributeId, Node> BagsNotNullAttribute;

namespace {
/**
 * Whether n is the null of a nullable sort, e.g.
 * (as nullable.null (Nullable Int)), the constructor of no argument.
 *
 * The test is on the shape of the node, not on its value: true for
 * (as nullable.null (Nullable Int)), and false for (nullable.some 5), whose
 * constructor has an argument, and for a free constant y : (Nullable Int),
 * which may or may not be null. The sort test rules out the constructors of
 * no argument of other datatypes, as the empty tuple.
 */
bool isNullConstant(const Node& n)
{
  return n.getKind() == Kind::APPLY_CONSTRUCTOR && n.getNumChildren() == 0
         && n.getType().isNullable();
}

/**
 * Whether t is a tuple term, (tuple a b): the rules read columns only of the
 * rows and the accumulators that are tuples, not of another datatype, as the
 * (nullable.some a) of an accumulator of sort (Nullable Int).
 *
 * That is, whether t is built by the tuple constructor, so that its child j
 * is its column j. For instance, true for (tuple 1 (nullable.some 2)) of sort
 * (Tuple Int (Nullable Int)); false for (nullable.some 2), also a constructor
 * term but of the datatype (Nullable Int); and false for a row variable t or
 * ((_ tuple.project 0 1) t), which have a tuple sort but are not built by the
 * constructor. The rules test it before they read the columns of a lambda's
 * body or of an initial value child by child.
 */
bool isTupleTerm(const Node& t)
{
  return t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getType().isTuple();
}

/**
 * The bound variable of type tn that the rewriter uses for role and key n,
 * one per (role, n, tn): the variable of id BAGS_FIRST_INDEX cached on
 * (SEXPR role n), role a string constant. The reductions of bags, the other
 * users of that id, cache on the bag terms they reduce, never on an SEXPR.
 *
 * The BoundVarManager returns the same variable for the same id, cache node
 * and sort, so every call with the same role, n and tn returns the same
 * variable. Rewriting the same term twice then builds the same lambda node,
 * which a fresh variable at each call would not. The role keeps apart
 * variables of different uses that share n: for instance, with n the integer
 * constant 0 and tn the sort Int, the roles "alpha-free" and "alpha-bound"
 * give two different variables, cached on (SEXPR "alpha-free" 0) and
 * (SEXPR "alpha-bound" 0), and each call returns its variable again.
 */
Node mkRewriterVar(NodeManager* nm, const char* role, Node n, TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, tn);
}

/**
 * The same, named name.
 *
 * The same variable as the overload above, which also gets the printed name
 * name. For instance, rowVariable calls it with the role "row", n the empty
 * bag (as bag.empty (Bag (Tuple Int Int))), the name "row_N", N the node id
 * of that empty bag, and tn the sort (Tuple Int Int), for the variable row_N
 * of that sort. The name is not part of the cache: a call with the same
 * role, n and tn but another name returns the same variable, renamed. The
 * callers derive the name from n, so this does not happen.
 */
Node mkRewriterVar(NodeManager* nm,
                   const char* role,
                   Node n,
                   const std::string& name,
                   TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, name, tn);
}
}  // namespace

BagsRewriteResponse::BagsRewriteResponse()
    : d_node(Node::null()), d_rewrite(Rewrite::NONE)
{
}

BagsRewriteResponse::BagsRewriteResponse(Node n, Rewrite rewrite)
    : d_node(n), d_rewrite(rewrite)
{
}

// Makes the rewriter. r is the solver's rewriter, which some rules call on the
// terms they build; statistics, when not null, counts the Rewrite id of every
// step. higherOrder says whether the logic has higher-order terms. When it is
// false, the rules that put a lambda into a term that had none do not apply,
// since the theory of uninterpreted functions rejects lambdas in such a logic:
// FILTER_MAP, MAP_MAP and PROJECT_TO_MAP each return their input unchanged
// unless d_higherOrder holds. For X : (Bag (Tuple Int Int)), with higherOrder
// true,
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t)) X)
// by PROJECT_TO_MAP, and with higherOrder false the projection stays as it is.
// d_zero and d_one, the integer constants 0 and 1, are made once here, since
// many rules build them.
BagsRewriter::BagsRewriter(NodeManager* nm,
                           Rewriter* r,
                           HistogramStat<Rewrite>* statistics,
                           bool higherOrder)
    : TheoryRewriter(nm),
      d_rewriter(r),
      d_statistics(statistics),
      d_higherOrder(higherOrder)
{
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

// The rewrite of a node n after its children are rewritten. The cases, in
// order: a constant is a normal form and stays as it is; an equality goes to
// postRewriteEqual and a bag.choose to rewriteChoose; any other node whose
// children are all constants is evaluated (CONSTANT_EVALUATION); every other
// node goes to the function of its kind, which returns n with Rewrite::NONE
// when no rule applies. Since evaluation comes first, only the projection of
// a table that is not a constant goes to postRewriteProject. For
// X : (Bag (Tuple Int Int)),
//   ((_ table.project 1 0) (bag (tuple 1 2) 3))
//   ---> (bag (tuple 2 1) 3)                          (CONSTANT_EVALUATION)
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t)) X)
// the latter by PROJECT_TO_MAP, with the higher-order flag (see the
// constructor). A result other than n is rewritten again, children included
// (REWRITE_AGAIN_FULL), so each rule may leave the rest to the other rules.
RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  BagsRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = BagsRewriteResponse(n, Rewrite::NONE);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    response = postRewriteEqual(n);
  }
  else if (n.getKind() == Kind::BAG_CHOOSE)
  {
    response = rewriteChoose(n);
  }
  else if (BagsUtils::areChildrenConstants(n))
  {
    Node value = BagsUtils::evaluate(d_rewriter, n);
    response = BagsRewriteResponse(value, Rewrite::CONSTANT_EVALUATION);
  }
  else
  {
    Kind k = n.getKind();
    switch (k)
    {
      case Kind::BAG_MAKE: response = rewriteMakeBag(n); break;
      case Kind::BAG_COUNT: response = rewriteBagCount(n); break;
      case Kind::BAG_SETOF: response = rewriteSetof(n); break;
      case Kind::BAG_UNION_MAX: response = rewriteUnionMax(n); break;
      case Kind::BAG_UNION_DISJOINT: response = rewriteUnionDisjoint(n); break;
      case Kind::BAG_INTER_MIN: response = rewriteIntersectionMin(n); break;
      case Kind::BAG_DIFFERENCE_SUBTRACT:
        response = rewriteDifferenceSubtract(n);
        break;
      case Kind::BAG_DIFFERENCE_REMOVE:
        response = rewriteDifferenceRemove(n);
        break;
      case Kind::BAG_CARD: response = rewriteCard(n); break;
      case Kind::BAG_MAP: response = postRewriteMap(n); break;
      case Kind::BAG_FILTER: response = postRewriteFilter(n); break;
      case Kind::BAG_ALL: response = postRewriteAll(n); break;
      case Kind::BAG_SOME: response = postRewriteSome(n); break;
      case Kind::BAG_FOLD: response = postRewriteFold(n); break;
      case Kind::BAG_PARTITION: response = postRewritePartition(n); break;
      case Kind::TABLE_PRODUCT: response = postRewriteProduct(n); break;
      // a projection of a table that is not a constant, see postRewriteProject
      case Kind::TABLE_PROJECT: response = postRewriteProject(n); break;
      case Kind::TABLE_AGGREGATE: response = postRewriteAggregate(n); break;
      case Kind::TABLE_GROUP: response = postRewriteGroup(n); break;
      default: response = BagsRewriteResponse(n, Rewrite::NONE); break;
    }
  }

  Trace("bags-rewrite") << "postRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

// The rewrite of a node n before its children are rewritten, for three kinds:
// an equality of a term with itself is true (IDENTICAL_NODES, see
// preRewriteEqual), and bag.subbag and bag.member become terms of the other
// bag operators (SUB_BAG, MEMBER). Every other node is left to postRewrite.
// For A : (Bag Int), B : (Bag Int) and x : Int,
//   (bag.subbag A B)
//   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag Int)))
//   (bag.member x A)
//   ---> (>= (bag.count x A) 1)
// As in postRewrite, a result other than n is rewritten again.
RewriteResponse BagsRewriter::preRewrite(TNode n)
{
  BagsRewriteResponse response;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::EQUAL: response = preRewriteEqual(n); break;
    case Kind::BAG_SUBBAG: response = rewriteSubBag(n); break;
    case Kind::BAG_MEMBER: response = rewriteMember(n); break;
    default: response = BagsRewriteResponse(n, Rewrite::NONE);
  }

  Trace("bags-rewrite") << "preRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

BagsRewriteResponse BagsRewriter::preRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a bag
    return BagsRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSubBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SUBBAG);

  // (bag.subbag A B) = ((bag.difference_subtract A B) == bag.empty)
  Node emptybag = d_nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = d_nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return BagsRewriteResponse(equal, Rewrite::SUB_BAG);
}

BagsRewriteResponse BagsRewriter::rewriteMember(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MEMBER);

  // - (bag.member x A) = (>= (bag.count x A) 1)
  Node count = d_nm->mkNode(Kind::BAG_COUNT, n[0], n[1]);
  Node geq = d_nm->mkNode(Kind::GEQ, count, d_one);
  return BagsRewriteResponse(geq, Rewrite::MEMBER);
}

BagsRewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  // return bag.empty for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (bag x c) = bag.empty where c <= 0
    Node emptybag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptybag, Rewrite::BAG_MAKE_COUNT_NEGATIVE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_COUNT);
  if (n[0].getKind() == Kind::APPLY_CONSTRUCTOR && n[0].getType().isTuple()
      && n[1].getType().getBagElementType().isTuple())
  {
    // COUNT_NULL_IN_NOT_NULL: a probe with a null in a column k that is never
    // null in X occurs in X 0 times; with column 1 of X never null,
    //   (bag.count (tuple a (as nullable.null (Nullable Int))) X) ---> 0
    std::set<uint32_t> nn;
    bool computed = false;
    for (size_t k = 0; k < n[0].getNumChildren(); k++)
    {
      if (!isNullConstant(n[0][k]))
      {
        continue;
      }
      if (!computed)
      {
        nn = nonNullColumns(n[1]);
        computed = true;
      }
      if (nn.count(k))
      {
        return BagsRewriteResponse(d_zero, Rewrite::COUNT_NULL_IN_NOT_NULL);
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_MAP)
  {
    // COUNT_MAP_DUPLICATE_COLUMNS: every row the map makes has its columns i <
    // j equal, the same term, so a probe occurs only when its columns i and j
    // are equal too, and column j leaves the probe and the map
    // (see rewrites.h). A probe e that is not a tuple term has the columns
    // ((_ tuple.select k) e).
    Node g = asLambda(n[1][0]);
    if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
        && g[1].getKind() == Kind::APPLY_CONSTRUCTOR && g[1].getType().isTuple()
        && g[1].getNumChildren() > 1)
    {
      Node body = g[1];
      size_t m = body.getNumChildren();
      for (size_t j = 1; j < m; j++)
      {
        for (size_t i = 0; i < j; i++)
        {
          if (body[i] != body[j])
          {
            continue;
          }
          std::vector<Node> cols, probe;
          std::vector<TypeNode> types;
          for (size_t k = 0; k < m; k++)
          {
            if (k != j)
            {
              cols.push_back(body[k]);
              types.push_back(body[k].getType());
              probe.push_back(
                  datatypes::TupleUtils::nthElementOfTuple(n[0], k));
            }
          }
          TypeNode t = d_nm->mkTupleType(types);
          // g2 and e2, the map and the probe without column j
          Node g2 = mkLambda(g[0][0],
                             datatypes::TupleUtils::constructTupleFromElements(
                                 t, cols, 0, cols.size() - 1));
          Node e2 = datatypes::TupleUtils::constructTupleFromElements(
              t, probe, 0, probe.size() - 1);
          // the count of e2 in the map by g2
          Node count = d_nm->mkNode(
              Kind::BAG_COUNT, e2, d_nm->mkNode(Kind::BAG_MAP, g2, n[1][1]));
          // (= a c)
          Node same = datatypes::TupleUtils::nthElementOfTuple(n[0], i).eqNode(
              datatypes::TupleUtils::nthElementOfTuple(n[0], j));
          Node ret = d_nm->mkNode(Kind::ITE, same, count, d_zero);
          return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_DUPLICATE_COLUMNS);
        }
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_MAP)
  {
    // COUNT_MAP_CONST_COLUMN: column j of every row the map makes is a constant
    // c, so a probe occurs only when its column j is c, and the column leaves
    // the probe and the map (see rewrites.h)
    Node g = asLambda(n[1][0]);
    if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
        && g[1].getKind() == Kind::APPLY_CONSTRUCTOR && g[1].getType().isTuple()
        && g[1].getNumChildren() > 1)
    {
      Node body = g[1];
      size_t m = body.getNumChildren();
      for (size_t j = 0; j < m; j++)
      {
        if (!body[j].isConst())
        {
          continue;
        }
        std::vector<Node> cols, probe;
        std::vector<TypeNode> types;
        for (size_t k = 0; k < m; k++)
        {
          if (k != j)
          {
            cols.push_back(body[k]);
            types.push_back(body[k].getType());
            probe.push_back(datatypes::TupleUtils::nthElementOfTuple(n[0], k));
          }
        }
        TypeNode t = d_nm->mkTupleType(types);
        // g2 and e2, the map and the probe without column j
        Node g2 = mkLambda(g[0][0],
                           datatypes::TupleUtils::constructTupleFromElements(
                               t, cols, 0, cols.size() - 1));
        Node e2 = datatypes::TupleUtils::constructTupleFromElements(
            t, probe, 0, probe.size() - 1);
        Node count = d_nm->mkNode(
            Kind::BAG_COUNT, e2, d_nm->mkNode(Kind::BAG_MAP, g2, n[1][1]));
        // (= b 5)
        Node same =
            datatypes::TupleUtils::nthElementOfTuple(n[0], j).eqNode(body[j]);
        Node ret = d_nm->mkNode(Kind::ITE, same, count, d_zero);
        return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_CONST_COLUMN);
      }
    }
  }
  // a table constant whose rows have the sort of the probe
  bool rowProbe = false;
  if (n[1].getKind() == Kind::VARIABLE)
  {
    TypeNode rowType = n[1].getType().getBagElementType();
    TypeNode probeType = n[0].getType();
    rowProbe = rowType.isTuple() && rowType == probeType;
  }
  if ((n[1].getKind() == Kind::BAG_MAP || rowProbe) && isTupleTerm(n[0])
      && n[0].getNumChildren() > 1)
  {
    // COUNT_MAP_CONST_PROBE: column k of the probe is a constant c and the map
    // copies column j of its row there, so only the rows of X whose column j is
    // c can give the probe: column k leaves the probe and the map, which goes
    // over those rows (see rewrites.h). A table constant X that the input
    // declares (Kind::VARIABLE) counts as its own identity map, but a skolem
    // that the solver introduced by purification does not: rewriting the counts
    // in those makes the solver introduce more of them.
    Node mapped = n[1];
    if (mapped.getKind() != Kind::BAG_MAP && !d_higherOrder)
    {
      // the identity map is a lambda
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    if (mapped.getKind() != Kind::BAG_MAP)
    {
      // the identity map of X above, over the row variable of T
      TypeNode et = mapped.getType().getBagElementType();
      Node v = rowVariable(et);
      std::vector<Node> cols;
      for (size_t k = 0; k < et.getTupleLength(); k++)
      {
        cols.push_back(datatypes::TupleUtils::nthElementOfTuple(v, k));
      }
      mapped = d_nm->mkNode(
          Kind::BAG_MAP,
          d_nm->mkNode(Kind::LAMBDA,
                       {d_nm->mkNode(Kind::BOUND_VAR_LIST, v),
                        datatypes::TupleUtils::constructTupleFromElements(
                            et, cols, 0, cols.size() - 1)}),
          mapped);
    }
    Node n1 = mapped;
    Node g = asLambda(n1[0]);
    if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
        && g[1].getKind() == Kind::APPLY_CONSTRUCTOR
        && g[1].getNumChildren() == n[0].getNumChildren())
    {
      Node sv = g[0][0];
      for (size_t k = 0; k < n[0].getNumChildren(); k++)
      {
        Node c = n[0][k];
        Node col = g[1][k];
        if (!c.isConst() || col.getKind() != Kind::APPLY_SELECTOR
            || col[0] != sv)
        {
          continue;
        }
        std::vector<Node> cols, probe;
        std::vector<TypeNode> types;
        for (size_t i = 0; i < n[0].getNumChildren(); i++)
        {
          if (i != k)
          {
            cols.push_back(g[1][i]);
            probe.push_back(n[0][i]);
            types.push_back(g[1][i].getType());
          }
        }
        TypeNode t = d_nm->mkTupleType(types);
        // g2 and e2, the map and the probe without column k
        Node g2 = mkLambda(sv,
                           datatypes::TupleUtils::constructTupleFromElements(
                               t, cols, 0, cols.size() - 1));
        Node e2 = datatypes::TupleUtils::constructTupleFromElements(
            t, probe, 0, probe.size() - 1);
        // the rows of X whose column j is c
        Node fixed =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(sv, col.eqNode(c)), n1[1]);
        Node ret = d_nm->mkNode(
            Kind::BAG_COUNT, e2, d_nm->mkNode(Kind::BAG_MAP, g2, fixed));
        return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_CONST_PROBE);
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_MAP && n[1][1].getKind() == Kind::BAG_FILTER)
  {
    // COUNT_MAP_FILTER_KEYS: g projects the rows of X onto columns J, and a
    // conjunct of the filter reads only those columns, or none: every row that
    // g maps to the probe agrees with the probe on them, so the conjunct holds
    // of all those rows or of none, and is decided on the probe instead, with
    // ((_ tuple.select J[k]) t) read as column k of the probe (see rewrites.h)
    // COUNT_MAP_FILTER_CORRELATED: a conjunct that equates a column of the row
    // with a term E that is not a constant and does not read the row, a column
    // of an enclosing row in a correlated subquery, goes, and the column joins
    // the map and E the probe (see rewrites.h). That leaves the filter free of
    // the enclosing row, so that the counts for two enclosing rows are counts
    // in one bag.
    Node g = asLambda(n[1][0]);
    Node p = asLambda(n[1][1][0]);
    Node X = n[1][1][1];
    std::vector<uint32_t> J = projectionIndices(g);
    if (!J.empty() && p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1)
    {
      Node sv = p[0][0];
      std::vector<Node> conjuncts;
      if (p[1].getKind() == Kind::AND)
      {
        conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
      }
      else
      {
        conjuncts.push_back(p[1]);
      }
      // from[k] is ((_ tuple.select J[k]) t), to[k] column k of the probe
      std::vector<Node> from, to;
      std::set<uint32_t> columns;
      for (size_t k = 0; k < J.size(); k++)
      {
        if (columns.insert(J[k]).second)
        {
          from.push_back(datatypes::TupleUtils::nthElementOfTuple(sv, J[k]));
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(n[0], k));
        }
      }
      std::vector<Node> moved, rest;
      std::vector<Node> extraS, extraE;
      for (const Node& c : conjuncts)
      {
        std::set<uint32_t> positions;
        bool onColumns =
            readPositions(c, sv, positions) && !bindsVariable(c, sv);
        for (uint32_t pos : positions)
        {
          onColumns = onColumns && columns.count(pos) > 0;
        }
        // a conjunct that reads no row of X, or only the projected columns
        Node m = onColumns ? c.substitute(
                                 from.begin(), from.end(), to.begin(), to.end())
                           : Node::null();
        if (!m.isNull() && !occursFree(m, sv))
        {
          moved.push_back(m);
          continue;
        }
        // an equation (= ((_ tuple.select k) t) E) between another column
        // and an expression E of an enclosing row: one more column to project
        // and to probe; a constant E stays in the filter, since
        // COUNT_MAP_CONST_PROBE would move it back
        bool extended = false;
        if (c.getKind() == Kind::EQUAL)
        {
          for (size_t sd = 0; sd < 2 && !extended; sd++)
          {
            if (c[sd].getKind() == Kind::APPLY_SELECTOR && c[sd][0] == sv
                && !c[1 - sd].isConst() && !occursFree(c[1 - sd], sv))
            {
              extraS.push_back(c[sd]);
              extraE.push_back(c[1 - sd]);
              extended = true;
            }
          }
        }
        if (!extended)
        {
          rest.push_back(c);
        }
      }
      if (!extraS.empty())
      {
        // COUNT_MAP_FILTER_CORRELATED, see above: cols are the columns of the
        // map followed by the columns ((_ tuple.select k) t) of the extra
        // equations, probe the columns of the probe followed by their E's
        Node g0 = asLambda(n[1][0]);
        std::vector<Node> cols, probe;
        std::vector<TypeNode> types;
        Node gBody = g0[1].substitute(TNode(g0[0][0]), TNode(sv));
        for (size_t k = 0, w = gBody.getNumChildren(); k < w; k++)
        {
          cols.push_back(gBody[k]);
          types.push_back(gBody[k].getType());
          probe.push_back(datatypes::TupleUtils::nthElementOfTuple(n[0], k));
        }
        for (size_t k = 0; k < extraS.size(); k++)
        {
          cols.push_back(extraS[k]);
          types.push_back(extraS[k].getType());
          probe.push_back(extraE[k]);
        }
        rest.insert(rest.end(), moved.begin(), moved.end());
        moved.clear();
        if (isTupleTerm(gBody) && !bindsVariable(g0[1], g0[0][0]))
        {
          TypeNode t = d_nm->mkTupleType(types);
          // g2 and e2, the map and the probe with the column and E added
          Node g2 = mkLambda(sv,
                             datatypes::TupleUtils::constructTupleFromElements(
                                 t, cols, 0, cols.size() - 1));
          Node e2 = datatypes::TupleUtils::constructTupleFromElements(
              t, probe, 0, probe.size() - 1);
          // the conjuncts that could move were read through the old
          // projection: keep them inside, over the row itself
          std::vector<Node> inner;
          for (const Node& c : conjuncts)
          {
            bool isExtra = false;
            for (size_t k = 0; k < extraS.size(); k++)
            {
              isExtra = isExtra
                        || (c.getKind() == Kind::EQUAL
                            && ((c[0] == extraS[k] && c[1] == extraE[k])
                                || (c[1] == extraS[k] && c[0] == extraE[k])));
            }
            if (!isExtra)
            {
              inner.push_back(c);
            }
          }
          Node innerBody =
              inner.empty()
                  ? d_nm->mkConst(true)
                  : (inner.size() == 1 ? inner[0]
                                       : d_nm->mkNode(Kind::AND, inner));
          // X filtered by the other conjuncts
          Node filteredX =
              d_nm->mkNode(Kind::BAG_FILTER, mkLambda(sv, innerBody), X);
          Node ret = d_nm->mkNode(
              Kind::BAG_COUNT, e2, d_nm->mkNode(Kind::BAG_MAP, g2, filteredX));
          return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_FILTER_CORRELATED);
        }
      }
      if (!moved.empty())
      {
        // COUNT_MAP_FILTER_KEYS, see above: the filter keeps the conjuncts
        // that stay, (< ((_ tuple.select 1) t) 7), and the moved ones,
        // (> a 3), guard the count
        Node restBody =
            rest.empty()
                ? d_nm->mkConst(true)
                : (rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::AND, rest));
        Node filtered =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(sv, restBody), X);
        Node count =
            d_nm->mkNode(Kind::BAG_COUNT,
                         n[0],
                         d_nm->mkNode(Kind::BAG_MAP, n[1][0], filtered));
        Node cond =
            moved.size() == 1 ? moved[0] : d_nm->mkNode(Kind::AND, moved);
        Node ret = d_nm->mkNode(Kind::ITE, cond, count, d_zero);
        return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_FILTER_KEYS);
      }
    }
  }
  if (n[1].isConst() && n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.count x bag.empty) = 0
    return BagsRewriteResponse(d_zero, Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == Kind::BAG_MAKE && n[0] == n[1][0] && n[1][1].isConst()
      && n[1][1].getConst<Rational>() > Rational(0))
  {
    // (bag.count x (bag x c)) = c, c > 0 is a constant
    Node c = n[1][1];
    return BagsRewriteResponse(c, Rewrite::COUNT_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.setof X), the elements of X each once, tried in this
// order:
// - none for the bag.setof of a key assertion, which stays as it is (see
//   BagsKeyTermAttribute);
// - SETOF_BAG_MAKE, for X = (bag x c): (bag x 1) when c is a positive
//   constant, and (bag x (ite (>= c 1) 1 0)) when c is not a constant. A
//   constant c <= 0 does not reach here, since rewriteMakeBag has already
//   made such a (bag x c) empty;
// - SETOF_PROJECTION_SORT, for X a map (rewriteSetofOfMap).
// For x : Int and c : Int,
//   (bag.setof (bag x c))
//   ---> (bag x (ite (>= c 1) 1 0))                           (SETOF_BAG_MAKE)
BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // The bag.setof of a key assertion, which states that columns of a table
    // are a key of it, as
    //   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
    // recordKey read the key off it and marked it. Rewriting it by the key
    // would make the assertion true and lose the fact, so it stays as it is.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT && n[0][0] == n[0][1])
  {
    // (bag.setof (bag.union_disjoint A A)) = (bag.setof A)
    return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_SETOF, n[0][0]),
                               Rewrite::SETOF_UNION_SAME);
  }
  if (n[0].getKind() == Kind::BAG_MAP)
  {
    // AGGREGATE_GROUP_KEYS: the set of the group columns of the groups that a
    // row reached is the set of those columns of the rows of X, see
    // keysOfReachedGroups and rewrites.h
    Node m = keysOfReachedGroups(asLambda(n[0][0]), n[0][1], false);
    if (!m.isNull())
    {
      return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_SETOF, m),
                                 Rewrite::AGGREGATE_GROUP_KEYS);
    }
  }
  if (n[0].getKind() == Kind::BAG_SETOF)
  {
    // (bag.setof (bag.setof A)) = (bag.setof A)
    return BagsRewriteResponse(n[0], Rewrite::SETOF_SETOF);
  }
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // (bag.setof (bag x n)) = (bag x 1)
    //  where n is a positive constant
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], d_one);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  if (n[0].getKind() == Kind::BAG_MAKE && !n[0][1].isConst())
  {
    // SETOF_BAG_MAKE for a count c that is not a constant: x is in the set
    // once when c is positive, and (bag x c) is empty otherwise, as is
    // (bag x 0), so
    //   (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
    Node count = d_nm->mkNode(
        Kind::ITE, d_nm->mkNode(Kind::GEQ, n[0][1], d_one), d_one, d_zero);
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], count);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  {
    // SETOF_ABSORB: under duplicate removal only membership counts, and a
    // union, a map or a filter has an element in its result exactly when it
    // has one with its argument's bag.setof instead: an inner bag.setof
    // reached through those changes nothing,
    //   (bag.setof (bag.map f (bag.union_disjoint (bag.setof X) Y)))
    //   --->
    //   (bag.setof (bag.map f (bag.union_disjoint X Y)))
    std::function<Node(const Node&)> absorb = [&](const Node& t) -> Node {
      switch (t.getKind())
      {
        case Kind::BAG_SETOF: return absorb(t[0]);
        case Kind::BAG_UNION_DISJOINT:
        case Kind::BAG_UNION_MAX:
        {
          Node a = absorb(t[0]);
          Node b = absorb(t[1]);
          return a == t[0] && b == t[1] ? t : d_nm->mkNode(t.getKind(), a, b);
        }
        case Kind::BAG_MAP:
        case Kind::BAG_FILTER:
        {
          Node a = absorb(t[1]);
          return a == t[1] ? t : d_nm->mkNode(t.getKind(), t[0], a);
        }
        default: return t;
      }
    };
    Node inner = absorb(n[0]);
    if (inner != n[0])
    {
      Node ret = d_nm->mkNode(Kind::BAG_SETOF, inner);
      return BagsRewriteResponse(ret, Rewrite::SETOF_ABSORB);
    }
  }
  if (n[0].getKind() == Kind::BAG_MAP && n[0][1].getKind() == Kind::BAG_FILTER)
  {
    // SEMI_TO_INTERSECTION: a projected semi-join as an intersection, see
    // semiJoinToIntersection
    Node inter = semiJoinToIntersection(n[0], true);
    if (!inter.isNull())
    {
      return BagsRewriteResponse(inter, Rewrite::SEMI_TO_INTERSECTION);
    }
  }
  if (isSet(n[0]))
  {
    // SETOF_OF_SET: a bag with no element twice is its own set, see isSet;
    // with columns 0 and 2 a key of X,
    //   (bag.setof (bag.filter p X)) ---> (bag.filter p X)
    return BagsRewriteResponse(n[0], Rewrite::SETOF_OF_SET);
  }
  {
    // SETOF_PUSHDOWN, see rewriteSetofPushdown
    BagsRewriteResponse r = rewriteSetofPushdown(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[0].getKind() == Kind::BAG_MAP)
  {
    // SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, see rewriteSetofOfMap
    return rewriteSetofOfMap(n);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  if (n[1].getKind() == Kind::BAG_EMPTY || n[0] == n[1])
  {
    // (bag.union_max A A) = A
    // (bag.union_max A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_max bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == Kind::BAG_UNION_MAX
       || n[1].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
    // (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
    // (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
    // (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       || n[0].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (bag.union_max (bag.union_max A B) A)) = (bag.union_max A B)
    // (bag.union_max (bag.union_max B A) A)) = (bag.union_max B A)
    // (bag.union_max (bag.union_disjoint A B) A)) = (bag.union_disjoint A B)
    // (bag.union_max (bag.union_disjoint B A) A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  {
    // UNION_COMPLEMENTARY_FILTERS: two filters of X that differ in one
    // conjunct, p in one and (not p) in the other, keep together the rows of X
    // that the other conjuncts keep, since a row of X passes one of the two or
    // neither, never both (see rewrites.h). Also under one map of both, and for
    // two parts of a longer union, the other parts unioned to the result. The
    // variables of the two filters may differ; the second is renamed to the
    // first.
    std::vector<Node> parts;
    std::vector<Node> todo{n};
    while (!todo.empty())
    {
      Node c = todo.back();
      todo.pop_back();
      if (c.getKind() == Kind::BAG_UNION_DISJOINT)
      {
        todo.push_back(c[1]);
        todo.push_back(c[0]);
      }
      else
      {
        parts.push_back(c);
      }
    }
    // a part, a filter of X by the conjuncts cs over the variable x, or a map
    // by g of one, seen as g, X, x and cs; g is null for a part without a map
    auto view =
        [&](const Node& u, Node& g, Node& X, Node& x, std::vector<Node>& cs) {
          Node F = u;
          g = Node::null();
          if (F.getKind() == Kind::BAG_MAP)
          {
            g = F[0];
            F = F[1];
          }
          if (F.getKind() != Kind::BAG_FILTER)
          {
            return false;
          }
          Node P = asLambda(F[0]);
          if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)
          {
            return false;
          }
          X = F[1];
          x = P[0][0];
          cs.clear();
          if (P[1].getKind() == Kind::AND)
          {
            cs.insert(cs.end(), P[1].begin(), P[1].end());
          }
          else
          {
            cs.push_back(P[1]);
          }
          return true;
        };
    for (size_t i = 0; i < parts.size(); i++)
    {
      for (size_t j = i + 1; j < parts.size(); j++)
      {
        Node gi, Xi, xi, gj, Xj, xj;
        std::vector<Node> ci, cj;
        if (!view(parts[i], gi, Xi, xi, ci) || !view(parts[j], gj, Xj, xj, cj)
            || Xi != Xj || gi != gj || ci.size() != cj.size())
        {
          continue;
        }
        for (Node& c : cj)
        {
          c = c.substitute(TNode(xj), TNode(xi));
        }
        std::multiset<Node> si(ci.begin(), ci.end()), sj(cj.begin(), cj.end());
        Node shared;
        for (const Node& c : ci)
        {
          Node neg = c.getKind() == Kind::NOT ? c[0] : c.notNode();
          if (!si.count(neg) && sj.count(neg))
          {
            std::multiset<Node> a = si, b = sj;
            a.erase(a.find(c));
            b.erase(b.find(neg));
            if (a == b)
            {
              std::vector<Node> keep(a.begin(), a.end());
              shared = keep.empty()
                           ? d_nm->mkConst(true)
                           : (keep.size() == 1 ? keep[0]
                                               : d_nm->mkNode(Kind::AND, keep));
              break;
            }
          }
        }
        if (shared.isNull())
        {
          continue;
        }
        // the filter of X by the other conjuncts, under the map by g if any
        Node merged = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(xi, shared), Xi);
        if (!gi.isNull())
        {
          merged = d_nm->mkNode(Kind::BAG_MAP, gi, merged);
        }
        Node ret = merged;
        for (size_t k = 0; k < parts.size(); k++)
        {
          if (k != i && k != j)
          {
            ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, ret, parts[k]);
          }
        }
        return BagsRewriteResponse(ret, Rewrite::UNION_COMPLEMENTARY_FILTERS);
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       && n[1].getKind() == Kind::BAG_INTER_MIN)
      || (n[1].getKind() == Kind::BAG_UNION_MAX
          && n[0].getKind() == Kind::BAG_INTER_MIN))

  {
    // (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B)) =
    //         (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    // check if the operands of bag.union_max and bag.inter_min are the
    // same
    std::set<Node> left(n[0].begin(), n[0].end());
    std::set<Node> right(n[1].begin(), n[1].end());
    if (left == right)
    {
      Node rewritten = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, n[0][0], n[0][1]);
      return BagsRewriteResponse(rewritten, Rewrite::UNION_DISJOINT_MAX_MIN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN);
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min A bag.empty) = bag.empty
    return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // (bag.inter_min A A) = A
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.inter_min A (bag.union_disjoint A B)) = A
      // (bag.inter_min A (bag.union_disjoint B A)) = A
      // (bag.inter_min A (bag.union_max A B)) = A
      // (bag.inter_min A (bag.union_max B A)) = A
      return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT
      || n[0].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.inter_min (bag.union_disjoint A B) A) = A
      // (bag.inter_min (bag.union_disjoint B A) A) = A
      // (bag.inter_min (bag.union_max A B) A) = A
      // (bag.inter_min (bag.union_max B A) A) = A
      return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_SHARED_RIGHT);
    }
  }

  if (n[1] < n[0])
  {
    // INTERSECTION_SORT: bag.inter_min is commutative, the arguments are
    // ordered by node id,
    //   (bag.inter_min B A) ---> (bag.inter_min A B) when A < B
    Node ret = d_nm->mkNode(Kind::BAG_INTER_MIN, n[1], n[0]);
    return BagsRewriteResponse(ret, Rewrite::INTERSECTION_SORT);
  }
  if (d_rewriter != nullptr && n.getType().getBagElementType().isTuple())
  {
    // INTERSECTION_SHARE_CONDITIONS: every element of A satisfies the
    // conditions read off its filters (see elementConditions), so an element of
    // B that is also in A does too, and the other way round: each side gets a
    // filter by the conditions of the other that it lacks, which the filter
    // rules merge, so that both sides have the same filters (see rewrites.h).
    // Each new filter is rewritten here, to see whether anything changed.
    Node w = rowVariable(n.getType().getBagElementType());
    std::set<Node> qa, qb;
    elementConditions(n[0], w, qa);
    elementConditions(n[1], w, qb);
    std::vector<Node> toA, toB;
    for (const Node& c : qb)
    {
      if (qa.count(c) == 0)
      {
        toA.push_back(c);
      }
    }
    for (const Node& c : qa)
    {
      if (qb.count(c) == 0)
      {
        toB.push_back(c);
      }
    }
    Node a = n[0];
    Node b = n[1];
    if (!toA.empty())
    {
      Node q = toA.size() == 1 ? toA[0] : d_nm->mkNode(Kind::AND, toA);
      a = d_rewriter->rewrite(
          d_nm->mkNode(Kind::BAG_FILTER, mkLambda(w, q), a));
    }
    if (!toB.empty())
    {
      Node q = toB.size() == 1 ? toB[0] : d_nm->mkNode(Kind::AND, toB);
      b = d_rewriter->rewrite(
          d_nm->mkNode(Kind::BAG_FILTER, mkLambda(w, q), b));
    }
    if (a != n[0] || b != n[1])
    {
      Node ret = d_nm->mkNode(Kind::BAG_INTER_MIN, a, b);
      return BagsRewriteResponse(ret, Rewrite::INTERSECTION_SHARE_CONDITIONS);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceSubtract(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_subtract A bag.empty) = A
    // (bag.difference_subtract bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // (bag.difference_subtract A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (bag.difference_subtract (bag.union_disjoint A B) A) = B
      return BagsRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.union_disjoint B A) A) = B
      return BagsRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_subtract A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_subtract A (bag.union_max A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.inter_min A B) A) = bag.empty
      // (bag.difference_subtract (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);

  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_remove A bag.empty) = A
    // (bag.difference_remove bag.empty B) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // (bag.difference_remove A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_remove A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_remove A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_remove A (bag.union_max A B)) = bag.empty
      // (bag.difference_remove A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_remove (bag.inter_min A B) A) = bag.empty
      // (bag.difference_remove (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CHOOSE);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>() > 0)
  {
    // (bag.choose (bag x c)) = x where c is a constant > 0
    return BagsRewriteResponse(n[0][0], Rewrite::CHOOSE_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CARD);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst())
  {
    // (bag.card (bag x c)) = c where c is a constant > 0
    return BagsRewriteResponse(n[0][1], Rewrite::CARD_BAG_MAKE);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// Records the keys and NOT NULL columns of table constants that a top-level
// assertion states, for the rules that read them (see the header). For
// X : (Bag (Tuple Int (Nullable Int))), the assertion
//   (and (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))
//        (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
//                         (= ((_ tuple.select 1) t)
//                            (as nullable.null (Nullable Int))))
//                       X)
//           (as bag.empty (Bag (Tuple Int (Nullable Int))))))
// records the key {0} of X (see recordKey) and that column 1 of X is never
// null (see recordNotNull). An assertion of any other shape records nothing.
void BagsRewriter::recordFacts(TNode assertion) const
{
  // Walk down the conjunctions of the assertion: a conjunct of a top-level
  // assertion holds whenever the assertion does, so it is a top-level fact
  // too. Only AND is entered, so an equality under a negation or a
  // disjunction, which need not hold, is never read.
  std::vector<TNode> todo{assertion};
  while (!todo.empty())
  {
    TNode a = todo.back();
    todo.pop_back();
    if (a.getKind() == Kind::AND)
    {
      todo.insert(todo.end(), a.begin(), a.end());
    }
    else if (a.getKind() == Kind::EQUAL && a[0].getType().isBag())
    {
      // An equality of bags may be a key assertion or a NOT NULL assertion.
      // Each of the two calls checks for its own shape and does nothing on
      // an equality of another shape.
      recordKey(a);
      recordNotNull(a);
    }
  }
}

// Records the key that n states, when n is a key assertion; does nothing
// otherwise. A key is a set of columns that no two rows of a table agree on.
// For X : (Bag (Tuple Int Int Int)),
//   (= (bag.setof ((_ table.project 2 0) X)) ((_ table.project 2 0) X))
// says that the projection of X onto columns 2 and 0 has no row twice, so no
// two rows of X agree on both columns: {0, 2} is a key of X. X gets the key
// (SEXPR 0 2) added to its BagsKeysAttribute, and the bag.setof of n gets
// BagsKeyTermAttribute, so that the rewriter leaves it as it is.
void BagsRewriter::recordKey(const TNode& n) const
{
  // n is a key assertion when one side is (bag.setof M) and the other side is
  // M itself, either way round, where M is the projection of a table constant
  // X onto columns K. M may be written as the input states a projection,
  // ((_ table.project 0 2) X), or as the map the rewriter turns a projection
  // into, (bag.map (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 0 2) t))
  // X). Then no two rows of X agree on K: K is a key of X. The loop tries
  // the bag.setof on side i = 0 and on side i = 1.
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() != Kind::BAG_SETOF || n[i][0] != n[1 - i])
    {
      continue;
    }
    Node M = n[1 - i];
    std::vector<uint32_t> K;
    Node T;
    // T is the table constant X; the fact is stored on it, so it must be a
    // free constant (isVar), not a term.
    if (M.getKind() == Kind::TABLE_PROJECT && M[0].isVar())
    {
      // M = ((_ table.project 0 2) X): K is the projection's indices.
      K = M.getOperator().getConst<ProjectOp>().getIndices();
      T = M[0];
    }
    else if (M.getKind() == Kind::BAG_MAP && M[1].isVar())
    {
      // M = (bag.map g X), with g a projection lambda, of body
      // ((_ tuple.project 0 2) t) or
      // (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)): K is the
      // columns that g selects (see projectionIndices), empty for another g.
      K = projectionIndices(asLambda(M[0]));
      T = M[1];
    }
    // K is empty when M has neither shape, or projects onto no column:
    // nothing is recorded then.
    if (K.empty())
    {
      continue;
    }
    // A key is a set of columns: sort K and drop repeats, so that
    // ((_ table.project 2 0) X) and ((_ table.project 0 2 0) X) give the same
    // key (SEXPR 0 2).
    std::sort(K.begin(), K.end());
    K.erase(std::unique(K.begin(), K.end()), K.end());
    std::vector<Node> cols;
    for (uint32_t k : K)
    {
      cols.push_back(d_nm->mkConstInt(Rational(k)));
    }
    // The key as a node, (SEXPR 0 2) for K = {0, 2}, to be added below to the
    // keys that X already has, such as (SEXPR (SEXPR 1)).
    Node key = d_nm->mkNode(Kind::SEXPR, cols);
    // Mark the bag.setof of n, so that the rewriter does not rewrite it away
    // with the very fact it states (see BagsKeyTermAttribute). The rewriter
    // rewrites the argument M before the bag.setof above it (PROJECT_TO_MAP,
    // for one, turns a projection into a map), and then meets
    // (bag.setof M'), with M' the rewritten M, a new node: mark that one too.
    // This needs the rewriter, so it is skipped when d_rewriter is null.
    Node keyTerm = n[i];
    keyTerm.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal = d_nm->mkNode(Kind::BAG_SETOF, d_rewriter->rewrite(M));
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
    // X's keys so far, then the new key unless X has it already; the
    // attribute is replaced by the SEXPR of them all.
    std::vector<Node> keys;
    if (T.hasAttribute(BagsKeysAttribute()))
    {
      Node old = T.getAttribute(BagsKeysAttribute());
      keys.insert(keys.end(), old.begin(), old.end());
    }
    if (std::find(keys.begin(), keys.end(), key) == keys.end())
    {
      keys.push_back(key);
      Node table = T;
      table.setAttribute(BagsKeysAttribute(), d_nm->mkNode(Kind::SEXPR, keys));
    }
  }
}

// Records the never-null column that n states, when n is a NOT NULL
// assertion; does nothing otherwise. For X : (Bag (Tuple Int (Nullable Int))),
// with both equalities the other way round from the header's example,
//   (= (as bag.empty (Bag (Tuple Int (Nullable Int))))
//      (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
//                    (= (as nullable.null (Nullable Int))
//                       ((_ tuple.select 1) t)))
//                  X))
// says that no row of X has null in column 1. X gets 1 added to its
// BagsNotNullAttribute, and the bag.filter of n gets BagsKeyTermAttribute,
// so that the rewriter leaves it as it is.
void BagsRewriter::recordNotNull(const TNode& n) const
{
  // n is a NOT NULL assertion when one side is the empty bag and the other is
  // the filter of a table constant X by a predicate that holds of the rows
  // with null in some column k: no row of X has null in column k. Both n and
  // the equality in the predicate may be either way round (see recordNotNull
  // in the header):
  //   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
  //                    (= ((_ tuple.select k) t)
  //                       (as nullable.null (Nullable Int))))
  //                  X)
  //      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
  // The loop tries the empty bag on side i = 0 and on side i = 1.
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() != Kind::BAG_EMPTY
        || n[1 - i].getKind() != Kind::BAG_FILTER)
    {
      continue;
    }
    Node F = n[1 - i];
    Node T = F[1];
    Node p = asLambda(F[0]);
    // F = (bag.filter p X): X must be a free constant (isVar), as the fact is
    // stored on it, and p a lambda of one variable whose body is an equality.
    // asLambda reads p as a lambda also when it is a function array constant.
    if (!T.isVar() || p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1
        || p[1].getKind() != Kind::EQUAL)
    {
      continue;
    }
    Node v = p[0][0];
    Node col;
    // One side of the equality must be the null constant, and the other a
    // selector applied to the lambda's variable, ((_ tuple.select k) t);
    // col is that selector term.
    for (size_t sd = 0; sd < 2; sd++)
    {
      if (isNullConstant(p[1][sd])
          && p[1][1 - sd].getKind() == Kind::APPLY_SELECTOR
          && p[1][1 - sd][0] == v)
      {
        col = p[1][1 - sd];
      }
    }
    if (col.isNull())
    {
      continue;
    }
    // Mark the filter of n, so that the rewriter does not rewrite it away
    // with the very fact it states (see BagsKeyTermAttribute). The rewriter
    // rewrites the predicate p before the filter above it, and then meets
    // (bag.filter p' X), with p' the rewritten p, a new node when p changes:
    // mark that one too. This needs the rewriter, so it is skipped when
    // d_rewriter is null.
    F.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal =
          d_nm->mkNode(Kind::BAG_FILTER, d_rewriter->rewrite(F[0]), T);
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
    // k, the index of the column that col selects, as an integer constant.
    // It is added to the never-null columns (SEXPR ..) that X already has,
    // unless it is among them; the attribute is replaced by the new SEXPR.
    Node k = d_nm->mkConstInt(
        Rational(datatypes::utils::indexOf(col.getOperator())));
    std::vector<Node> cols;
    if (T.hasAttribute(BagsNotNullAttribute()))
    {
      Node old = T.getAttribute(BagsNotNullAttribute());
      cols.insert(cols.end(), old.begin(), old.end());
    }
    if (std::find(cols.begin(), cols.end(), k) == cols.end())
    {
      cols.push_back(k);
      Node table = T;
      table.setAttribute(BagsNotNullAttribute(),
                         d_nm->mkNode(Kind::SEXPR, cols));
      // The results that nonNullColumns cached were computed without this
      // column and could miss it: drop them all.
      d_nonNull.clear();
    }
  }
}

// Whether the term t is never null, in every row x and accumulator acc whose
// columns nx of x and nacc of acc are never null. x and acc are variables of
// the lambda that t is the body of, or a part of the body of; either may be
// null when there is none, and then none of its columns counts. The test is
// by the shape of t and is conservative: false means only that no reason was
// found.
// For x : (Tuple Int (Nullable Int)) and nx = {1},
//   (ite (> ((_ tuple.select 0) x) 3)
//        ((_ tuple.select 1) x)
//        (nullable.some 0))
// is never null; so is any term of a sort that is not nullable, such as
// ((_ tuple.select 0) x) : Int; but a free constant y : (Nullable Int) is not.
bool BagsRewriter::nonNullTerm(const Node& t,
                               const Node& x,
                               const std::set<uint32_t>& nx,
                               const Node& acc,
                               const std::set<uint32_t>& nacc) const
{
  // Only a term of a nullable sort can be null: any other term is never null.
  if (!t.getType().isNullable())
  {
    return true;
  }
  if (t.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // t has a nullable sort, so it is built by one of the two constructors:
    // (nullable.some a), of one argument, is never null, and
    // (as nullable.null (Nullable Int)), of none, is null.
    return t.getNumChildren() == 1;
  }
  if (t.getKind() == Kind::APPLY_SELECTOR && t[0].getType().isTuple())
  {
    // ((_ tuple.select k) x) or ((_ tuple.select k) acc): column k of the row
    // or of the accumulator, never null when k is among the never-null
    // columns given for it. A column of any other tuple, e.g. of a row bound
    // by an inner lambda, is not known.
    uint32_t k = datatypes::utils::indexOf(t.getOperator());
    return (!x.isNull() && t[0] == x && nx.count(k) > 0)
           || (!acc.isNull() && t[0] == acc && nacc.count(k) > 0);
  }
  if (t.getKind() == Kind::BAG_FOLD)
  {
    // (bag.fold l i X) of a nullable sort is never null when its initial value
    // i is (nullable.some a), and each value that the step l can return is
    // either the accumulator itself or a (nullable.some b): by induction on
    // the rows folded, the accumulator is never null. For instance
    //   (bag.fold (lambda ((t (Tuple Int Int)) (acc (Nullable Int)))
    //               (ite p (nullable.some ((_ tuple.select 0) t)) acc))
    //             (nullable.some 0)
    //             X)
    // is never null. Here i is t[1], and l is read as a lambda also when it
    // is a function array constant.
    Node l = asLambda(t[0]);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2
        && t[1].getKind() == Kind::APPLY_CONSTRUCTOR
        && t[1].getNumChildren() == 1)
    {
      // keeps(e): whether the step's body e, of the accumulator's nullable
      // sort, returns the accumulator variable l[0][1] or a constructor of
      // one argument, (nullable.some b), in each branch of its ites. Any
      // other term, even one that nonNullTerm would accept, is rejected.
      std::function<bool(const Node&)> keeps = [&](const Node& e) {
        if (e == l[0][1])
        {
          return true;
        }
        if (e.getKind() == Kind::APPLY_CONSTRUCTOR)
        {
          return e.getNumChildren() == 1;
        }
        if (e.getKind() == Kind::ITE)
        {
          return keeps(e[1]) && keeps(e[2]);
        }
        return false;
      };
      return keeps(l[1]);
    }
    // a fold of another shape is not known to be never null
    return false;
  }
  if (t.getKind() == Kind::ITE)
  {
    // (ite (= (as nullable.null (Nullable Int)) a) b c), with the equality
    // either way round and a never null: the condition is false, so the ite
    // is c, and it is never null when c is. Any other ite is never null when
    // both of its branches are.
    const Node& c = t[0];
    if (c.getKind() == Kind::EQUAL)
    {
      for (size_t sd = 0; sd < 2; sd++)
      {
        if (isNullConstant(c[sd]) && nonNullTerm(c[1 - sd], x, nx, acc, nacc))
        {
          return nonNullTerm(t[2], x, nx, acc, nacc);
        }
      }
    }
    return nonNullTerm(t[1], x, nx, acc, nacc)
           && nonNullTerm(t[2], x, nx, acc, nacc);
  }
  // Any other term, e.g. a free constant y : (Nullable Int), or an
  // application of an uninterpreted function, is not known to be never null.
  return false;
}

// The columns of the rows of the aggregate B = ((_ table.aggr K) f i X) that
// are never null. Each row of B is a group of rows of X folded by the step f
// from the initial value i; for an empty X, B is the one row i. A column is
// never null when it is never null in i and f keeps it so. A reached group
// is one that holds a row of X, so that f ran on it at least once; with
// reached true, the caller asks only about the rows of reached groups, and a
// column is then also never null when f's result for it is never null given
// the columns of the accumulator found never null before. For
// X : (Bag (Tuple Int Int)),
//   f = (lambda ((t (Tuple Int Int))
//                (acc (Tuple (Nullable Int) (Nullable Int))))
//         (tuple ((_ tuple.select 0) acc) (nullable.some 1)))
//   i = (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
// give {0}, and {0, 1} with reached: the first step makes column 1
// (nullable.some 1).
std::set<uint32_t> BagsRewriter::aggregateNonNull(const Node& B,
                                                  bool reached) const
{
  std::set<uint32_t> out;
  Node f = asLambda(B[0]);
  Node init = B[1];
  // Only an f of two variables, the row x and the accumulator acc, whose body
  // is a tuple term, and an i that is a tuple term of the same width: column
  // j of a row of B is then child j of f's body or of i. Otherwise no column
  // is known.
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(init)
      || init.getNumChildren() != f[1].getNumChildren())
  {
    return out;
  }
  // the never-null columns of X, which hold of f's row x
  std::set<uint32_t> nx = nonNullColumns(B[2]);
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  // inv starts as the columns of i that are never null. A column j then
  // leaves inv when f's result for it might be null, even with the columns
  // in inv of acc never null, until no column leaves. What is left is the
  // largest set of columns that are never null in i and that every step
  // keeps never null when they are never null before it: by induction on the
  // steps, they are never null in every accumulator, so in every row of B.
  std::set<uint32_t> inv;
  for (size_t j = 0; j < w; j++)
  {
    if (nonNullTerm(init[j], Node::null(), {}, Node::null(), {}))
    {
      inv.insert(j);
    }
  }
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (uint32_t j : std::set<uint32_t>(inv))
    {
      if (!nonNullTerm(f[1][j], x, nx, acc, inv))
      {
        inv.erase(j);
        changed = true;
      }
    }
  }
  out = inv;
  if (reached)
  {
    // The row of a reached group is the result of a step, run on an
    // accumulator whose columns in inv are never null: each column for
    // which f's result is then never null is never null in that row.
    for (size_t j = 0; j < w; j++)
    {
      if (nonNullTerm(f[1][j], x, nx, acc, inv))
      {
        out.insert(j);
      }
    }
  }
  return out;
}

// The columns of the rows of B that are never null, read off B's structure:
// the NOT NULL columns recorded for a table constant (see recordNotNull),
// the columns that each operator keeps never null from its arguments, and
// those that a filter makes never null by testing them. For instance, with
// column 0 of X : (Bag (Tuple (Nullable Int) (Nullable Int))) recorded never
// null,
//   (bag.filter
//     (lambda ((t (Tuple (Nullable Int) (Nullable Int))))
//       (nullable.is_some ((_ tuple.select 1) t)))
//     X)
// has the never-null columns {0, 1}. The result is conservative, a column
// missing from it may still be never null, and is cached in d_nonNull.
std::set<uint32_t> BagsRewriter::nonNullColumns(const Node& B) const
{
  // the cached result, which recordNotNull clears when it records a column
  auto it = d_nonNull.find(B);
  if (it != d_nonNull.end())
  {
    return it->second;
  }
  std::set<uint32_t> out;
  TypeNode et = B.getType().getBagElementType();
  // Only a table, a bag of tuples, has columns; for another bag, such as a
  // (Bag Int), the result is empty.
  if (et.isTuple())
  {
    switch (B.getKind())
    {
      case Kind::BAG_FILTER:
      {
        // B = (bag.filter p Y): the rows of B are rows of Y, so Y's
        // never-null columns stay never null. More are added below from what
        // p requires of the rows it keeps.
        out = nonNullColumns(B[1]);
        Node p = asLambda(B[0]);
        if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1)
        {
          // the conjuncts of the body of p over its row x, each of which
          // holds of every row kept
          Node x = p[0][0];
          std::vector<Node> conjuncts;
          if (p[1].getKind() == Kind::AND)
          {
            conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
          }
          else
          {
            conjuncts.push_back(p[1]);
          }
          for (const Node& c : conjuncts)
          {
            // A conjunct (nullable.is_some ((_ tuple.select k) x)) makes
            // column k never null in the rows kept. isTester gives the index
            // ci of the constructor that c tests, and nullable.is_some is
            // the test of the constructor of one argument.
            Node a;
            int ci = datatypes::utils::isTester(c, a);
            if (ci >= 0 && a.getKind() == Kind::APPLY_SELECTOR && a[0] == x
                && a.getType().isNullable()
                && a.getType().getDType()[ci].getNumArgs() == 1)
            {
              out.insert(datatypes::utils::indexOf(a.getOperator()));
            }
            // So does a conjunct (= ((_ tuple.select k) x) a), either way
            // round, with a never null by its own shape, such as
            // (nullable.some 5); a column of x does not count for a. For a
            // column of a sort that is not nullable, which nonNullTerm finds
            // never null, this adds a column that is never null anyway.
            if (c.getKind() == Kind::EQUAL)
            {
              for (size_t sd = 0; sd < 2; sd++)
              {
                if (c[sd].getKind() == Kind::APPLY_SELECTOR && c[sd][0] == x
                    && nonNullTerm(
                        c[1 - sd], Node::null(), {}, Node::null(), {}))
                {
                  out.insert(datatypes::utils::indexOf(c[sd].getOperator()));
                }
              }
            }
          }
        }
        if (B[1].getKind() == Kind::TABLE_AGGREGATE
            && counterColumn(B[0], asLambda(B[1][0]), B[1][1]) >= 0)
        {
          // B = (bag.filter p ((_ table.aggr K) f i Y)), with p requiring
          // (>= ((_ tuple.select c) r) 1) of a counter column c, which f
          // increments by 1 from 0 (see counterColumn). A row that p keeps
          // has a positive count, so it comes from a group that a row of Y
          // reached, folded at least once by f: aggregateNonNull, with
          // reached true, gives the columns never null in such rows.
          std::set<uint32_t> more = aggregateNonNull(B[1], true);
          out.insert(more.begin(), more.end());
        }
        if (B[1].getKind() == Kind::TABLE_PRODUCT && p.getKind() == Kind::LAMBDA
            && p[0].getNumChildren() == 1)
        {
          // B = (bag.filter p (table.product X (table.product Y Z))), whose
          // components are X, Y and Z. For a component that is an aggregate,
          // p may keep only the rows of B whose part from that component
          // comes from a reached group: when p tests its counter positive,
          // or joins it on all its group columns to such a component (see
          // reachedComponents). Its never-null columns in reached groups
          // are then never null in B, shifted by the column at which the
          // component starts in B's rows.
          //
          // First split the product along its right operands: comps2 gets
          // the components X, Y and Z, and starts2 the column at which each
          // starts. A left operand that is itself a product counts as one
          // component.
          std::vector<Node> comps2;
          std::vector<size_t> starts2;
          Node rest2 = B[1];
          size_t at2 = 0;
          while (true)
          {
            Node c = rest2.getKind() == Kind::TABLE_PRODUCT ? rest2[0] : rest2;
            comps2.push_back(c);
            starts2.push_back(at2);
            at2 += c.getType().getBagElementType().getTupleLength();
            if (rest2.getKind() != Kind::TABLE_PRODUCT)
            {
              break;
            }
            rest2 = rest2[1];
          }
          // reached2[i] is nonzero when p keeps only reached groups of
          // component i; test2, the conjuncts that test the counters, is not
          // used here.
          std::vector<int> test2;
          std::vector<int> reached2 =
              reachedComponents(B[0], comps2, starts2, test2);
          for (size_t i = 0; i < comps2.size(); i++)
          {
            if (reached2[i] && comps2[i].getKind() == Kind::TABLE_AGGREGATE)
            {
              for (uint32_t m : aggregateNonNull(comps2[i], true))
              {
                out.insert(m + starts2[i]);
              }
            }
          }
        }
        break;
      }
      // (bag.setof Y), (bag.difference_subtract Y Z) and
      // (bag.difference_remove Y Z): every row of B is a row of Y, so the
      // never-null columns of Y.
      case Kind::BAG_SETOF:
      case Kind::BAG_DIFFERENCE_SUBTRACT:
      case Kind::BAG_DIFFERENCE_REMOVE: out = nonNullColumns(B[0]); break;
      case Kind::BAG_INTER_MIN:
      {
        // every row of (bag.inter_min Y Z) is a row of both Y and Z, so a
        // column never null in either is never null in B
        out = nonNullColumns(B[0]);
        std::set<uint32_t> more = nonNullColumns(B[1]);
        out.insert(more.begin(), more.end());
        break;
      }
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      {
        // a row of (bag.union_disjoint Y Z) or (bag.union_max Y Z) may come
        // from either side, so only the columns never null on both sides
        std::set<uint32_t> a = nonNullColumns(B[0]);
        std::set<uint32_t> b = nonNullColumns(B[1]);
        for (uint32_t c : a)
        {
          if (b.count(c))
          {
            out.insert(c);
          }
        }
        break;
      }
      case Kind::TABLE_PRODUCT:
      {
        // a row of (table.product Y Z) is a row of Y followed by a row of Z:
        // the never-null columns of Y, and those of Z shifted by the width wl
        // of Y's rows
        out = nonNullColumns(B[0]);
        size_t wl = B[0].getType().getBagElementType().getTupleLength();
        for (uint32_t c : nonNullColumns(B[1]))
        {
          out.insert(c + wl);
        }
        break;
      }
      case Kind::BAG_MAP:
      {
        // A row of (bag.map (lambda ((t ..)) (tuple a0 .. am)) Y) is
        // (tuple a0 .. am) for a row t of Y: column j is never null when aj
        // is, given the never-null columns of Y for t. The body must be
        // built by the tuple constructor for its columns to be read; for
        // another body, such as ((_ tuple.project 1 0) t), none is found.
        Node g = asLambda(B[0]);
        if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
            && g[1].getKind() == Kind::APPLY_CONSTRUCTOR)
        {
          std::set<uint32_t> nx = nonNullColumns(B[1]);
          for (size_t j = 0; j < g[1].getNumChildren(); j++)
          {
            if (nonNullTerm(g[1][j], g[0][0], nx, Node::null(), {}))
            {
              out.insert(j);
            }
          }
        }
        break;
      }
      // ((_ table.aggr K) f i Y), see aggregateNonNull; whether its groups
      // were reached is not known here, so reached is false
      case Kind::TABLE_AGGREGATE: out = aggregateNonNull(B, false); break;
      default:
        // A table constant: the NOT NULL columns recorded for it, as the
        // SEXPR of integer constants that recordNotNull built. Any other
        // node, such as (bag (tuple ..) 1) or a projection, gets none.
        if (B.isVar() && B.hasAttribute(BagsNotNullAttribute()))
        {
          for (const Node& c : B.getAttribute(BagsNotNullAttribute()))
          {
            out.insert(c.getConst<Rational>().getNumerator().toUnsignedInt());
          }
        }
        break;
    }
  }
  d_nonNull[B] = out;
  return out;
}

// body, the body of a lambda over the row x, with the null tests that the
// never-null columns cols of x decide replaced by their values. A test
// (nullable.is_some a) or (nullable.is_null a) of a term a that is never null
// given cols (see nonNullTerm) becomes true or false, and an equality of such
// an a with the null constant becomes false. The rule NOT_NULL_COLUMNS uses
// it, with the never-null columns of the bag that x ranges over. For
// x : (Tuple Int (Nullable Int)) and cols = {1},
//   (and (nullable.is_some ((_ tuple.select 1) x))
//        (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
//        p)
// becomes (and true false p), which the rewriter then simplifies. The result
// is body itself when no test is decided.
Node BagsRewriter::assumeNonNull(const Node& body,
                                 const Node& x,
                                 const std::set<uint32_t>& cols) const
{
  // with no never-null column, no test is decided
  if (cols.empty())
  {
    return body;
  }
  // decided(n): the value of n when n is a null test that cols decide, null
  // otherwise. (= (as nullable.null (Nullable Int)) a), either way round,
  // with a never null, is false. A tester of a nullable a that is never null
  // is true when it tests the constructor of one argument, nullable.is_some,
  // and false for nullable.is_null.
  auto decided = [&](const Node& n) -> Node {
    if (n.getKind() == Kind::EQUAL)
    {
      for (size_t sd = 0; sd < 2; sd++)
      {
        if (isNullConstant(n[sd])
            && nonNullTerm(n[1 - sd], x, cols, Node::null(), {}))
        {
          return d_nm->mkConst(false);
        }
      }
    }
    Node a;
    int ci = datatypes::utils::isTester(n, a);
    if (ci >= 0 && a.getType().isNullable()
        && nonNullTerm(a, x, cols, Node::null(), {}))
    {
      return d_nm->mkConst(a.getType().getDType()[ci].getNumArgs() == 1);
    }
    return Node::null();
  };
  // Rebuild body bottom up, without recursion: cache maps each node done to
  // its replacement. A decided node is replaced by its value, and its
  // children are not visited; a leaf stays as it is; any other node is
  // rebuilt from the replacements of its children, once they are all done.
  // The walk also enters the lambdas nested in body, and does not check
  // whether one of them binds x again.
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{body};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      // already done, e.g. a child shared by two parents
      todo.pop_back();
      continue;
    }
    Node d = decided(n);
    if (!d.isNull())
    {
      cache[n] = d;
      todo.pop_back();
      continue;
    }
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    // push the children not done yet, and come back to n after them
    bool ready = true;
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // n from the replacements of its children, with the operator first for a
    // parameterized kind, such as the selector of ((_ tuple.select 1) x); n
    // itself when no child changed
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      changed = changed || cache[c] != c;
      children.push_back(cache[c]);
    }
    cache[n] = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
  }
  return cache[body];
}

// The keys recorded for a table constant (see recordKey), each as a set of
// column indices; a key is a set of columns that no two rows of the table
// agree on. B is the table constant X or a filter of it, possibly nested,
// as (bag.filter p (bag.filter q X)): a filter keeps some of the rows of X,
// so the keys of X still hold. For X with the attribute
// (SEXPR (SEXPR 0 2) (SEXPR 1)), the result is {{0, 2}, {1}}. It is empty
// for any other B, and for a table constant with no key recorded.
std::vector<std::set<uint32_t>> BagsRewriter::keysOf(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  // strip the filters above the table
  Node T = B;
  while (T.getKind() == Kind::BAG_FILTER)
  {
    T = T[1];
  }
  if (!T.isVar() || !T.hasAttribute(BagsKeysAttribute()))
  {
    return keys;
  }
  // each key (SEXPR 0 2), of integer constants, as the set {0, 2}
  for (const Node& key : T.getAttribute(BagsKeysAttribute()))
  {
    std::set<uint32_t> cols;
    for (const Node& c : key)
    {
      cols.insert(c.getConst<Rational>().getNumerator().toUnsignedInt());
    }
    keys.push_back(cols);
  }
  return keys;
}

// The keys of B, read off its structure. A key is a set of columns that no
// two rows of B agree on, a row that occurs twice counting as two rows, so
// every key found means that B has no row twice; the empty key means that B
// has at most one row. The keys found are a table constant's recorded keys
// (see keysOf), kept by filters, intersections and differences and by maps
// that copy their columns, and combined by products; all the columns of a
// bag.setof; and the columns of an aggregate's rows that copy its group
// columns. Keys may be missed, and the same key may occur twice. With X and
// Y of two columns, each with the key {0}:
//   (table.product X Y) has the key {0, 2}, Y's column 0 being column 2
//     of the product;
//   (bag.map (lambda ((t (Tuple Int Int)))
//              (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
//            X) has the key {1};
//   ((_ table.aggr 0) f i X) has the key {k} when column k of f's result
//     is ((_ tuple.select 0) t), the group column.
std::vector<std::set<uint32_t>> BagsRewriter::rowKeys(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  TypeNode et = B.getType().getBagElementType();
  // only a table, a bag of tuples, has columns
  if (!et.isTuple())
  {
    return keys;
  }
  size_t width = et.getTupleLength();
  switch (B.getKind())
  {
    case Kind::BAG_FILTER:
    {
      // B = (bag.filter P Y) keeps some of the rows of Y, so the keys of Y
      // hold, and P can make them smaller. A key column that P fixes to a
      // constant has the same value in all the rows kept, so it is dropped
      // from the key; a key column that P sets equal to another column is
      // replaced by that column. For X : (Bag (Tuple Int Int Int)) with the
      // key {0, 1},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 1) t) 5))
      //               X)
      // has the key {0}; and with the key {1, 2},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
      //               X)
      // has the key {0, 1}, column 2 being equal to column 0.
      keys = rowKeys(B[1]);
      // the columns fixed by conjuncts (= ((_ tuple.select k) t) c), with c
      // a constant (see fixedColumns)
      std::map<uint32_t, Node> fixed = fixedColumns(B[0]);
      Node P = asLambda(B[0]);
      // rep is a union-find over the columns, joined by the equalities of P
      // between two columns; find(k) is the smallest column known equal to
      // column k, with path compression.
      std::vector<uint32_t> rep(width);
      for (uint32_t k = 0; k < width; k++)
      {
        rep[k] = k;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t k) {
        return rep[k] == k ? k : (rep[k] = find(rep[k]));
      };
      if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
      {
        // the conjuncts of P's body, each of which holds of every row kept;
        // a conjunct (= ((_ tuple.select j) t) ((_ tuple.select k) t)), with
        // t the row, joins the classes of columns j and k
        std::vector<Node> conjuncts;
        if (P[1].getKind() == Kind::AND)
        {
          conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
        }
        else
        {
          conjuncts.push_back(P[1]);
        }
        for (const Node& c : conjuncts)
        {
          if (c.getKind() == Kind::EQUAL
              && c[0].getKind() == Kind::APPLY_SELECTOR
              && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == P[0][0]
              && c[1][0] == P[0][0])
          {
            uint32_t a = find(datatypes::utils::indexOf(c[0].getOperator()));
            uint32_t b = find(datatypes::utils::indexOf(c[1].getOperator()));
            if (a != b && a < width && b < width)
            {
              rep[std::max(a, b)] = std::min(a, b);
            }
          }
        }
      }
      // Each key of Y without its fixed columns, and with each other column
      // replaced by the smallest column equal to it. This is a key of B: two
      // rows kept that agree on it agree on the fixed columns (both have the
      // constant) and on the replaced ones (equal to their replacements), so
      // on the whole key of Y. A key may become empty, as {1} with column 1
      // fixed: B then has at most one row.
      std::vector<std::set<uint32_t>> out;
      for (const std::set<uint32_t>& K : keys)
      {
        std::set<uint32_t> k2;
        for (uint32_t c : K)
        {
          if (!fixed.count(c))
          {
            k2.insert(find(c));
          }
        }
        out.push_back(k2);
      }
      return out;
    }
    // (bag.difference_subtract Y Z) and (bag.difference_remove Y Z) keep some
    // of the rows of Y, so the keys of Y
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE: return rowKeys(B[0]);
    case Kind::BAG_INTER_MIN:
    {
      // (bag.inter_min Y Z) is contained in both Y and Z, so the keys of each
      keys = rowKeys(B[0]);
      std::vector<std::set<uint32_t>> more = rowKeys(B[1]);
      keys.insert(keys.end(), more.begin(), more.end());
      return keys;
    }
    case Kind::BAG_SETOF:
    {
      // (bag.setof Y) has the rows of Y, so the keys of Y hold; and it has no
      // row twice, so all of its columns are a key too.
      keys = rowKeys(B[0]);
      // For (bag.setof (bag.map g Z)) with g's body (tuple a0 .. am), that
      // key leaves out a column j whose aj is a constant, the same in every
      // row, and a column j whose aj is the same term as that of an earlier
      // column, so equal to it; the first of equal columns stays. For
      // instance, for (tuple ((_ tuple.select 0) t) 5 ((_ tuple.select 0) t))
      // the key is {0}. For any other Y, it is all the columns.
      std::set<uint32_t> all;
      Node g =
          B[0].getKind() == Kind::BAG_MAP ? asLambda(B[0][0]) : Node::null();
      std::set<Node> seen;
      for (size_t k = 0; k < width; k++)
      {
        if (!g.isNull() && g.getKind() == Kind::LAMBDA && isTupleTerm(g[1])
            && g[1].getNumChildren() == width)
        {
          if (g[1][k].isConst() || !seen.insert(g[1][k]).second)
          {
            continue;
          }
        }
        all.insert(k);
      }
      keys.push_back(all);
      return keys;
    }
    case Kind::BAG_MAP:
    {
      // B = (bag.map g Y), with g = (lambda ((t ..)) (tuple a0 .. am)); for
      // another g no key is known.
      Node g = asLambda(B[0]);
      if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
          || !isTupleTerm(g[1]) || g[1].getNumChildren() != width)
      {
        return keys;
      }
      // carried maps each column c of Y that g copies, as some
      // aj = ((_ tuple.select c) t), to the first such column j of B
      Node x = g[0][0];
      std::map<uint32_t, uint32_t> carried;
      for (size_t k = 0; k < width; k++)
      {
        const Node& c = g[1][k];
        if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == x)
        {
          uint32_t col = datatypes::utils::indexOf(c.getOperator());
          if (!carried.count(col))
          {
            carried[col] = k;
          }
        }
      }
      // A key K of Y all of whose columns g copies gives the key of their
      // copies in B: two rows of Y differ on K, so their images differ on
      // the copies, and as Y has no row twice, no image occurs twice. A key
      // with a column that g does not copy is lost.
      for (const std::set<uint32_t>& K : rowKeys(B[1]))
      {
        std::set<uint32_t> out;
        bool kept = true;
        for (uint32_t c : K)
        {
          kept = kept && carried.count(c) > 0;
          if (kept)
          {
            out.insert(carried[c]);
          }
        }
        if (kept)
        {
          keys.push_back(out);
        }
      }
      return keys;
    }
    case Kind::TABLE_PRODUCT:
    {
      // B = (table.product Y Z): each key K1 of Y with each key K2 of Z gives
      // the key of K1 and of K2 shifted by the width wl of Y's rows. Two rows
      // of B that agree on it come from the same row of Y and the same row
      // of Z, and neither Y nor Z has a row twice.
      size_t wl = B[0].getType().getBagElementType().getTupleLength();
      for (const std::set<uint32_t>& K1 : rowKeys(B[0]))
      {
        for (const std::set<uint32_t>& K2 : rowKeys(B[1]))
        {
          std::set<uint32_t> out = K1;
          for (uint32_t c : K2)
          {
            out.insert(c + wl);
          }
          keys.push_back(out);
        }
      }
      return keys;
    }
    case Kind::TABLE_AGGREGATE:
    {
      // B = ((_ table.aggr K) f i Y), with
      // f = (lambda ((t ..) (acc ..)) (tuple e0 .. em)): B has one row per
      // group, and the rows of a group agree on the group columns K. When,
      // for each group column c, some ek is ((_ tuple.select c) t), column k
      // of a group's row is column c of the last row folded, the group's
      // value of c. Those columns k are a key of B, since two groups differ
      // on some group column; an empty Y gives B the one row i, and a table
      // of one row has every key. With no group columns, B has one row and
      // the key is empty. If a group column is not copied, no key is known.
      Node f = asLambda(B[0]);
      if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
          || !isTupleTerm(f[1]))
      {
        return keys;
      }
      Node x = f[0][0];
      std::set<uint32_t> out;
      for (uint32_t c : B.getOperator().getConst<ProjectOp>().getIndices())
      {
        // the first column k of f's result that copies group column c
        bool found = false;
        for (size_t k = 0; k < f[1].getNumChildren() && !found; k++)
        {
          const Node& e = f[1][k];
          if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == x
              && datatypes::utils::indexOf(e.getOperator()) == c)
          {
            out.insert(k);
            found = true;
          }
        }
        if (!found)
        {
          return keys;
        }
      }
      keys.push_back(out);
      return keys;
    }
    default: break;
  }
  // a table constant: its recorded keys (see keysOf); any other node, such as
  // (bag (tuple ..) 1) or a projection, has no key found
  if (B.isVar())
  {
    return keysOf(B);
  }
  return keys;
}

// The rules for an equality (= A B) of two bags, after A and B are rewritten,
// tried in this order:
// - EQ_REFL: sides that rewrote to one term make true;
// - EQ_CONST_FALSE: two constants make false. Bag constants are in a normal
//   form, so two constants that are not one node are distinct bags; this is
//   why EQ_REFL must come first;
// - EQ_SYM: the sides in one order, the smaller node first, so that (= A B)
//   and (= B A) become one node.
// For A : (Bag Int),
//   (= (bag.union_disjoint A (as bag.empty (Bag Int))) A)
//   ---> true                                                     (EQ_REFL)
//   (= (bag 1 2) (bag 1 3))
//   ---> false                                             (EQ_CONST_FALSE)
BagsRewriteResponse BagsRewriter::postRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() == Kind::BAG_EMPTY
        && (n[1 - i].getKind() == Kind::BAG_MAP
            || n[1 - i].getKind() == Kind::BAG_SETOF))
    {
      // EQ_EMPTY_ARG: a map or a bag.setof is empty when its argument is,
      //   (= (bag.map f X) (as bag.empty (Bag U)))
      //   ---> (= X (as bag.empty (Bag T)))
      //   (= (bag.setof X) (as bag.empty (Bag T)))
      //   ---> (= X (as bag.empty (Bag T)))
      Node X = n[1 - i][n[1 - i].getNumChildren() - 1];
      Node empty = d_nm->mkConst(EmptyBag(X.getType()));
      return BagsRewriteResponse(X.eqNode(empty), Rewrite::EQ_EMPTY_ARG);
    }
  }
  if (n[0] == n[1])
  {
    Node ret = d_nm->mkConst(true);
    return BagsRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    Node ret = d_nm->mkConst(false);
    return BagsRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // standard ordering
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return BagsRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.map f X), the bag of (f t) for the rows t of X, tried in
// this order; the first that changes the term returns it:
// - MAP_IDENTITY: a map that copies every column of X, in order, is X;
// - NOT_NULL_COLUMNS: the null tests in f's body of the columns that are
//   never null in the rows of X are decided (assumeNonNull);
// - MAP_CONST, MAP_BAG_MAKE and MAP_UNION_DISJOINT, for X a constant, a
//   (bag x c) or a bag.union_disjoint;
// - MAP_MAP, for X a map (rewriteMapOfMap);
// - AGGREGATE_DEAD_COLUMNS, for X an aggregate, possibly under a filter
//   (rewriteAggregateDeadColumns);
// - MAP_EQUAL_COLUMNS, then MAP_FIXED_COLUMNS, for X a filter;
// - CANONICAL_VARIABLE (canonicalLambda), last, so that f's variable is
//   renamed only once no other rule changes the term.
// For X : (Bag (Tuple Int Int)),
//   (bag.map
//     (lambda ((t (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
//     X)
//   ---> X                                                    (MAP_IDENTITY)
BagsRewriteResponse BagsRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAP);
  TypeNode mapType = n.getType();
  TypeNode argType = n[1].getType();
  if (mapType == argType && argType.getBagElementType().isTuple())
  {
    // MAP_IDENTITY, for a map whose result has the sort of X: J lists the
    // columns of t that f's tuple copies, {0, 1} for
    //   (lambda ((t (Tuple Int Int)))
    //     (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
    // or for (lambda ((t (Tuple Int Int))) ((_ tuple.project 0 1) t)), and is
    // empty when f is no such projection (see projectionIndices). f is the
    // identity when J is 0, 1, ..., w - 1 for the w columns of X.
    std::vector<uint32_t> J = projectionIndices(asLambda(n[0]));
    bool identity =
        J.size() == n[1].getType().getBagElementType().getTupleLength();
    for (size_t k = 0; k < J.size() && identity; k++)
    {
      identity = J[k] == k;
    }
    if (identity)
    {
      return BagsRewriteResponse(n[1], Rewrite::MAP_IDENTITY);
    }
  }
  {
    // NOT_NULL_COLUMNS: nonNullColumns reads off the shape of X the columns
    // that no row of X has null in, as column 1 of
    // X : (Bag (Tuple Int (Nullable Int))) given an assertion that it is NOT
    // NULL. In the body of g, f as a lambda (see asLambda), assumeNonNull
    // decides the null tests of these columns of g's variable t:
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true. The map by the
    // new body is the same bag, as the tests had these values on every row.
    Node g = asLambda(n[0]);
    if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
        && n[1].getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(g[1], g[0][0], nonNullColumns(n[1]));
      if (b != g[1])
      {
        Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(g[0][0], b), n[1]);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  if (n[1].isConst())
  {
    // (bag.map f (as bag.empty (Bag T1)) = (as bag.empty (Bag T2))
    // (bag.map f (bag "a" 3)) = (bag (f "a") 3)
    std::map<Node, Rational> elements = BagsUtils::getBagElements(n[1]);
    std::map<Node, Rational> mappedElements;
    std::map<Node, Rational>::iterator it = elements.begin();
    while (it != elements.end())
    {
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], it->first);
      mappedElements[mappedElement] = it->second;
      ++it;
    }
    TypeNode t = d_nm->mkBagType(n[0].getType().getRangeType());
    Node ret = BagsUtils::constructConstantBagFromElements(t, mappedElements);
    return BagsRewriteResponse(ret, Rewrite::MAP_CONST);
  }
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // (bag.map f (bag x y)) = (bag (apply f x) y)
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, mappedElement, n[1][1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.map f (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.map f A) (bag.map f B))
      Node a = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::MAP_UNION_DISJOINT);
    }

    case Kind::BAG_MAP:
    {
      // MAP_MAP: for X = (bag.map g Y), one map of Y by f composed with g,
      // when both are lambdas and with the higher-order flag (see
      // rewriteMapOfMap). When it does not apply, the rules below are tried.
      BagsRewriteResponse r = rewriteMapOfMap(n);
      if (r.d_node != n)
      {
        return r;
      }
      break;
    }
    // any other X goes on to the rules below
    default: break;
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 1)
  {
    // EQ_EMPTY_FILTER_DECORRELATE: the emptiness tests of filters in the
    // body, as formulas over the row, see normalizeEmptiness
    Node normalized = normalizeEmptiness(n[0][1]);
    if (normalized != n[0][1])
    {
      Node ret =
          d_nm->mkNode(Kind::BAG_MAP, mkLambda(n[0][0][0], normalized), n[1]);
      return BagsRewriteResponse(ret, Rewrite::EQ_EMPTY_FILTER_DECORRELATE);
    }
  }
  // The rules for a map of an aggregate, each implemented and documented in a
  // function of its own.
  {
    // MAP_SPLIT_CLOSED, see rewriteMapSplitClosed
    BagsRewriteResponse r = rewriteMapSplitClosed(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_DEAD_COLUMNS: for X an aggregate, or a filter of one, the
    // columns of the aggregate's rows that neither f nor the filter reads,
    // and that no other column's step reads, are not computed (see
    // rewriteAggregateDeadColumns, which returns n when the rule does not
    // apply)
    BagsRewriteResponse r = rewriteAggregateDeadColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_COLLAPSE, see rewriteAggregateCollapse
    BagsRewriteResponse r = rewriteAggregateCollapse(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_ROLLUP, see rewriteAggregateRollup
    BagsRewriteResponse r = rewriteAggregateRollup(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_JOIN_MERGE and AGGREGATE_SETOF_IDEMPOTENT, see
    // rewriteAggregateJoinMerge
    BagsRewriteResponse r = rewriteAggregateJoinMerge(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // PRODUCT_AGGREGATE_DEAD_COLUMN, see rewriteProductAggregateColumns
    BagsRewriteResponse r = rewriteProductAggregateColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_UNION_DISJOINT_KEYS, see rewriteAggregateUnionDisjointKeys
    BagsRewriteResponse r = rewriteAggregateUnionDisjointKeys(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_UNION_SPLIT, see rewriteAggregateUnionSplit
    BagsRewriteResponse r = rewriteAggregateUnionSplit(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // MAP_EQUAL_COLUMNS, for X = (bag.filter P Y): a row of Y that passes P
    // has equal values in two columns that a conjunct of P equates, as
    // (= ((_ tuple.select 0) r) ((_ tuple.select 2) r)), so f may read the
    // smallest column of each class of equated columns in place of the
    // others. Two maps that read different columns of a class then become one
    // term. f (as h) and P must be lambdas of one variable, over tuples.
    Node h = asLambda(n[0]);
    Node P = asLambda(n[1][0]);
    if (h.getKind() == Kind::LAMBDA && h[0].getNumChildren() == 1
        && P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1
        && n[1][1].getType().getBagElementType().isTuple())
    {
      Node r = P[0][0];
      size_t w = n[1][1].getType().getBagElementType().getTupleLength();
      // rep is a union-find over the w columns of Y: each column points to a
      // column it equals, the roots are the smallest of their classes, and
      // find returns the root of a column's class, shortening the path
      std::vector<uint32_t> rep(w);
      for (uint32_t col = 0; col < w; col++)
      {
        rep[col] = col;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t col) {
        return rep[col] == col ? col : (rep[col] = find(rep[col]));
      };
      // the conjuncts of P's body, or the body itself when it is not an and
      std::vector<Node> conjuncts;
      if (P[1].getKind() == Kind::AND)
      {
        conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
      }
      else
      {
        conjuncts.push_back(P[1]);
      }
      // a conjunct (= ((_ tuple.select a) r) ((_ tuple.select b) r)) over P's
      // own variable r merges the classes of a and b, under the smaller root
      for (const Node& c : conjuncts)
      {
        if (c.getKind() == Kind::EQUAL && c[0].getKind() == Kind::APPLY_SELECTOR
            && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
            && c[1][0] == r)
        {
          uint32_t a = find(datatypes::utils::indexOf(c[0].getOperator()));
          uint32_t b = find(datatypes::utils::indexOf(c[1].getOperator()));
          if (a != b)
          {
            rep[std::max(a, b)] = std::min(a, b);
          }
        }
      }
      // in f's body, over f's own variable v, each ((_ tuple.select col) v)
      // of a column that is not the root of its class is replaced by the read
      // of the root; the rule applies only when the body has such a read
      std::vector<Node> from, to;
      Node v = h[0][0];
      for (uint32_t col = 0; col < w; col++)
      {
        if (find(col) != col)
        {
          from.push_back(datatypes::TupleUtils::nthElementOfTuple(v, col));
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(v, find(col)));
        }
      }
      if (!from.empty())
      {
        Node body =
            h[1].substitute(from.begin(), from.end(), to.begin(), to.end());
        if (body != h[1])
        {
          Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(v, body), n[1]);
          return BagsRewriteResponse(ret, Rewrite::MAP_EQUAL_COLUMNS);
        }
      }
    }
  }
  {
    // AGGREGATE_GROUP_KEYS: the distinct group columns of the groups some row
    // reached, read off the rows, see keysOfReachedGroups:
    //   (bag.map h (bag.filter P ((_ table.aggr 0) f i X)))
    //   ---> (bag.setof (bag.map h' X))
    Node m = keysOfReachedGroups(asLambda(n[0]), n[1], true);
    if (!m.isNull())
    {
      return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_SETOF, m),
                                 Rewrite::AGGREGATE_GROUP_KEYS);
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER && n[0].getKind() == Kind::LAMBDA
      && n[0][0].getNumChildren() == 1)
  {
    // MAP_FIXED_COLUMNS, for X = (bag.filter P Y) and f a lambda node: a row
    // that passes P has in column k the constant c of a conjunct
    // (= ((_ tuple.select k) r) c) of P, so f's body may read c in place of
    // ((_ tuple.select k) t). fixed maps each such k to its c (see
    // fixedColumns), and readFixed makes the replacements.
    std::map<uint32_t, Node> fixed = fixedColumns(n[1][0]);
    if (n[1][1].getKind() == Kind::TABLE_AGGREGATE)
    {
      // For Y an aggregate and P a test that its counter column, the count of
      // rows of each group, is at least 1, P keeps only the groups that some
      // row of the aggregate's input made. In each of them, a column that the
      // step sets to a constant, or keeps at a constant initial value, has
      // that constant (see reachedGroupConstants). Where P also fixes the
      // column, insert keeps P's constant.
      std::map<uint32_t, Node> constant = reachedGroupConstants(n[1]);
      fixed.insert(constant.begin(), constant.end());
    }
    Node var = n[0][0][0];
    Node body = readFixed(n[0][1], var, fixed);
    if (body != n[0][1])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(var, body), n[1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_FIXED_COLUMNS);
    }
    // MAP_IDENTITY_ON_FILTER: a map over a filter that keeps every column of
    // the rows that pass, each the row's own or the constant the filter fixes
    // it to, is the filter (see rewrites.h)
    TypeNode rowType = n[1].getType().getBagElementType();
    if (body.getKind() == Kind::APPLY_CONSTRUCTOR && body.getType() == rowType
        && rowType.isTuple())
    {
      // or a column the filter sets equal to it, as MAP_EQUAL_COLUMNS leaves
      // (tuple ((_ tuple.select 0) t) ((_ tuple.select 0) t)) over a filter
      // with (= ((_ tuple.select 0) s) ((_ tuple.select 1) s)); equal holds
      // the pairs of columns equated, both ways
      std::set<std::pair<uint32_t, uint32_t>> equal;
      Node P = asLambda(n[1][0]);
      if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
      {
        std::vector<Node> conjuncts;
        if (P[1].getKind() == Kind::AND)
        {
          conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
        }
        else
        {
          conjuncts.push_back(P[1]);
        }
        for (const Node& c : conjuncts)
        {
          if (c.getKind() == Kind::EQUAL
              && c[0].getKind() == Kind::APPLY_SELECTOR
              && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == P[0][0]
              && c[1][0] == P[0][0])
          {
            uint32_t a = datatypes::utils::indexOf(c[0].getOperator());
            uint32_t b = datatypes::utils::indexOf(c[1].getOperator());
            equal.insert({a, b});
            equal.insert({b, a});
          }
        }
      }
      bool identity = true;
      for (size_t col = 0, w = body.getNumChildren(); col < w && identity;
           col++)
      {
        Node own = datatypes::TupleUtils::nthElementOfTuple(var, col);
        std::map<uint32_t, Node>::iterator it = fixed.find(col);
        identity =
            body[col] == own || (it != fixed.end() && body[col] == it->second);
        if (!identity && body[col].getKind() == Kind::APPLY_SELECTOR
            && body[col][0] == var)
        {
          uint32_t j = datatypes::utils::indexOf(body[col].getOperator());
          identity = equal.count({j, static_cast<uint32_t>(col)}) > 0;
        }
      }
      if (identity)
      {
        return BagsRewriteResponse(n[1], Rewrite::MAP_IDENTITY_ON_FILTER);
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // SEMI_TO_INTERSECTION, see semiJoinToIntersection
    Node inter = semiJoinToIntersection(n, false);
    if (!inter.isNull())
    {
      return BagsRewriteResponse(inter, Rewrite::SEMI_TO_INTERSECTION);
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER
      && n[1][1].getKind() == Kind::TABLE_PRODUCT)
  {
    // SEMI_JOIN, see rewriteSemiJoin
    for (size_t side = 0; side < 2; side++)
    {
      BagsRewriteResponse r = rewriteSemiJoin(n, side);
      if (r.d_node != n)
      {
        return r;
      }
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 1)
  {
    // CANONICAL_VARIABLE: f with its variable renamed to t_N, N the id of f's
    // alpha key, a node that is the same for lambdas that differ only in the
    // names of their variables (see canonicalLambda). Such lambdas then become
    // one node, which the solver treats as one function.
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, canonical, n[1]);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.filter P A), the rows t of A with (P t), tried in this
// order; the first that changes the term returns it:
// - none for the filter of a NOT NULL assertion (see BagsKeyTermAttribute);
// - NOT_NULL_COLUMNS: the null tests in P's body of the columns that are
//   never null in the rows of A are decided (assumeNonNull);
// - FILTER_TRUE and FILTER_FALSE, for a body that is a constant;
// - FILTER_NULLABLE_TRUTH (normalizeTruth);
// - FILTER_CONFLICTING_CONSTANTS: empty when conjuncts fix one term to two
//   constants, and otherwise the conjuncts that other conjuncts imply go;
// - FILTER_FALSE, for a conjunct next to its negation;
// - CANONICAL_VARIABLE (canonicalLambda);
// - FILTER_CONST, FILTER_BAG_MAKE and FILTER_UNION_DISJOINT, for A a
//   constant, a (bag x c) or a bag.union_disjoint;
// - FILTER_MAP, for A a map (rewriteFilterOfMap);
// - AGGREGATE_KEYED, for A an aggregate, or a product with aggregates among
//   its components (keyedAggregateRows, reachedComponents).
// The rules that simplify P come before those that read the shape of A, so
// the latter see only a P that the former leave as it is.
// For X : (Bag (Tuple Int Int)),
//   (bag.filter
//     (lambda ((t (Tuple Int Int)))
//       (and (= ((_ tuple.select 0) t) 1) (= ((_ tuple.select 0) t) 2)))
//     X)
//   ---> (as bag.empty (Bag (Tuple Int Int)))  (FILTER_CONFLICTING_CONSTANTS)
BagsRewriteResponse BagsRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  Node P = n[0];
  Node A = n[1];
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // The filter of a NOT NULL assertion, which states that a column of a
    // table X is never null, as
    //   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
    //                    (= ((_ tuple.select 1) t)
    //                       (as nullable.null (Nullable Int))))
    //                  X)
    //      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
    // recordNotNull read the fact off it and marked it. Rewriting it by the
    // fact would make the assertion true and lose the fact, so it stays.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode t = A.getType();
  {
    // FILTER_COUNT_AS_COUNTER: an aggregate with a counter column c, the count
    // of rows of its group, whose step is (+ ((_ tuple.select c) acc) 1) from
    // 0, has on every row a COUNT(*) column q, one whose step counts rows from
    // (nullable.some 0) (see isCountStep), equal to
    // (nullable.some ((_ tuple.select c) t)); the filter reads column q so,
    // which makes a test of COUNT(*) a test of the counter, which the solver
    // relates to the rows of the group (see rewrites.h). Also for the
    // aggregates among the components of a product: the components of
    // (table.product G (table.product Y Z)) are G, Y and Z, whose columns start
    // at starts[i] in the rows of the product.
    Node p = asLambda(P);
    if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1
        && (A.getKind() == Kind::TABLE_AGGREGATE
            || A.getKind() == Kind::TABLE_PRODUCT))
    {
      std::vector<Node> comps;
      std::vector<size_t> starts;
      Node rest = A;
      size_t at = 0;
      bool tuples = true;
      while (tuples)
      {
        Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
        tuples = c.getType().getBagElementType().isTuple();
        if (!tuples)
        {
          break;
        }
        comps.push_back(c);
        starts.push_back(at);
        at += c.getType().getBagElementType().getTupleLength();
        if (rest.getKind() != Kind::TABLE_PRODUCT)
        {
          break;
        }
        rest = rest[1];
      }
      std::vector<Node> from, to;
      for (size_t i = 0; tuples && i < comps.size(); i++)
      {
        const Node& G = comps[i];
        Node f = G.getKind() == Kind::TABLE_AGGREGATE ? asLambda(G[0])
                                                      : Node::null();
        if (f.isNull() || f.getKind() != Kind::LAMBDA
            || f[0].getNumChildren() != 2 || !isTupleTerm(f[1])
            || !isTupleTerm(G[1]))
        {
          continue;
        }
        Node acc = f[0][1];
        int counter = -1;
        for (size_t q = 0; q < f[1].getNumChildren(); q++)
        {
          Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
          const Node& e = f[1][q];
          if (e.getKind() == Kind::ADD && e.getNumChildren() == 2
              && ((e[0] == own && e[1] == d_one)
                  || (e[1] == own && e[0] == d_one))
              && G[1][q].isConst() && G[1][q].getConst<Rational>().isZero())
          {
            counter = static_cast<int>(q);
          }
        }
        for (size_t q = 0; counter >= 0 && q < f[1].getNumChildren(); q++)
        {
          Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
          const Node& e = f[1][q];
          if (static_cast<int>(q) == counter || e.getKind() == Kind::ITE
              || !isCountStep(e, own, G[1][q]))
          {
            continue;
          }
          // ((_ tuple.select q) t) is read as
          // (nullable.some ((_ tuple.select c) t)), si the index of the
          // constructor nullable.some
          const DType& dt = e.getType().getDType();
          size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
          from.push_back(
              datatypes::TupleUtils::nthElementOfTuple(p[0][0], starts[i] + q));
          to.push_back(d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                    dt[si].getConstructor(),
                                    datatypes::TupleUtils::nthElementOfTuple(
                                        p[0][0], starts[i] + counter)));
        }
      }
      if (!from.empty())
      {
        Node b =
            p[1].substitute(from.begin(), from.end(), to.begin(), to.end());
        if (b != p[1])
        {
          Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(p[0][0], b), A);
          return BagsRewriteResponse(ret, Rewrite::FILTER_COUNT_AS_COUNTER);
        }
      }
    }
  }
  {
    // NOT_NULL_COLUMNS: nonNullColumns reads off the shape of A the columns
    // that no row of A has null in, as column 1 of
    // A : (Bag (Tuple Int (Nullable Int))) given an assertion that it is NOT
    // NULL. In the body of p, P as a lambda (see asLambda), assumeNonNull
    // decides the null tests of these columns of p's variable t:
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true. The filter by
    // the new body keeps the same rows, as the tests had these values on all.
    Node p = asLambda(P);
    if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1
        && A.getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(p[1], p[0][0], nonNullColumns(A));
      if (b != p[1])
      {
        Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(p[0][0], b), A);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  {
    Node lambda = asLambda(P);
    if (lambda.getKind() == Kind::LAMBDA && lambda[1].isConst())
    {
      // FILTER_TRUE and FILTER_FALSE: a predicate whose body is true keeps
      // every row, and one whose body is false keeps none. The rewriter turns
      // a lambda with a constant body into a function array constant, which
      // asLambda turns back into the lambda; P may also be a lambda node.
      if (lambda[1].getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
  }
  if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
  {
    // EQ_EMPTY_FILTER_DECORRELATE: the emptiness tests of filters in the
    // predicate, as formulas over the row, see normalizeEmptiness
    Node normalized = normalizeEmptiness(P[1]);
    if (normalized != P[1])
    {
      Node ret =
          d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], normalized), A);
      return BagsRewriteResponse(ret, Rewrite::EQ_EMPTY_FILTER_DECORRELATE);
    }
    // FILTER_NULLABLE_TRUTH: SQL's three-valued truth value is a
    // (Nullable Bool) b, and a row passes when b is (nullable.some true),
    // not when it is (nullable.some false) or null. The body may say so by
    // the two conjuncts (nullable.is_some b) and (nullable.val b);
    // normalizeTruth replaces them by the one formula they state, so that
    // predicates that say the same in either way become one term.
    Node truth = normalizeTruth(P[1]);
    if (truth != P[1])
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], truth), A);
      return BagsRewriteResponse(ret, Rewrite::FILTER_NULLABLE_TRUTH);
    }
  }
  if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
  {
    Node body = P[1];
    if (body.isConst())
    {
      // FILTER_TRUE and FILTER_FALSE again. The test above already returns
      // for a lambda node with a constant body (asLambda leaves a lambda as
      // it is), so this branch is not reached.
      if (body.getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
    {
      // FILTER_DE_MORGAN: a conjunct (not (or a b)) is the conjuncts (not a)
      // and (not b), which the rules below read one at a time (see rewrites.h)
      // cs: the conjuncts of the body, or the body itself when it is not an
      // and
      std::vector<Node> cs;
      if (body.getKind() == Kind::AND)
      {
        cs.insert(cs.end(), body.begin(), body.end());
      }
      else
      {
        cs.push_back(body);
      }
      bool split = false;
      std::vector<Node> flat;
      for (const Node& c : cs)
      {
        if (c.getKind() == Kind::NOT && c[0].getKind() == Kind::OR)
        {
          for (const Node& d : c[0])
          {
            flat.push_back(d.notNode());
          }
          split = true;
        }
        else
        {
          flat.push_back(c);
        }
      }
      if (split)
      {
        Node newBody =
            flat.size() == 1 ? flat[0] : d_nm->mkNode(Kind::AND, flat);
        Node ret =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], newBody), A);
        return BagsRewriteResponse(ret, Rewrite::FILTER_DE_MORGAN);
      }
      // FILTER_CONFLICTING_CONSTANTS, first part: a conjunct (= a c), or
      // (= c a), with c a constant and a not, fixes the term a to c. When two
      // conjuncts fix one term to two distinct constants, no row passes and
      // the filter is empty; constants are in a normal form, so two distinct
      // constant nodes are two distinct values. fixed maps each term that a
      // conjunct fixes to its constant.
      std::map<Node, Node> fixed;
      for (const Node& c : flat)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        bool leftConst = c[0].isConst();
        bool rightConst = c[1].isConst();
        // an equality of two constants, or of two terms that are not, fixes
        // nothing
        if (leftConst == rightConst)
        {
          continue;
        }
        Node a = c[0].isConst() ? c[1] : c[0];
        Node v = c[0].isConst() ? c[0] : c[1];
        auto it = fixed.find(a);
        if (it == fixed.end())
        {
          fixed[a] = v;
        }
        else if (it->second != v)
        {
          return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                     Rewrite::FILTER_CONFLICTING_CONSTANTS);
        }
      }
      // nonNull: the terms that a membership conjunct puts in a column that is
      // never null. For (>= (bag.count (tuple a e) Y) 1) and column 1 of Y
      // never null (see nonNullColumns), the row (tuple a e) is in Y, so e is
      // not null.
      std::set<Node> nonNull;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && c[0].getKind() == Kind::BAG_COUNT
            && c[0][0].getKind() == Kind::APPLY_CONSTRUCTOR
            && c[0][1].getType().getBagElementType().isTuple())
        {
          std::set<uint32_t> nn = nonNullColumns(c[0][1]);
          for (uint32_t k : nn)
          {
            if (k < c[0][0].getNumChildren())
            {
              nonNull.insert(c[0][0][k]);
            }
          }
        }
      }
      // FILTER_KNOWN_NONEMPTY: a bag that a membership conjunct finds a row in,
      // or a bag that it reaches that row from through maps, filters and
      // bag.setof, is not empty, and a conjunct that says so goes; the filter
      // is empty when a conjunct says that the bag is empty (see rewrites.h)
      {
        std::set<Node> nonEmpty;
        for (const Node& c : flat)
        {
          if (c.getKind() == Kind::GEQ && c[1].isConst()
              && c[1].getConst<Rational>() == Rational(1)
              && c[0].getKind() == Kind::BAG_COUNT)
          {
            Node X = c[0][1];
            while (true)
            {
              nonEmpty.insert(X);
              if (X.getKind() == Kind::BAG_MAP
                  || X.getKind() == Kind::BAG_FILTER)
              {
                X = X[1];
              }
              else if (X.getKind() == Kind::BAG_SETOF)
              {
                X = X[0];
              }
              else
              {
                break;
              }
            }
          }
        }
        bool changed = false;
        std::vector<Node> rewritten;
        for (const Node& c : flat)
        {
          Node e = c.getKind() == Kind::NOT ? c[0] : c;
          bool empty = false;
          if (e.getKind() == Kind::EQUAL && e[0].getType().isBag())
          {
            for (size_t sd = 0; sd < 2 && !empty; sd++)
            {
              empty = e[sd].getKind() == Kind::BAG_EMPTY
                      && nonEmpty.count(e[1 - sd]) > 0;
            }
          }
          if (!empty)
          {
            rewritten.push_back(c);
            continue;
          }
          changed = true;
          if (c.getKind() != Kind::NOT)
          {
            // a conjunct that is false
            return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                       Rewrite::FILTER_KNOWN_NONEMPTY);
          }
        }
        if (changed)
        {
          Node newBody = rewritten.empty()
                             ? d_nm->mkConst(true)
                             : (rewritten.size() == 1
                                    ? rewritten[0]
                                    : d_nm->mkNode(Kind::AND, rewritten));
          Node ret =
              d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], newBody), A);
          return BagsRewriteResponse(ret, Rewrite::FILTER_KNOWN_NONEMPTY);
        }
      }
      // FILTER_CONFLICTING_CONSTANTS, second part: a conjunct that other
      // conjuncts imply goes. These are
      // - a tester of the constructor of the constant that fixed maps its
      //   argument to, as (nullable.is_some a) next to (= a (nullable.some 5));
      // - (nullable.is_some e), or (not (= (as nullable.null (Nullable Int))
      //   e)) either way round, for e in nonNull;
      // - (>= (* a b) 1), of integers, next to (>= a 1) and (>= b 1): a
      //   product of positive integers is positive. Such a conjunct tests that
      //   the product of the counts of rows of two groups is positive.
      // positive holds the integer terms a of the conjuncts (>= a 1).
      std::set<Node> positive;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && c[0].getType().isInteger())
        {
          positive.insert(c[0]);
        }
      }
      std::vector<Node> kept;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && (c[0].getKind() == Kind::MULT
                || c[0].getKind() == Kind::NONLINEAR_MULT))
        {
          // the product goes when every factor is in positive
          bool implied = true;
          for (const Node& m : c[0])
          {
            implied = implied && positive.count(m) > 0;
          }
          if (implied)
          {
            continue;
          }
        }
        // ci is the index of the constructor that c tests a for, when c is a
        // tester, and -1 otherwise
        Node a;
        int ci = datatypes::utils::isTester(c, a);
        auto it = ci >= 0 ? fixed.find(a) : fixed.end();
        if (it != fixed.end() && it->second.getKind() == Kind::APPLY_CONSTRUCTOR
            && datatypes::utils::indexOf(it->second.getOperator())
                   == static_cast<size_t>(ci))
        {
          // a is fixed to a constant of the constructor that c tests for
          continue;
        }
        if (ci >= 0 && nonNull.count(a) && a.getType().isNullable()
            && a.getType().getDType()[ci].getNumArgs() == 1)
        {
          // c tests a, which is not null, for nullable.some, the constructor
          // of a nullable sort that has an argument
          continue;
        }
        if (c.getKind() == Kind::NOT && c[0].getKind() == Kind::EQUAL
            && ((isNullConstant(c[0][0]) && nonNull.count(c[0][1]))
                || (isNullConstant(c[0][1]) && nonNull.count(c[0][0]))))
        {
          continue;
        }
        kept.push_back(c);
      }
      // when a conjunct went, the filter by the others, or by true when none
      // is left
      if (kept.size() < flat.size())
      {
        Node newBody =
            kept.empty()
                ? d_nm->mkConst(true)
                : (kept.size() == 1 ? kept[0] : d_nm->mkNode(Kind::AND, kept));
        Node ret =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], newBody), A);
        return BagsRewriteResponse(ret, Rewrite::FILTER_CONFLICTING_CONSTANTS);
      }
    }
    {
      // FILTER_INTO_SETOF, see rewriteFilterIntoSetofComponent
      BagsRewriteResponse r = rewriteFilterIntoSetofComponent(n);
      if (r.d_node != n)
      {
        return r;
      }
    }
    {
      // FILTER_KNOWN_MEMBERSHIP: memberships every row of A satisfies, see
      // dropKnownMemberships
      Node simpler = dropKnownMemberships(body, P[0][0], A);
      if (simpler != body)
      {
        Node ret =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], simpler), A);
        return BagsRewriteResponse(ret, Rewrite::FILTER_KNOWN_MEMBERSHIP);
      }
    }
    if (body.getKind() == Kind::AND)
    {
      // FILTER_FALSE: no row passes a conjunct c and its negation (not c),
      // so a body (and .. c .. (not c) ..) makes the filter empty
      std::unordered_set<Node> present(body.begin(), body.end());
      for (const Node& c : body)
      {
        if (c.getKind() == Kind::NOT && present.count(c[0]))
        {
          return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                     Rewrite::FILTER_FALSE);
        }
      }
      // FILTER_SORT_CONJUNCTS: the conjuncts in one order, without duplicates,
      // so that two filters by the same conjunction, merged in different
      // orders, are one lambda (see rewrites.h). The order is by alphaKey,
      // which does not depend on the name of the row variable: the name is
      // chosen after the order (canonicalLambda), so an order by node id would
      // change with it.
      std::vector<Node> cs(body.begin(), body.end());
      std::vector<Node> sorted = cs;
      sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
      Node var = P[0][0];
      std::map<Node, Node> keys;
      for (const Node& c : sorted)
      {
        keys[c] = alphaKey(mkLambda(var, c));
      }
      std::stable_sort(
          sorted.begin(), sorted.end(), [&](const Node& a, const Node& b) {
            return keys[a] < keys[b];
          });
      std::vector<Node> deduped;
      for (const Node& c : sorted)
      {
        if (deduped.empty() || keys[deduped.back()] != keys[c]
            || deduped.back() != c)
        {
          if (std::find(deduped.begin(), deduped.end(), c) == deduped.end())
          {
            deduped.push_back(c);
          }
        }
      }
      sorted = deduped;
      if (sorted != cs)
      {
        Node newBody =
            sorted.size() == 1 ? sorted[0] : d_nm->mkNode(Kind::AND, sorted);
        Node ret =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], newBody), A);
        return BagsRewriteResponse(ret, Rewrite::FILTER_SORT_CONJUNCTS);
      }
    }
    // CANONICAL_VARIABLE: P with its variable renamed to t_N, N the id of P's
    // alpha key, a node that is the same for lambdas that differ only in the
    // names of their variables (see canonicalLambda), so that such lambdas
    // become one node
    Node canonical = canonicalLambda(P);
    if (canonical != P)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, canonical, A);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
    if (body.getKind() == Kind::OR)
    {
      // FILTER_SPLIT_CLOSED: a disjunct c that does not read the row, such as
      // EXISTS of a subquery, splits the filter in two, by c and by (not c)
      // with the other disjuncts: a row passes one of the two exactly when it
      // passes the disjunction, and never both (see rewrites.h)
      Node var = P[0][0];
      for (size_t k = 0, m = body.getNumChildren(); k < m; k++)
      {
        if (occursFree(body[k], var))
        {
          // or a question about a bag that reads the row and nothing else,
          // such as IN (subquery), (>= (bag.count ((_ tuple.project 0) t) Y)
          // 1): split on it as on EXISTS
          std::unordered_set<Node> fvs;
          expr::getFreeVariables(body[k], fvs);
          fvs.erase(var);
          if (!fvs.empty()
              || !expr::hasSubtermKinds({Kind::BAG_FILTER,
                                         Kind::BAG_MAP,
                                         Kind::BAG_COUNT,
                                         Kind::BAG_SETOF,
                                         Kind::TABLE_PRODUCT,
                                         Kind::TABLE_AGGREGATE,
                                         Kind::TABLE_PROJECT},
                                        body[k]))
          {
            continue;
          }
        }
        Node c = body[k];
        std::vector<Node> rest;
        for (size_t j = 0; j < m; j++)
        {
          if (j != k)
          {
            rest.push_back(body[j]);
          }
        }
        Node q = rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::OR, rest);
        Node a = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(var, c), A);
        Node b = d_nm->mkNode(
            Kind::BAG_FILTER, mkLambda(var, c.notNode().andNode(q)), A);
        Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
        return BagsRewriteResponse(ret, Rewrite::FILTER_SPLIT_CLOSED);
      }
    }
  }
  if (A.isConst())
  {
    // (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
    // (bag.filter p (bag "a" 3) ((bag "b" 2))) =
    //   (bag.union_disjoint
    //     (ite (p "a") (bag "a" 3) (as bag.empty (Bag T)))
    //     (ite (p "b") (bag "b" 2) (as bag.empty (Bag T)))

    Node ret = BagsUtils::evaluateBagFilter(n);
    return BagsRewriteResponse(ret, Rewrite::FILTER_CONST);
  }
  Kind k = A.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // FILTER_BAG_MAKE: x is kept as often as it occurs when it passes, and
      // not at all otherwise. The result is a bag of x again, with an ite as
      // its count, rather than an ite of two bags, so that a map or a product
      // over it still has a (bag x ..) to apply its rules to:
      //   (bag.filter p (bag x y)) ---> (bag x (ite (p x) y 0))
      Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, A[0]);
      Node count = d_nm->mkNode(Kind::ITE, pOfe, A[1], d_zero);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, A[0], count);
      return BagsRewriteResponse(ret, Rewrite::FILTER_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.filter p (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.filter p A) (bag.filter p B))
      Node a = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::FILTER_UNION_DISJOINT);
    }

    // FILTER_FILTER, see rewriteFilterOfFilter
    case Kind::BAG_FILTER: return rewriteFilterOfFilter(n);
    // FILTER_MAP: a filter of a map is a map of a filter, by the predicate of
    // the image of each row, when both functions are lambdas and with the
    // higher-order flag (see rewriteFilterOfMap, which returns n otherwise)
    case Kind::BAG_MAP: return rewriteFilterOfMap(n);
    case Kind::TABLE_AGGREGATE:
    {
      // AGGREGATE_KEYED, for A = ((_ table.aggr K) f i Y). The aggregate of an
      // empty Y is one row, the row of initial values i, which SQL's GROUP BY
      // does not have; P drops that row when (P i) rewrites to false (see
      // rejectsInitialRow). When K contains a key of Y, columns on which no
      // two rows of Y agree, every group is one row t of Y, folded once, so
      // the aggregate's other rows are (bag.map (lambda ((t ..)) (f t i)) Y)
      // (see keyedAggregateRows, null when K holds no key), and the filter of
      // that map keeps the same rows.
      if (rejectsInitialRow(n[0], A[1]))
      {
        Node rows = keyedAggregateRows(A);
        if (!rows.isNull())
        {
          Node ret = d_nm->mkNode(Kind::BAG_FILTER, n[0], rows);
          return BagsRewriteResponse(ret, Rewrite::AGGREGATE_KEYED);
        }
      }
      // FILTER_AGGREGATE_ONE_ROW: an aggregate of a single row e, with Q
      // keeping only the groups some row reached (Q tests the counter
      // positive, see counterColumn) and m 1 or (ite c 1 0), is that row's
      // group folded once, m times:
      //   (bag.filter Q ((_ table.aggr 0) f i (bag e m)))
      //   ---> (bag.filter Q (bag (f e i) m))
      // where (f e i) is f's body with t := e and acc := i; with m 0 the
      // aggregate's row of initial values has counter 0 and Q drops it
      Node G = A;
      Node f = asLambda(G[0]);
      if (G[2].getKind() == Kind::BAG_MAKE && f.getKind() == Kind::LAMBDA
          && f[0].getNumChildren() == 2 && counterColumn(n[0], f, G[1]) >= 0)
      {
        Node m = G[2][1];
        bool oneOrNone =
            (m.isConst() && m.getConst<Rational>() == Rational(1))
            || (m.getKind() == Kind::ITE && m[1].isConst() && m[2].isConst()
                && ((m[1].getConst<Rational>() == Rational(1)
                     && m[2].getConst<Rational>().isZero())
                    || (m[2].getConst<Rational>() == Rational(1)
                        && m[1].getConst<Rational>().isZero())));
        if (oneOrNone)
        {
          // (f e i), the body of f with t := e and acc := i
          std::vector<Node> from{f[0][0], f[0][1]};
          std::vector<Node> to{G[2][0], G[1]};
          Node row =
              f[1].substitute(from.begin(), from.end(), to.begin(), to.end());
          Node ret = d_nm->mkNode(
              Kind::BAG_FILTER, n[0], d_nm->mkNode(Kind::BAG_MAKE, row, m));
          return BagsRewriteResponse(ret, Rewrite::FILTER_AGGREGATE_ONE_ROW);
        }
      }
      // FILTER_AGGREGATE, see rewriteFilterOfAggregate
      return rewriteFilterOfAggregate(n);
    }
    case Kind::BAG_SETOF:
    {
      // FILTER_SETOF:
      //   (bag.filter p (bag.setof A)) ---> (bag.setof (bag.filter p A))
      Node inner = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_SETOF, inner);
      return BagsRewriteResponse(ret, Rewrite::FILTER_SETOF);
    }
    case Kind::BAG_INTER_MIN:
    {
      // FILTER_INTER_MIN:
      //   (bag.filter p (bag.inter_min A B))
      //   ---> (bag.inter_min (bag.filter p A) (bag.filter p B))
      Node a = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_INTER_MIN, a, b);
      return BagsRewriteResponse(ret, Rewrite::FILTER_INTER_MIN);
    }
    case Kind::TABLE_PRODUCT:
    {
      {
        // AGGREGATE_KEYED, for A a product. The components of A are the
        // factors of the right-nested product, G, Y and Z for
        // (table.product G (table.product Y Z)), and starts holds the column
        // of A's rows at which the columns of each component start. An
        // aggregate among them has a row of initial values when its input is
        // empty; a component is "reached" when no row that passes P has that
        // row in its columns, as when P tests the component's count of rows
        // positive (see reachedComponents). A reached aggregate grouped by a
        // key of its input is replaced by the rows of its groups, as in the
        // case above (see keyedAggregateRows): the rows of A that this drops
        // do not pass P.
        std::vector<Node> comps;
        std::vector<size_t> starts;
        Node rest = A;
        size_t at = 0;
        // collect the components from left to right; tuples is false when a
        // component's rows are not tuples, and then nothing is done
        bool tuples = true;
        while (tuples)
        {
          Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
          tuples = c.getType().getBagElementType().isTuple();
          comps.push_back(c);
          starts.push_back(at);
          if (!tuples || rest.getKind() != Kind::TABLE_PRODUCT)
          {
            break;
          }
          at += c.getType().getBagElementType().getTupleLength();
          rest = rest[1];
        }
        if (tuples)
        {
          // reached[c] is nonzero for a reached component c; test, which
          // gives the conjunct of P that tests each component's count, is not
          // read here
          std::vector<int> test;
          std::vector<int> reached =
              reachedComponents(n[0], comps, starts, test);
          bool changed = false;
          for (size_t c = 0; c < comps.size(); c++)
          {
            if (reached[c] && comps[c].getKind() == Kind::TABLE_AGGREGATE)
            {
              // null when the group columns hold no key of the input
              Node rows = keyedAggregateRows(comps[c]);
              if (!rows.isNull())
              {
                comps[c] = rows;
                changed = true;
              }
            }
          }
          if (changed)
          {
            // the right-nested product of the new components, built from the
            // last one leftwards, under the same filter
            Node prod = comps.back();
            for (size_t pos = comps.size() - 1; pos-- > 0;)
            {
              prod = d_nm->mkNode(Kind::TABLE_PRODUCT, comps[pos], prod);
            }
            Node ret = d_nm->mkNode(Kind::BAG_FILTER, n[0], prod);
            return BagsRewriteResponse(ret, Rewrite::AGGREGATE_KEYED);
          }
        }
      }
      {
        // FILTER_IMPLIED_COUNTER, see dropImpliedCounters
        BagsRewriteResponse r = dropImpliedCounters(n);
        if (r.d_node != n)
        {
          return r;
        }
      }
      {
        // FILTER_JOIN_TRANSITIVE, see rewriteJoinTransitiveConditions
        BagsRewriteResponse r = rewriteJoinTransitiveConditions(n);
        if (r.d_node != n)
        {
          return r;
        }
      }
      // FILTER_EQUI_JOIN_SETS, see rewriteEquiJoinOfSets
      return rewriteEquiJoinOfSets(n);
    }
    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
}

BagsRewriteResponse BagsRewriter::rewriteJoinTransitiveConditions(
    const TNode& n) const
{
  // FILTER_JOIN_TRANSITIVE, for (bag.filter P (table.product C0 C1 ..)) where P
  // equates columns of different components: a condition on one column of a
  // class of equated columns that the rows of its component satisfy, read off
  // the component and the conjuncts of P on it alone (see elementConditions),
  // holds of the first column of the class too, and joins P when it is not
  // there, so that a condition written on either side of a join is on both
  // (see rewrites.h)
  Node P = asLambda(n[0]);
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || d_rewriter == nullptr)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node r = P[0][0];
  std::vector<Node> comps;
  std::vector<size_t> starts;
  {
    Node rest = n[1];
    size_t at = 0;
    while (true)
    {
      Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
      if (!c.getType().getBagElementType().isTuple())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      comps.push_back(c);
      starts.push_back(at);
      at += c.getType().getBagElementType().getTupleLength();
      if (rest.getKind() != Kind::TABLE_PRODUCT)
      {
        break;
      }
      rest = rest[1];
    }
  }
  size_t width = starts.back()
                 + comps.back().getType().getBagElementType().getTupleLength();
  auto compOf = [&](size_t pos) {
    size_t c = 0;
    while (c + 1 < comps.size() && starts[c + 1] <= pos)
    {
      c++;
    }
    return c;
  };
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  // the classes of equated columns, a union-find whose representative is the
  // smallest column, {0, 2} for (= ((_ tuple.select 0) t) ((_ tuple.select 2)
  // t)); across is whether some class has columns of two components
  std::vector<uint32_t> rep(width);
  for (uint32_t k = 0; k < width; k++)
  {
    rep[k] = k;
  }
  std::function<uint32_t(uint32_t)> find = [&](uint32_t k) {
    return rep[k] == k ? k : (rep[k] = find(rep[k]));
  };
  bool across = false;
  for (const Node& c : conjuncts)
  {
    if (c.getKind() == Kind::EQUAL && c[0].getKind() == Kind::APPLY_SELECTOR
        && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
        && c[1][0] == r)
    {
      uint32_t a = find(datatypes::utils::indexOf(c[0].getOperator()));
      uint32_t b = find(datatypes::utils::indexOf(c[1].getOperator()));
      if (a != b)
      {
        across = across || compOf(a) != compOf(b);
        rep[std::max(a, b)] = std::min(a, b);
      }
    }
  }
  if (!across)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::set<Node> present(conjuncts.begin(), conjuncts.end());
  std::vector<Node> added;
  for (size_t i = 0; i < comps.size(); i++)
  {
    size_t w = comps[i].getType().getBagElementType().getTupleLength();
    // P's conjuncts on this component alone, over its rows: column
    // starts[i] + k of t is column k of v
    Node v = rowVariable(comps[i].getType().getBagElementType());
    std::vector<Node> fromP, toP;
    for (size_t k = 0; k < w; k++)
    {
      fromP.push_back(
          datatypes::TupleUtils::nthElementOfTuple(r, starts[i] + k));
      toP.push_back(datatypes::TupleUtils::nthElementOfTuple(v, k));
    }
    std::vector<Node> local;
    for (const Node& c : conjuncts)
    {
      std::set<uint32_t> pos;
      if (!readPositions(c, r, pos) || pos.empty())
      {
        continue;
      }
      bool inside = true;
      for (uint32_t q : pos)
      {
        inside = inside && q >= starts[i] && q < starts[i] + w;
      }
      if (inside)
      {
        local.push_back(
            c.substitute(fromP.begin(), fromP.end(), toP.begin(), toP.end()));
      }
    }
    // the component filtered by those conjuncts, whose element conditions are
    // read off
    Node C = comps[i];
    if (!local.empty())
    {
      Node body = local.size() == 1 ? local[0] : d_nm->mkNode(Kind::AND, local);
      C = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(v, body), C);
    }
    Node u = rowVariable(comps[i].getType().getBagElementType());
    std::set<Node> conds;
    elementConditions(C, u, conds);
    for (const Node& c : conds)
    {
      std::set<uint32_t> pos;
      if (!readPositions(c, u, pos) || pos.size() != 1)
      {
        continue;
      }
      uint32_t k = *pos.begin();
      uint32_t g = starts[i] + k;
      uint32_t first = find(g);
      if (first == g)
      {
        bool others = false;
        for (uint32_t q = 0; q < width && !others; q++)
        {
          others = q != g && find(q) == g;
        }
        if (!others)
        {
          continue;
        }
      }
      // the condition on the class's first column, unless P has it or the
      // first column's own component does: (> ((_ tuple.select 0) u) 3)
      // becomes (> ((_ tuple.select 0) t) 3) for u's column 0 at column 2
      Node fromCol = datatypes::TupleUtils::nthElementOfTuple(u, k);
      Node toCol = datatypes::TupleUtils::nthElementOfTuple(r, first);
      Node c2 = d_rewriter->rewrite(c.substitute(TNode(fromCol), TNode(toCol)));
      if (occursFree(c2, u) || present.count(c2) || c2.isConst())
      {
        continue;
      }
      size_t j = compOf(first);
      if (j == i && first == g)
      {
        continue;
      }
      // nor one the rows of the product satisfy anyway, which would go again
      if (dropKnownMemberships(c2, r, n[1]).isConst())
      {
        continue;
      }
      // nor a null test that NOT_NULL_COLUMNS decides on the rows of the
      // product: (nullable.is_some ((_ tuple.select 0) t)) for a column 0
      // that is never null would go again, see assumeNonNull
      if (assumeNonNull(c2, r, nonNullColumns(n[1])) != c2)
      {
        continue;
      }
      present.insert(c2);
      added.push_back(c2);
    }
  }
  if (added.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  conjuncts.insert(conjuncts.end(), added.begin(), added.end());
  Node body = d_nm->mkNode(Kind::AND, conjuncts);
  Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, body), n[1]);
  return BagsRewriteResponse(ret, Rewrite::FILTER_JOIN_TRANSITIVE);
}

// For a filter predicate P over the rows of a product of the components
// comps, those of comps[c] starting at column starts[c]: which components are
// reached. An aggregate ((_ table.aggr K) f i X) of an empty X is one row of
// initial values i; a component is reached when no row that passes P has
// that row in the component's columns, only groups of rows of its input. The
// result holds per component
// - 1 when P tests the aggregate's counter column, which counts the rows of
//   each group by (+ ((_ tuple.select c) acc) 1) from 0, to be at least 1;
//   test[c] is then the index of that conjunct of P (and -1 when there is
//   none);
// - 2 when P equates the copy of each group column in the aggregate's rows
//   with the copy of the matching group column of a reached aggregate, and
//   the inputs of the two have one set of group values;
// - 0 otherwise, also for an aggregate that does not copy all its group
//   columns to its rows.
// For X : (Bag (Tuple Int Int)),
// G1 = ((_ table.aggr 0) f i X) and G2 = ((_ table.aggr 0) g j X), each with
// rows of three columns that copy group column 0 to column 0 and count the
// rows of the group in column 2, and
//   P = (lambda ((t (Tuple Int Int Int Int Int Int)))
//         (and (>= ((_ tuple.select 2) t) 1)
//              (= ((_ tuple.select 0) t) ((_ tuple.select 3) t))))
// over (table.product G1 G2), with starts {0, 3}, the result is {1, 2} and
// test is {0, -1}: G1's count is tested, and every group of G2 that a reached
// group of G1 meets has a row of X, with the same group values as that group.
std::vector<int> BagsRewriter::reachedComponents(
    const Node& P,
    const std::vector<Node>& comps,
    const std::vector<size_t>& starts,
    std::vector<int>& test) const
{
  std::vector<int> reached(comps.size(), 0);
  test.assign(comps.size(), -1);
  // nothing is reached unless P is a lambda of one variable r, and without
  // the rewriter, which keySet below needs
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || d_rewriter == nullptr)
  {
    return reached;
  }
  Node r = lambda[0][0];
  // the conjuncts of P's body, or the body itself when it is not an and
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  // First the components reached by a test of their counter (1). Only an
  // aggregate A = ((_ table.aggr K) f i X) whose step f is a lambda of a row
  // t and an accumulator acc, with a tuple as its body, is considered.
  std::vector<std::map<uint32_t, size_t>> keyAt(comps.size());
  std::vector<bool> keyed(comps.size(), false);
  for (size_t c = 0; c < comps.size(); c++)
  {
    const Node& A = comps[c];
    if (A.getKind() != Kind::TABLE_AGGREGATE)
    {
      continue;
    }
    Node f = asLambda(A[0]);
    if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
        || !isTupleTerm(f[1]))
    {
      continue;
    }
    // K, the group columns of A, are columns of X
    const std::vector<uint32_t>& K =
        A.getOperator().getConst<ProjectOp>().getIndices();
    for (size_t q = 0; q < f[1].getNumChildren(); q++)
    {
      const Node& e = f[1][q];
      if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == f[0][0])
      {
        uint32_t k = datatypes::utils::indexOf(e.getOperator());
        if (std::find(K.begin(), K.end(), k) != K.end() && !keyAt[c].count(k))
        {
          keyAt[c][k] = q;
        }
      }
    }
    // keyAt[c] maps each group column k to the first column q of A's rows
    // that copies it, the q-th component of f's tuple being
    // ((_ tuple.select k) t). keyed[c] holds when K is not empty and every
    // group column has such a copy; the other components are never reached.
    keyed[c] =
        !K.empty()
        && keyAt[c].size() == std::set<uint32_t>(K.begin(), K.end()).size();
    if (!keyed[c])
    {
      continue;
    }
    // A conjunct (>= ((_ tuple.select pos) r) 1) of P, with pos among the w
    // columns of component c, tests column pos - starts[c] of A's own rows.
    // local is that test as a predicate over A's rows, with the row variable
    // of their sort; counterColumn says whether that column counts the rows
    // of each group, by (+ ((_ tuple.select q) acc) 1) from 0. The row of
    // initial values has 0 in it and fails the test.
    Node row = rowVariable(A.getType().getBagElementType());
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      const Node& d = conjuncts[k];
      if (d.getKind() != Kind::GEQ || !d[1].isConst()
          || d[1].getConst<Rational>() != Rational(1)
          || d[0].getKind() != Kind::APPLY_SELECTOR || d[0][0] != r)
      {
        continue;
      }
      size_t pos = datatypes::utils::indexOf(d[0].getOperator());
      size_t w = A.getType().getBagElementType().getTupleLength();
      if (pos < starts[c] || pos >= starts[c] + w)
      {
        continue;
      }
      Node local = mkLambda(
          row,
          d_nm->mkNode(
              Kind::GEQ,
              datatypes::TupleUtils::nthElementOfTuple(row, pos - starts[c]),
              d_one));
      if (counterColumn(local, f, A[1]) == static_cast<int>(pos - starts[c]))
      {
        // with several such conjuncts, test[c] is the last one
        test[c] = static_cast<int>(k);
        reached[c] = 1;
      }
    }
  }
  // equated(a, b): whether a conjunct of P is
  // (= ((_ tuple.select a) r) ((_ tuple.select b) r)), either way round
  auto equated = [&](size_t a, size_t b) {
    for (const Node& e : conjuncts)
    {
      if (e.getKind() == Kind::EQUAL && e[0].getKind() == Kind::APPLY_SELECTOR
          && e[1].getKind() == Kind::APPLY_SELECTOR && e[0][0] == r
          && e[1][0] == r)
      {
        size_t x0 = datatypes::utils::indexOf(e[0].getOperator());
        size_t x1 = datatypes::utils::indexOf(e[1].getOperator());
        if ((x0 == a && x1 == b) || (x0 == b && x1 == a))
        {
          return true;
        }
      }
    }
    return false;
  };
  // keySet(c): the set of the values that the group columns K take in the
  // input X of the keyed component c, in the order of K, as a rewritten term,
  // cached in keySets. For group column 0 of X : (Bag (Tuple Int Int)), it
  // is the rewrite of
  //   (bag.setof
  //     (bag.map (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 0) s)))
  //              X))
  // Two components whose sets rewrite to one term have the same group
  // values, so the input of one is empty exactly when that of the other is.
  std::map<size_t, Node> keySets;
  auto keySet = [&](size_t c) {
    auto it = keySets.find(c);
    if (it != keySets.end())
    {
      return it->second;
    }
    const Node& A = comps[c];
    const std::vector<uint32_t>& K =
        A.getOperator().getConst<ProjectOp>().getIndices();
    Node X = A[2];
    Node xr = rowVariable(X.getType().getBagElementType());
    std::vector<Node> cols;
    std::vector<TypeNode> types;
    for (uint32_t k : K)
    {
      cols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, k));
      types.push_back(cols.back().getType());
    }
    TypeNode kt = d_nm->mkTupleType(types);
    Node m =
        d_nm->mkNode(Kind::BAG_MAP,
                     mkLambda(xr,
                              datatypes::TupleUtils::constructTupleFromElements(
                                  kt, cols, 0, cols.size() - 1)),
                     X);
    Node ks = d_rewriter->rewrite(d_nm->mkNode(Kind::BAG_SETOF, m));
    keySets[c] = ks;
    return ks;
  };
  // Then the components reached through a join (2): a keyed component j with
  // a reached keyed component i such that both have as many group columns,
  // P equates the copy of the m-th group column of i with that of j, for
  // every m, and keySet(i) and keySet(j) are one term. In a row that passes
  // P, i's columns hold a group of rows of i's input, so that input is not
  // empty, nor is j's, and j has no row of initial values. A component
  // marked 2 may let another one be reached, so this repeats until nothing
  // changes.
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (size_t j = 0; j < comps.size(); j++)
    {
      if (reached[j] || !keyed[j])
      {
        continue;
      }
      for (size_t i = 0; i < comps.size() && !reached[j]; i++)
      {
        if (i == j || !reached[i] || !keyed[i])
        {
          continue;
        }
        const std::vector<uint32_t>& Ki =
            comps[i].getOperator().getConst<ProjectOp>().getIndices();
        const std::vector<uint32_t>& Kj =
            comps[j].getOperator().getConst<ProjectOp>().getIndices();
        if (Ki.size() != Kj.size())
        {
          continue;
        }
        bool joined = true;
        for (size_t m = 0; m < Ki.size() && joined; m++)
        {
          joined =
              equated(starts[i] + keyAt[i][Ki[m]], starts[j] + keyAt[j][Kj[m]]);
        }
        if (!joined)
        {
          continue;
        }
        Node keysI = keySet(i);
        Node keysJ = keySet(j);
        if (keysI == keysJ)
        {
          reached[j] = 2;
          changed = true;
        }
      }
    }
  }
  return reached;
}

BagsRewriteResponse BagsRewriter::dropImpliedCounters(const TNode& n) const
{
  // FILTER_IMPLIED_COUNTER: a filter over the product of two aggregates that
  // copy all their group columns, joined on them, over tables with the same key
  // values (see reachedComponents): the group of the second that a reached
  // group of the first meets is reached too, and the test of its counter goes
  // (see rewrites.h)
  Node P = asLambda(n[0]);
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> comps;
  std::vector<size_t> starts;
  {
    Node rest = n[1];
    size_t at = 0;
    while (true)
    {
      Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
      if (!c.getType().getBagElementType().isTuple())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      comps.push_back(c);
      starts.push_back(at);
      at += c.getType().getBagElementType().getTupleLength();
      if (rest.getKind() != Kind::TABLE_PRODUCT)
      {
        break;
      }
      rest = rest[1];
    }
  }
  // one test at a time, from the last component: the first tested component
  // stays tested, a later one reached through it loses its test
  std::vector<int> test;
  std::vector<int> reached = reachedComponents(n[0], comps, starts, test);
  for (size_t j = comps.size(); j-- > 0;)
  {
    if (test[j] < 0)
    {
      continue;
    }
    // without j's test, is j still reached through another?
    std::vector<Node> conjuncts;
    if (P[1].getKind() == Kind::AND)
    {
      conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
    }
    else
    {
      conjuncts.push_back(P[1]);
    }
    std::vector<Node> kept;
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      if (static_cast<int>(k) != test[j])
      {
        kept.push_back(conjuncts[k]);
      }
    }
    if (kept.empty())
    {
      continue;
    }
    // P without the test of component j
    Node body = kept.size() == 1 ? kept[0] : d_nm->mkNode(Kind::AND, kept);
    Node P2 = mkLambda(P[0][0], body);
    std::vector<int> test2;
    std::vector<int> reached2 = reachedComponents(P2, comps, starts, test2);
    if (reached2[j])
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, P2, n[1]);
      return BagsRewriteResponse(ret, Rewrite::FILTER_IMPLIED_COUNTER);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteEquiJoinOfSets(const TNode& n) const
{
  // FILTER_EQUI_JOIN_SETS: a join of two sets X and Y of rows of one sort, on
  // all their columns, pairs each row of X with the one equal row of Y, if any:
  // the rows of the intersection, twice over (see rewrites.h). It is the shape
  // of SQL's INTERSECT, which the translator writes as bag.inter_min; X and Y
  // are sets, see isSet.
  Node P = asLambda(n[0]);
  Node X = n[1][0];
  Node Y = n[1][1];
  TypeNode xType = X.getType();
  TypeNode yType = Y.getType();
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || xType != yType || !xType.getBagElementType().isTuple() || !isSet(X)
      || !isSet(Y))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node t = P[0][0];
  size_t m = X.getType().getBagElementType().getTupleLength();
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  std::vector<bool> joined(m, false);
  std::vector<Node> rest;
  for (const Node& c : conjuncts)
  {
    bool used = false;
    if (c.getKind() == Kind::EQUAL && c[0].getKind() == Kind::APPLY_SELECTOR
        && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == t
        && c[1][0] == t)
    {
      size_t i = datatypes::utils::indexOf(c[0].getOperator());
      size_t j = datatypes::utils::indexOf(c[1].getOperator());
      size_t lo = std::min(i, j), hi = std::max(i, j);
      if (lo < m && hi == lo + m)
      {
        joined[lo] = true;
        used = true;
      }
    }
    if (!used)
    {
      rest.push_back(c);
    }
  }
  if (std::find(joined.begin(), joined.end(), false) != joined.end())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode wType = X.getType().getBagElementType();
  Node w = rowVariable(wType);
  std::vector<Node> cols;
  for (size_t k = 0; k < 2 * m; k++)
  {
    cols.push_back(datatypes::TupleUtils::nthElementOfTuple(w, k % m));
  }
  TypeNode rowType = n.getType().getBagElementType();
  // dup, the map that writes each row of the intersection twice over
  Node dup = mkLambda(w,
                      datatypes::TupleUtils::constructTupleFromElements(
                          rowType, cols, 0, cols.size() - 1));
  Node ret =
      d_nm->mkNode(Kind::BAG_MAP, dup, d_nm->mkNode(Kind::BAG_INTER_MIN, X, Y));
  if (!rest.empty())
  {
    Node q = rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::AND, rest);
    ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, q), ret);
  }
  return BagsRewriteResponse(ret, Rewrite::FILTER_EQUI_JOIN_SETS);
}

void BagsRewriter::elementConditions(const Node& A,
                                     const Node& w,
                                     std::set<Node>& out) const
{
  // conditions that every element w of A satisfies, read off the filters of A,
  // through projections onto distinct columns, and through the key columns of
  // the groups that the rows of an aggregate reached. For X : (Bag (Tuple Int
  // Int)) and
  //   A = (bag.map
  //         (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 1) s)))
  //         (bag.filter
  //           (lambda ((s (Tuple Int Int)))
  //             (and (> ((_ tuple.select 1) s) 3)
  //                  (< ((_ tuple.select 0) s) 7)))
  //           X))
  // out gets (> ((_ tuple.select 0) w) 3): the map keeps column 1 of the rows,
  // as column 0 of w, and drops column 0, of which nothing is said
  switch (A.getKind())
  {
    case Kind::BAG_SETOF: elementConditions(A[0], w, out); return;
    case Kind::BAG_INTER_MIN:
      elementConditions(A[0], w, out);
      elementConditions(A[1], w, out);
      return;
    case Kind::BAG_FILTER:
    {
      Node p = asLambda(A[0]);
      if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1
          && !bindsVariable(p[1], p[0][0]))
      {
        Node body = p[1].substitute(TNode(p[0][0]), TNode(w));
        if (body.getKind() == Kind::AND)
        {
          out.insert(body.begin(), body.end());
        }
        else
        {
          out.insert(body);
        }
      }
      if (A[1].getKind() == Kind::TABLE_AGGREGATE
          && counterColumn(A[0], asLambda(A[1][0]), A[1][1]) >= 0)
      {
        // a reached group's key columns hold values of its rows: with
        // column q of f's result the group column ((_ tuple.select 0) t), a
        // condition (> ((_ tuple.select 0) v) 3) of the rows of the input is
        // (> ((_ tuple.select q) w) 3)
        Node G = A[1];
        Node f = asLambda(G[0]);
        const std::vector<uint32_t>& K =
            G.getOperator().getConst<ProjectOp>().getIndices();
        if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2
            && isTupleTerm(f[1]))
        {
          Node v = rowVariable(G[2].getType().getBagElementType());
          std::set<Node> inner;
          elementConditions(G[2], v, inner);
          std::map<uint32_t, size_t> at;
          for (size_t q = 0; q < f[1].getNumChildren(); q++)
          {
            const Node& e = f[1][q];
            if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == f[0][0])
            {
              uint32_t k = datatypes::utils::indexOf(e.getOperator());
              if (std::find(K.begin(), K.end(), k) != K.end() && !at.count(k))
              {
                at[k] = q;
              }
            }
          }
          for (const Node& c : inner)
          {
            std::set<uint32_t> pos;
            if (!readPositions(c, v, pos) || pos.empty())
            {
              continue;
            }
            std::vector<Node> from, to;
            bool keysOnly = true;
            for (uint32_t k : pos)
            {
              keysOnly = keysOnly && at.count(k) > 0;
              if (keysOnly)
              {
                from.push_back(datatypes::TupleUtils::nthElementOfTuple(v, k));
                to.push_back(
                    datatypes::TupleUtils::nthElementOfTuple(w, at[k]));
              }
            }
            if (keysOnly)
            {
              Node cw =
                  c.substitute(from.begin(), from.end(), to.begin(), to.end());
              if (!occursFree(cw, v))
              {
                out.insert(cw);
              }
            }
          }
        }
        return;
      }
      elementConditions(A[1], w, out);
      return;
    }
    case Kind::BAG_MAP:
    {
      Node g = asLambda(A[0]);
      std::vector<uint32_t> J = projectionIndices(g);
      std::set<uint32_t> distinct(J.begin(), J.end());
      Node Y = A[1];
      if (J.empty() || distinct.size() != J.size()
          || !Y.getType().getBagElementType().isTuple())
      {
        return;
      }
      Node v = rowVariable(Y.getType().getBagElementType());
      std::set<Node> inner;
      elementConditions(Y, v, inner);
      std::vector<Node> from, to;
      for (size_t k = 0; k < J.size(); k++)
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(v, J[k]));
        to.push_back(datatypes::TupleUtils::nthElementOfTuple(w, k));
      }
      for (const Node& c : inner)
      {
        std::set<uint32_t> pos;
        if (!readPositions(c, v, pos) || pos.empty())
        {
          continue;
        }
        bool projected = true;
        for (uint32_t q : pos)
        {
          projected = projected && distinct.count(q) > 0;
        }
        if (projected)
        {
          Node cw =
              c.substitute(from.begin(), from.end(), to.begin(), to.end());
          if (!occursFree(cw, v))
          {
            out.insert(cw);
          }
        }
      }
      return;
    }
    default: return;
  }
}

BagsRewriteResponse BagsRewriter::postRewriteAll(TNode n)
{
  Assert(n.getKind() == Kind::BAG_ALL);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.all p (as bag.empty (Bag T)) = true)
      return BagsRewriteResponse(nm->mkConst(true), Rewrite::ALL_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.all p (bag x n)) = (or (p x) (<= n 0)
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::LEQ, n[1][1], d_zero);
      Node ret = px.orNode(leq);
      return BagsRewriteResponse(ret, Rewrite::ALL_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.all p (bag.union_disjoint A B)) =
      //   (and (bag.all p A) (bag.all p B))
      Node a = nm->mkNode(Kind::BAG_ALL, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_ALL, n[0], n[1][1]);
      Node ret = a.andNode(b);
      return BagsRewriteResponse(ret, Rewrite::ALL_UNION_DISJOINT);
    }
    default:
    {
      // (bag.all p A) is rewritten as (bag.filter p A) = A
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node all = filter.eqNode(n[1]);
      return BagsRewriteResponse(all, Rewrite::ALL_FILTER);
    }
  }
}

BagsRewriteResponse BagsRewriter::postRewriteSome(TNode n)
{
  Assert(n.getKind() == Kind::BAG_SOME);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.some p (as bag.empty (Set T)) = false)
      return BagsRewriteResponse(nm->mkConst(false), Rewrite::SOME_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.some p (bag x n)) = (and (> n 0) (p x))
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::GT, n[1][1], d_zero);
      Node ret = px.andNode(leq);
      return BagsRewriteResponse(ret, Rewrite::SOME_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.some p (bag.union_disjoint A B)) =
      //   (or (bag.some p A) (bag.union_disjoint p B))
      Node a = nm->mkNode(Kind::BAG_SOME, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_SOME, n[0], n[1][1]);
      Node ret = a.orNode(b);
      return BagsRewriteResponse(ret, Rewrite::SOME_UNION_DISJOINT);
    }
    default:
    {
      // (bag.some p A) is rewritten as (distinct (bag.filter p A) bag.empty))
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node empty = nm->mkConst(EmptyBag(n[1].getType()));
      Node some = filter.eqNode(empty).notNode();
      return BagsRewriteResponse(some, Rewrite::SOME_FILTER);
    }
  }
}

// The rules for (bag.fold f t X), the step f folded over the rows of X from
// the initial value t (X is bag in the code), tried in this order; the first
// that applies returns:
// - FOLD_CONST, for X a constant, and FOLD_BAG, for X = (bag x c) with c a
//   positive constant: the fold is evaluated or unrolled;
// - NOT_NULL_COLUMNS, for f a lambda of a row and an accumulator, over rows
//   of tuples (assumeNonNull);
// - FOLD_TUPLE (rewriteFoldOfTuple);
// - FOLD_CONSTANT_STEP;
// - FOLD_UNION_DISJOINT, for X a bag.union_disjoint;
// - CANONICAL_VARIABLE (canonicalLambda), for f a lambda node.
// Any other X, a (bag x c) with c not a constant among them, goes on past
// FOLD_BAG. For X : (Bag Int),
//   (bag.fold (lambda ((t Int) (acc Int)) 7) 0 X)
//   ---> (ite (= X (as bag.empty (Bag Int))) 0 7)        (FOLD_CONSTANT_STEP)
BagsRewriteResponse BagsRewriter::postRewriteFold(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  Node f = n[0];
  Node t = n[1];
  Node bag = n[2];
  if (bag.isConst())
  {
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  if (bag.getKind() == Kind::BAG_MAKE && bag[1].isConst()
      && bag[1].getConst<Rational>() > Rational(0))
  {
    // (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, n > 0
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_BAG);
  }
  {
    // l is f as a lambda, also when f is a function array constant (see
    // asLambda); its two variables are the row l[0][0] and the accumulator
    // l[0][1]
    Node l = asLambda(f);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2)
    {
      if (l[1] == l[0][1])
      {
        // FOLD_IDENTITY_STEP: a fold whose step keeps the accumulator is its
        // initial value (see rewrites.h)
        return BagsRewriteResponse(t, Rewrite::FOLD_IDENTITY_STEP);
      }
      if (bag.getKind() == Kind::BAG_FILTER
          && bag[1].getKind() == Kind::TABLE_PRODUCT
          && !l[1].getType().isTuple())
      {
        // FOLD_OVER_JOIN: a fold over a join is a fold over the join of the
        // aggregates of its sides, see eagerAggregation and rewrites.h.
        // eagerAggregation takes an aggregate step, over tuples, so f goes as a
        // step over tuples of one column that reads ((_ tuple.select 0) acc)
        // for the accumulator of f, from (tuple i). For COUNT(*), with
        //   f = (lambda ((t (Tuple Int Int Int)) (acc (Nullable Int)))
        //         (nullable.some (+ 1 (nullable.val acc))))
        // the step is
        //   f1 = (lambda ((t (Tuple Int Int Int)) (acc (Tuple (Nullable Int))))
        //          (tuple (nullable.some
        //                   (+ 1 (nullable.val ((_ tuple.select 0) acc))))))
        // from (tuple (nullable.some 0)), and the step f3 that eagerAggregation
        // gives back goes back over the accumulator of f the same way.
        Node a = l[0][1];
        TypeNode tt = d_nm->mkTupleType({a.getType()});
        Node acc = NodeManager::mkBoundVar("acc", tt);
        Node a0 = datatypes::TupleUtils::nthElementOfTuple(acc, 0);
        Node body = datatypes::TupleUtils::constructTupleFromElements(
            tt, {l[1].substitute(TNode(a), TNode(a0))}, 0, 0);
        Node f1 = d_nm->mkNode(Kind::LAMBDA,
                               d_nm->mkNode(Kind::BOUND_VAR_LIST, l[0][0], acc),
                               body);
        Node i1 =
            datatypes::TupleUtils::constructTupleFromElements(tt, {t}, 0, 0);
        Node e = eagerAggregation(f1, i1, bag, {});
        if (!e.isNull())
        {
          // f3 is a step over tuples of one column, with the body (tuple b3);
          // the step of the result is b3, with a3 for ((_ tuple.select 0) acc3)
          Node f3 = e[0];
          Node acc3 = f3[0][1];
          Node a3 = NodeManager::mkBoundVar("acc", a.getType());
          Node step = f3[1][0].substitute(
              TNode(datatypes::TupleUtils::nthElementOfTuple(acc3, 0)),
              TNode(a3));
          Node lambda =
              d_nm->mkNode(Kind::LAMBDA,
                           d_nm->mkNode(Kind::BOUND_VAR_LIST, f3[0][0], a3),
                           step);
          Node ret = d_nm->mkNode(Kind::BAG_FOLD, lambda, t, e[1]);
          return BagsRewriteResponse(ret, Rewrite::FOLD_OVER_JOIN);
        }
      }
      if (t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getNumChildren() == 1
          && t[0].isConst() && t[0].getConst<Rational>().isZero()
          && l[1].getKind() == Kind::APPLY_CONSTRUCTOR
          && l[1].getNumChildren() == 1 && l[1][0].getKind() == Kind::ADD
          && t.getType().isNullable())
      {
        // FOLD_SUM_FROM_ZERO: a sum from (nullable.some 0) of a term e that
        // does not read the accumulator is 0 over no row, and otherwise the sum
        // that skips nulls from null: one fold then stands for both SUM, from
        // null, and COALESCE(SUM, 0), from 0 (see rewrites.h)
        Node a = l[0][1];
        const DType& dt = t.getType().getDType();
        size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
        Node val =
            d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), a);
        std::vector<Node> rest;
        bool once = false;
        for (const Node& c : l[1][0])
        {
          if (c == val && !once)
          {
            once = true;
          }
          else
          {
            rest.push_back(c);
          }
        }
        Node e = rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::ADD, rest);
        // not a count, a sum of a constant, which stays a count from 0
        if (once && !rest.empty() && !occursFree(e, a) && !e.isConst())
        {
          // null is (as nullable.null (Nullable Int)), some is
          // (nullable.some e), step the step of S above
          Node null = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                   dt[1 - si].getConstructor());
          Node some =
              d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, dt[si].getConstructor(), e);
          Node step =
              d_nm->mkNode(Kind::ITE,
                           {null.eqNode(a),
                            some,
                            d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                         dt[si].getConstructor(),
                                         d_nm->mkNode(Kind::ADD, val, e))});
          Node S = d_nm->mkNode(Kind::BAG_FOLD,
                                d_nm->mkNode(Kind::LAMBDA, l[0], step),
                                null,
                                bag);
          Node ret = d_nm->mkNode(Kind::ITE, null.eqNode(S), t, S);
          return BagsRewriteResponse(ret, Rewrite::FOLD_SUM_FROM_ZERO);
        }
      }
      if (bag.getKind() == Kind::BAG_UNION_DISJOINT && t.getType().isNullable())
      {
        // FOLD_UNION_COMBINE: a sum, minimum or maximum that skips nulls from
        // null (see nullAwareStepKind), or a count from (nullable.some 0) (see
        // isCountStep), over a union: the two folds combined by the
        // operation, which does not depend on the order the fold visits the
        // rows in, unlike FOLD_UNION_DISJOINT below. For a sum f,
        //   (bag.fold f (as nullable.null (Nullable Int))
        //             (bag.union_disjoint A B))
        //   --->
        //   (ite (= (as nullable.null (Nullable Int)) a)
        //        b
        //        (ite (= (as nullable.null (Nullable Int)) b)
        //             a
        //             (nullable.some (+ (nullable.val a) (nullable.val b)))))
        // where a = (bag.fold f (as nullable.null (Nullable Int)) A) and b
        // the same over B; a minimum combines as
        // (ite (<= (nullable.val a) (nullable.val b)) a b), a maximum with >=,
        // and two counts from (nullable.some 0) as
        // (nullable.some (+ (nullable.val a) (nullable.val b))), without the
        // null tests. k is 0 for a sum, 1 for a minimum, 2 for a maximum and 3
        // for a count
        Node arg;
        int k = isNullConstant(t) ? nullAwareStepKind(l[1], l[0][1], arg) : -1;
        if (k < 0 && isCountStep(l[1], l[0][1], t))
        {
          k = 3;
        }
        if (k >= 0)
        {
          Node a = d_nm->mkNode(Kind::BAG_FOLD, f, t, bag[0]);
          Node b = d_nm->mkNode(Kind::BAG_FOLD, f, t, bag[1]);
          const DType& dt = t.getType().getDType();
          size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
          Node null = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                   dt[1 - si].getConstructor());
          Node va =
              d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), a);
          Node vb =
              d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), b);
          Node both;
          switch (k)
          {
            case 0:
            case 3:
              both = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                  dt[si].getConstructor(),
                                  d_nm->mkNode(Kind::ADD, va, vb));
              break;
            case 1:
              both = d_nm->mkNode(
                  Kind::ITE, d_nm->mkNode(Kind::LEQ, va, vb), a, b);
              break;
            default:
              both = d_nm->mkNode(
                  Kind::ITE, d_nm->mkNode(Kind::GEQ, va, vb), a, b);
              break;
          }
          Node ret =
              k == 3 ? both
                     : d_nm->mkNode(
                           Kind::ITE,
                           {null.eqNode(a),
                            b,
                            d_nm->mkNode(Kind::ITE, null.eqNode(b), a, both)});
          return BagsRewriteResponse(ret, Rewrite::FOLD_UNION_COMBINE);
        }
      }
      if (bag.getType().getBagElementType().isTuple())
      {
        // NOT_NULL_COLUMNS: in the step's body, the null tests of the columns
        // of the row that no row of X has null in (see nonNullColumns) are
        // decided, as (nullable.is_some ((_ tuple.select 1) t)) becomes true
        // for column 1 never null (see assumeNonNull). The new lambda keeps
        // f's variables, l[0].
        Node b = assumeNonNull(l[1], l[0][0], nonNullColumns(bag));
        if (b != l[1])
        {
          Node ret = d_nm->mkNode(
              Kind::BAG_FOLD, d_nm->mkNode(Kind::LAMBDA, l[0], b), t, bag);
          return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
        }
      }
      Node g = bag.getKind() == Kind::BAG_MAP ? asLambda(bag[0]) : Node::null();
      if (!g.isNull() && g.getKind() == Kind::LAMBDA
          && g[0].getNumChildren() == 1 && !bindsVariable(l[1], l[0][0]))
      {
        // FOLD_MAP: a fold over a map visits the image of y once per occurrence
        // of y in Y, so it is the fold over Y whose step reads the image for
        // its row, when the image does not read the accumulator variable
        // (see rewrites.h)
        Node y = g[0][0];
        Node body = l[1].substitute(TNode(l[0][0]), TNode(g[1]));
        // the map and Y are two bags, folded each in an order of its own: one
        // fold only for a step whose value no order changes
        if (!occursFree(g[1], l[0][1])
            && orderIndependentStep(l, {}, nonNullColumns(bag)))
        {
          Node lambda =
              d_nm->mkNode(Kind::LAMBDA,
                           d_nm->mkNode(Kind::BOUND_VAR_LIST, y, l[0][1]),
                           body);
          Node ret = d_nm->mkNode(Kind::BAG_FOLD, lambda, t, bag[1]);
          return BagsRewriteResponse(ret, Rewrite::FOLD_MAP);
        }
      }
    }
  }
  {
    // FOLD_TUPLE: a fold whose accumulator is a tuple, and whose step computes
    // each component from that component of the accumulator only, is the
    // tuple of the folds of the components (see rewriteFoldOfTuple, which
    // returns n when the rule does not apply)
    BagsRewriteResponse r = rewriteFoldOfTuple(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // FOLD_CONSTANT_STEP: a step c that reads neither the row nor the
    // accumulator gives c after any row, and the fold of no row is the
    // initial value t, so the fold is (ite (= X (as bag.empty ..)) t c)
    Node lambda = asLambda(f);
    if (lambda.getKind() == Kind::LAMBDA && lambda[0].getNumChildren() == 2
        && !occursFree(lambda[1], lambda[0][0])
        && !occursFree(lambda[1], lambda[0][1]))
    {
      Node empty = d_nm->mkConst(EmptyBag(bag.getType()));
      Node ret = d_nm->mkNode(Kind::ITE, bag.eqNode(empty), t, lambda[1]);
      return BagsRewriteResponse(ret, Rewrite::FOLD_CONSTANT_STEP);
    }
  }
  if (bag.getKind() == Kind::BAG_UNION_DISJOINT)
  {
    // (bag.fold f t (bag.union_disjoint A B)) =
    //       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
    Node A = bag[0] < bag[1] ? bag[0] : bag[1];
    Node B = bag[0] < bag[1] ? bag[1] : bag[0];
    Node foldA = d_nm->mkNode(Kind::BAG_FOLD, f, t, A);
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, f, foldA, B);
    return BagsRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
  }
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N
    // the id of f's alpha key, a node that is the same for lambdas that differ
    // only in the names of their variables (see canonicalLambda)
    Node canonical = canonicalLambda(f);
    if (canonical != f)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FOLD, canonical, t, bag);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewritePartition(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_PARTITION);
  if (n[1].isConst())
  {
    Node ret = BagsUtils::evaluateBagPartition(d_rewriter, n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::PARTITION_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateIntegerSum(
    const TNode& n) const
{
  // AGGREGATE_INTEGER_SUM: ((_ table.aggr K) f i X) where f's column j is a
  // sum, seeded with null, of reals that are integers read as reals: the sum
  // of the integers, read as a real once, so that the sum of the integers
  // read as reals and the integer sum read as a real are one term. With
  // column 1 of X an (Nullable Int) and column 1 of f the null-aware sum
  // (see nullAwareStepKind) of
  //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) t))
  //        (as nullable.null (Nullable Real))
  //        (nullable.some (to_real (nullable.val ((_ tuple.select 1) t)))))
  // from (as nullable.null (Nullable Real)),
  //   ((_ table.aggr 0) f i X)
  //   --->
  //   (bag.map (lambda ((r (Tuple Int (Nullable Int))))
  //              (tuple ((_ tuple.select 0) r)
  //                     (ite (= (as nullable.null (Nullable Int))
  //                             ((_ tuple.select 1) r))
  //                          (as nullable.null (Nullable Real))
  //                          (nullable.some
  //                            (to_real (nullable.val
  //                                       ((_ tuple.select 1) r)))))))
  //            ((_ table.aggr 0) f' i' X))
  // where column 1 of f' is the null-aware sum of ((_ tuple.select 1) t)
  // itself, from (as nullable.null (Nullable Int)), and i' is i with that
  // seed; the other columns of f' are those of f over the new accumulator
  Node f = asLambda(n[0]);
  Node init = n[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(init)
      || init.getNumChildren() != f[1].getNumChildren()
      || d_rewriter == nullptr)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  TypeNode accType = acc.getType();
  for (size_t j = 0; j < w; j++)
  {
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, j);
    TypeNode t = own.getType();
    if (!t.isNullable() || !t.getNullableElementType().isReal()
        || t.getNullableElementType().isInteger() || !isNullConstant(init[j]))
    {
      continue;
    }
    Node A;
    if (nullAwareStepKind(f[1][j], own, A) != 0)
    {
      continue;
    }
    // the integer A reads as a real: (nullable.some (to_real e)), or the
    // nullable lift
    //   (ite (= (as nullable.null (Nullable Int)) y)
    //        (as nullable.null (Nullable Real))
    //        (nullable.some (to_real (nullable.val y))))
    // intArg is (nullable.some e), or y
    Node intArg;
    if (A.getKind() == Kind::APPLY_CONSTRUCTOR && A.getNumChildren() == 1
        && A[0].getKind() == Kind::TO_REAL && A[0][0].getType().isInteger())
    {
      TypeNode ni = d_nm->mkNullableType(A[0][0].getType());
      intArg =
          d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                       ni.getDType()[ni.getDType()[0].getNumArgs() == 1 ? 0 : 1]
                           .getConstructor(),
                       A[0][0]);
    }
    else if (A.getKind() == Kind::ITE && isNullConstant(A[1])
             && A[0].getKind() == Kind::EQUAL)
    {
      for (size_t sd = 0; sd < 2 && intArg.isNull(); sd++)
      {
        Node y = A[0][1 - sd];
        if (isNullConstant(A[0][sd]) && y.getType().isNullable()
            && y.getType().getNullableElementType().isInteger()
            && A[2].getKind() == Kind::APPLY_CONSTRUCTOR
            && A[2].getNumChildren() == 1 && A[2][0].getKind() == Kind::TO_REAL
            && A[2][0][0].getKind() == Kind::APPLY_SELECTOR
            && A[2][0][0][0] == y)
        {
          intArg = y;
        }
      }
    }
    if (intArg.isNull())
    {
      continue;
    }
    // no other column reads column j of the accumulator
    bool readElsewhere = false;
    for (size_t k = 0; k < w && !readElsewhere; k++)
    {
      readElsewhere = k != j && expr::hasSubterm(f[1][k], own);
    }
    if (readElsewhere || occursFree(intArg, acc))
    {
      continue;
    }
    std::vector<TypeNode> types = accType.getTupleTypes();
    types[j] = intArg.getType();
    TypeNode accType2 = d_nm->mkTupleType(types);
    Node acc2 = d_nm->mkBoundVar("acc", accType2);
    std::vector<Node> from, to;
    for (size_t k = 0; k < w; k++)
    {
      if (k != j)
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, k));
        to.push_back(datatypes::TupleUtils::nthElementOfTuple(acc2, k));
      }
    }
    std::vector<Node> cells, seeds;
    for (size_t k = 0; k < w; k++)
    {
      if (k != j)
      {
        cells.push_back(
            f[1][k].substitute(from.begin(), from.end(), to.begin(), to.end()));
        seeds.push_back(init[k]);
        continue;
      }
      // the null-aware sum of the integers, with a = ((_ tuple.select j) acc2)
      // and y the integer argument intArg,
      //   (ite (= (as nullable.null (Nullable Int)) y)
      //        a
      //        (ite (= (as nullable.null (Nullable Int)) a)
      //             y
      //             (nullable.some (+ (nullable.val a) (nullable.val y)))))
      Node own2 = datatypes::TupleUtils::nthElementOfTuple(acc2, j);
      const DType& dt = types[j].getDType();
      size_t someIndex = dt[0].getNumArgs() == 1 ? 0 : 1;
      Node null = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                               dt[1 - someIndex].getConstructor());
      Node val = d_nm->mkNode(
          Kind::APPLY_SELECTOR, dt[someIndex][0].getSelector(), own2);
      Node valArg = d_nm->mkNode(
          Kind::APPLY_SELECTOR, dt[someIndex][0].getSelector(), intArg);
      Node sum = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                              dt[someIndex].getConstructor(),
                              d_nm->mkNode(Kind::ADD, val, valArg));
      Node seeded = d_nm->mkNode(Kind::ITE, null.eqNode(own2), intArg, sum);
      Node step = d_nm->mkNode(Kind::ITE, null.eqNode(intArg), own2, seeded);
      cells.push_back(d_rewriter->rewrite(step));
      seeds.push_back(null);
    }
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType2, cells, 0, w - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType2, seeds, 0, w - 1);
    Node f2 = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
    std::vector<Node> children{n.getOperator(), f2, seed, n[2]};
    Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    // read column j as a real again, the map of the example above
    Node r = rowVariable(accType2);
    std::vector<Node> out;
    for (size_t k = 0; k < w; k++)
    {
      Node c = datatypes::TupleUtils::nthElementOfTuple(r, k);
      if (k == j)
      {
        const DType& dr = t.getDType();
        size_t si = dr[0].getNumArgs() == 1 ? 0 : 1;
        const DType& di = types[j].getDType();
        size_t sj = di[0].getNumArgs() == 1 ? 0 : 1;
        Node rnull =
            d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, dr[1 - si].getConstructor());
        Node inull =
            d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, di[1 - sj].getConstructor());
        Node v = d_nm->mkNode(Kind::APPLY_SELECTOR, di[sj][0].getSelector(), c);
        Node some = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                 dr[si].getConstructor(),
                                 d_nm->mkNode(Kind::TO_REAL, v));
        c = d_nm->mkNode(Kind::ITE, inull.eqNode(c), rnull, some);
      }
      out.push_back(c);
    }
    Node back = mkLambda(r,
                         datatypes::TupleUtils::constructTupleFromElements(
                             accType, out, 0, w - 1));
    Node ret = d_nm->mkNode(Kind::BAG_MAP, back, aggr);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_INTEGER_SUM);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateUnionSplit(
    const TNode& top) const
{
  // AGGREGATE_UNION_SPLIT, for
  // (bag.map h (bag.filter Q ((_ table.aggr K) f i (bag.union_disjoint U1 ..
  // Um)))) where every column of f other than the copies of the group columns
  // and the counter folds an argument column, skipping its nulls, that is null
  // on every row of all parts but one, and every part has the same group keys:
  // each group folds each column over the rows of one part, so the rows are
  // those of the aggregates of the parts, one per part, joined on the keys
  // (see rewrites.h). Q reads the counter only through (>= c 1) and h not at
  // all: with the same keys in every part, the counter of the first part is
  // positive exactly when theirs are, and stands for it. This is SQL's
  //   SELECT k, SUM(a), SUM(b) FROM (SELECT k, a, NULL AS b FROM X
  //     UNION ALL SELECT k, NULL, b FROM Y) GROUP BY k
  // with two parts, each giving the argument of one sum and null for the other.
  Node h = asLambda(top[0]);
  if (top[1].getKind() != Kind::BAG_FILTER || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1
      || top[1][1].getKind() != Kind::TABLE_AGGREGATE)
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  Node Q = asLambda(top[1][0]);
  Node n = top[1][1];
  Node f = asLambda(n[0]);
  Node init = n[1];
  int co = counterColumn(top[1][0], f, init);
  if (co < 0 || Q.getKind() != Kind::LAMBDA || Q[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  {
    std::set<uint32_t> read;
    if (!readPositions(h[1], h[0][0], read) || read.count(co))
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
    Node r = Q[0][0];
    std::vector<Node> conjuncts;
    if (Q[1].getKind() == Kind::AND)
    {
      conjuncts.insert(conjuncts.end(), Q[1].begin(), Q[1].end());
    }
    else
    {
      conjuncts.push_back(Q[1]);
    }
    for (const Node& c : conjuncts)
    {
      std::set<uint32_t> pos;
      bool counter = c.getKind() == Kind::GEQ
                     && c[0].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
                     && datatypes::utils::indexOf(c[0].getOperator())
                            == static_cast<size_t>(co);
      if (!counter && (!readPositions(c, r, pos) || pos.count(co)))
      {
        return BagsRewriteResponse(top, Rewrite::NONE);
      }
    }
  }
  if (n[2].getKind() != Kind::BAG_UNION_DISJOINT || f.getKind() != Kind::LAMBDA
      || f[0].getNumChildren() != 2 || !isTupleTerm(f[1]) || !isTupleTerm(init)
      || d_rewriter == nullptr)
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      n.getOperator().getConst<ProjectOp>().getIndices();
  if (K.empty())
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  std::vector<Node> parts;
  {
    std::vector<Node> todo{n[2]};
    while (!todo.empty())
    {
      Node c = todo.back();
      todo.pop_back();
      if (c.getKind() == Kind::BAG_UNION_DISJOINT)
      {
        todo.push_back(c[1]);
        todo.push_back(c[0]);
      }
      else
      {
        parts.push_back(c);
      }
    }
  }
  // the columns each part has null on every row: those its map makes
  // (as nullable.null (Nullable Int))
  std::vector<std::set<uint32_t>> nullCols(parts.size());
  for (size_t m = 0; m < parts.size(); m++)
  {
    Node g = parts[m].getKind() == Kind::BAG_MAP ? asLambda(parts[m][0])
                                                 : Node::null();
    if (!g.isNull() && g.getKind() == Kind::LAMBDA && isTupleTerm(g[1]))
    {
      for (size_t c = 0; c < g[1].getNumChildren(); c++)
      {
        if (isNullConstant(g[1][c]))
        {
          nullCols[m].insert(c);
        }
      }
    }
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  std::set<uint32_t> keys(K.begin(), K.end());
  // per column: -2 a key copy, -3 the counter, -1 no part, -4 several parts
  // (combined by kind[q]: a sum, minimum, maximum or count), or the one part
  std::vector<int> owner(w, -1);
  std::vector<std::vector<size_t>> owners(w);
  std::vector<int> kind(w, -1);
  for (size_t q = 0; q < w; q++)
  {
    Node e = f[1][q];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
    if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == x
        && keys.count(datatypes::utils::indexOf(e.getOperator())))
    {
      owner[q] = -2;
      continue;
    }
    if (e.getKind() == Kind::ADD && e.getNumChildren() == 2
        && ((e[0] == own && e[1] == d_one) || (e[1] == own && e[0] == d_one))
        && init[q].isConst() && init[q].getConst<Rational>().isZero())
    {
      owner[q] = -3;
      continue;
    }
    std::set<uint32_t> accRead;
    if (!readPositions(e, acc, accRead) || accRead.size() > 1
        || (accRead.size() == 1 && !accRead.count(q)))
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
    // the argument columns the step skips a row for, when one is null (none
    // for COUNT(*))
    std::set<uint32_t> argCols;
    Node arg;
    int k = isNullConstant(init[q]) ? nullAwareStepKind(e, own, arg) : -1;
    if (k >= 0 && arg.getKind() == Kind::APPLY_SELECTOR && arg[0] == x)
    {
      argCols.insert(datatypes::utils::indexOf(arg.getOperator()));
    }
    else if (isCountStep(e, own, init[q]))
    {
      k = 3;
      if (e.getKind() == Kind::ITE && e[1] == own)
      {
        // (= (as nullable.null (Nullable Int)) ((_ tuple.select c) x)), or
        // an or of those: COUNT(c, ..)
        std::vector<Node> tests;
        if (e[0].getKind() == Kind::OR)
        {
          tests.insert(tests.end(), e[0].begin(), e[0].end());
        }
        else
        {
          tests.push_back(e[0]);
        }
        for (const Node& t : tests)
        {
          bool ok = false;
          for (size_t sd = 0; t.getKind() == Kind::EQUAL && sd < 2 && !ok; sd++)
          {
            if (isNullConstant(t[sd])
                && t[1 - sd].getKind() == Kind::APPLY_SELECTOR
                && t[1 - sd][0] == x)
            {
              argCols.insert(
                  datatypes::utils::indexOf(t[1 - sd].getOperator()));
              ok = true;
            }
          }
          if (!ok)
          {
            return BagsRewriteResponse(top, Rewrite::NONE);
          }
        }
      }
      else if (e.getKind() == Kind::ITE)
      {
        return BagsRewriteResponse(top, Rewrite::NONE);
      }
    }
    else
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
    std::set<uint32_t> read;
    if (!readPositions(e, x, read)
        || (argCols.empty() ? read.size() > 1 : read != argCols))
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
    kind[q] = k;
    for (size_t m = 0; m < parts.size(); m++)
    {
      bool skipped = false;
      for (uint32_t c : argCols)
      {
        skipped = skipped || nullCols[m].count(c) > 0;
      }
      if (skipped)
      {
        continue;
      }
      owners[q].push_back(m);
    }
    owner[q] = owners[q].empty()       ? -1
               : owners[q].size() == 1 ? static_cast<int>(owners[q][0])
                                       : -4;
  }
  // the parts own columns, and have the same keys: the sets of their key
  // columns, the bag.setof of their projections onto them, are one term after
  // rewriting
  {
    std::set<size_t> used;
    for (size_t q = 0; q < w; q++)
    {
      used.insert(owners[q].begin(), owners[q].end());
    }
    if (used.size() < 2)
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
  }
  TypeNode uType = n[2].getType().getBagElementType();
  std::vector<TypeNode> uTypes = uType.getTupleTypes();
  Node ur = rowVariable(uType);
  std::vector<Node> kcols;
  std::vector<TypeNode> ktypes;
  for (uint32_t k : K)
  {
    kcols.push_back(datatypes::TupleUtils::nthElementOfTuple(ur, k));
    ktypes.push_back(uTypes[k]);
  }
  TypeNode kType = d_nm->mkTupleType(ktypes);
  Node keyMap = mkLambda(ur,
                         datatypes::TupleUtils::constructTupleFromElements(
                             kType, kcols, 0, kcols.size() - 1));
  Node keySet;
  for (const Node& u : parts)
  {
    Node ks = d_rewriter->rewrite(
        d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, keyMap, u)));
    if (keySet.isNull())
    {
      keySet = ks;
    }
    else if (ks != keySet)
    {
      return BagsRewriteResponse(top, Rewrite::NONE);
    }
  }
  // one aggregate per part: the key copies, its columns, a counter; at[m][q]
  // is the column of part m's aggregate that holds column q of f, and
  // counterAt[m] the column of its counter
  std::vector<Node> aggs;
  std::vector<std::vector<int>> at(parts.size(), std::vector<int>(w, -1));
  std::vector<size_t> counterAt(parts.size(), 0);
  for (size_t m = 0; m < parts.size(); m++)
  {
    std::vector<size_t> cols;
    for (size_t q = 0; q < w; q++)
    {
      if (owner[q] == -2
          || std::find(owners[q].begin(), owners[q].end(), m)
                 != owners[q].end())
      {
        cols.push_back(q);
      }
    }
    std::vector<TypeNode> types;
    for (size_t q : cols)
    {
      types.push_back(f[1][q].getType());
    }
    types.push_back(d_nm->integerType());
    TypeNode accType = d_nm->mkTupleType(types);
    Node acc2 = NodeManager::mkBoundVar("acc", accType);
    std::vector<Node> cells, seeds;
    for (size_t c = 0; c < cols.size(); c++)
    {
      size_t q = cols[c];
      at[m][q] = static_cast<int>(c);
      Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
      Node own2 = datatypes::TupleUtils::nthElementOfTuple(acc2, c);
      cells.push_back(f[1][q].substitute(TNode(own), TNode(own2)));
      seeds.push_back(init[q]);
    }
    // the counter, (+ ((_ tuple.select c) acc2) 1) from 0
    counterAt[m] = cols.size();
    cells.push_back(d_nm->mkNode(
        Kind::ADD,
        datatypes::TupleUtils::nthElementOfTuple(acc2, cols.size()),
        d_one));
    seeds.push_back(d_zero);
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType, cells, 0, cells.size() - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType, seeds, 0, seeds.size() - 1);
    Node fm = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
    std::vector<Node> children{n.getOperator(), fm, seed, parts[m]};
    // a keyed part's aggregate is its reached groups' rows, AGGREGATE_KEYED
    // (see keyedAggregateRows): when a part has no row, no part has (they have
    // the same keys), and the joined row of initial values that the
    // aggregates would give has counter 0, which Q drops
    Node partAggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    Node rows = keyedAggregateRows(partAggr);
    aggs.push_back(rows.isNull() ? partAggr : rows);
  }
  // (table.product A1 (table.product A2 ..)), joined on the key copies:
  // (= ((_ tuple.select 0) p) ((_ tuple.select 3) p)) in the example
  Node product = aggs.back();
  for (size_t k = aggs.size() - 1; k-- > 0;)
  {
    product = d_nm->mkNode(Kind::TABLE_PRODUCT, aggs[k], product);
  }
  std::vector<size_t> start(aggs.size(), 0);
  for (size_t m = 1; m < aggs.size(); m++)
  {
    start[m] = start[m - 1]
               + aggs[m - 1].getType().getBagElementType().getTupleLength();
  }
  Node pr = rowVariable(product.getType().getBagElementType());
  std::vector<Node> equal;
  for (size_t q = 0; q < w; q++)
  {
    if (owner[q] != -2)
    {
      continue;
    }
    for (size_t m = 1; m < aggs.size(); m++)
    {
      equal.push_back(
          datatypes::TupleUtils::nthElementOfTuple(pr, start[0] + at[0][q])
              .eqNode(datatypes::TupleUtils::nthElementOfTuple(
                  pr, start[m] + at[m][q])));
    }
  }
  Node cond =
      equal.empty()
          ? d_nm->mkConst(true)
          : (equal.size() == 1 ? equal[0] : d_nm->mkNode(Kind::AND, equal));
  Node joined = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(pr, cond), product);
  std::vector<Node> cells;
  for (size_t q = 0; q < w; q++)
  {
    if (owner[q] == -2)
    {
      cells.push_back(
          datatypes::TupleUtils::nthElementOfTuple(pr, start[0] + at[0][q]));
    }
    else if (owner[q] == -3)
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(
          pr, start[0] + counterAt[0]));
    }
    else if (owner[q] >= 0)
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(
          pr, start[owner[q]] + at[owner[q]][q]));
    }
    else if (owner[q] == -4)
    {
      // the parts' values combined by the operation, skipping nulls: a sum, a
      // minimum or a maximum of the two, or the one that is not null
      TypeNode t = f[1][q].getType();
      const DType& dt = t.getDType();
      size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
      Node null =
          d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, dt[1 - si].getConstructor());
      auto val = [&](const Node& v) {
        return d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), v);
      };
      auto some = [&](const Node& v) {
        return d_nm->mkNode(
            Kind::APPLY_CONSTRUCTOR, dt[si].getConstructor(), v);
      };
      Node c;
      for (size_t m : owners[q])
      {
        Node v =
            datatypes::TupleUtils::nthElementOfTuple(pr, start[m] + at[m][q]);
        if (c.isNull())
        {
          c = v;
          continue;
        }
        Node both;
        switch (kind[q])
        {
          case 0:
          case 3: both = some(d_nm->mkNode(Kind::ADD, {val(c), val(v)})); break;
          case 1:
            both = d_nm->mkNode(
                Kind::ITE, d_nm->mkNode(Kind::LEQ, {val(c), val(v)}), c, v);
            break;
          default:
            both = d_nm->mkNode(
                Kind::ITE, d_nm->mkNode(Kind::GEQ, {val(c), val(v)}), c, v);
            break;
        }
        c = kind[q] == 3
                ? both
                : d_nm->mkNode(
                      Kind::ITE,
                      {null.eqNode(c),
                       v,
                       d_nm->mkNode(Kind::ITE, null.eqNode(v), c, both)});
      }
      cells.push_back(c);
    }
    else
    {
      cells.push_back(init[q]);
    }
  }
  Node rows = d_nm->mkNode(
      Kind::BAG_MAP,
      mkLambda(pr,
               datatypes::TupleUtils::constructTupleFromElements(
                   n.getType().getBagElementType(), cells, 0, w - 1)),
      joined);
  Node ret = d_nm->mkNode(
      Kind::BAG_MAP, top[0], d_nm->mkNode(Kind::BAG_FILTER, top[1][0], rows));
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_UNION_SPLIT);
}

Node BagsRewriter::keysOfReachedGroups(const Node& h,
                                       const Node& F,
                                       bool covering) const
{
  // F =
  // (bag.filter (lambda ((r ..)) (>= ((_ tuple.select c) r) 1)) ((_ table.aggr
  // K) f i X)) with c the counter (see counterColumn), and h reading only
  // columns where f copies a group column ((_ tuple.select k) t): the rows that
  // h makes of the groups are those it makes of the rows of X, without repeats,
  // (bag.map h' X), to put under a bag.setof; null otherwise. h' is h with
  // column p of r read as column k of the rows s of X. With covering, h must
  // read all of K, so that distinct groups give distinct rows. With f copying
  // column 0 of X : (Bag (Tuple Int Int)) to its column 0 and counting the rows
  // in its column 2,
  //   h = (lambda ((r (Tuple Int Int Int))) (tuple ((_ tuple.select 0) r)))
  //   h' = (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 0) s)))
  if (h.getKind() != Kind::LAMBDA || h[0].getNumChildren() != 1
      || F.getKind() != Kind::BAG_FILTER
      || F[1].getKind() != Kind::TABLE_AGGREGATE)
  {
    return Node::null();
  }
  Node P = asLambda(F[0]);
  Node A = F[1];
  Node f = asLambda(A[0]);
  if (P.getKind() != Kind::LAMBDA || P[1].getKind() == Kind::AND
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || counterColumn(F[0], f, A[1]) < 0)
  {
    return Node::null();
  }
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  if (K.empty())
  {
    return Node::null();
  }
  std::set<uint32_t> read;
  if (!readPositions(h[1], h[0][0], read))
  {
    return Node::null();
  }
  Node X = A[2];
  Node xr = rowVariable(X.getType().getBagElementType());
  std::vector<Node> from, to;
  std::set<uint32_t> covered;
  for (uint32_t p : read)
  {
    const Node& e = f[1][p];
    if (e.getKind() != Kind::APPLY_SELECTOR || e[0] != f[0][0])
    {
      return Node::null();
    }
    uint32_t k = datatypes::utils::indexOf(e.getOperator());
    if (std::find(K.begin(), K.end(), k) == K.end())
    {
      return Node::null();
    }
    covered.insert(k);
    from.push_back(datatypes::TupleUtils::nthElementOfTuple(h[0][0], p));
    to.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, k));
  }
  if (covering
      && covered.size() != std::set<uint32_t>(K.begin(), K.end()).size())
  {
    return Node::null();
  }
  Node body = h[1].substitute(from.begin(), from.end(), to.begin(), to.end());
  if (occursFree(body, h[0][0]))
  {
    return Node::null();
  }
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(xr, body), X);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateUnionDisjointKeys(
    const TNode& top) const
{
  // AGGREGATE_UNION_DISJOINT_KEYS: an aggregate over a union of parts no two of
  // which share a key value, under a filter Q that keeps only the groups some
  // row reached (see counterColumn): every reached group is that of one part,
  // so the groups are the union of the groups of the parts (see rewrites.h).
  // Two parts are disjoint when a key column that the rows of one part have
  // equal to a constant makes a condition on the rows of the other false, as
  // for the parts
  //   (bag.filter (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 0) s) 1))
  //               X)
  //   (bag.filter (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 0) s) 2))
  //               Y)
  // by column 0; or when the key columns of one part are constants or ites of
  // constants and each of their combinations makes such a condition false, or
  // is null in a column the other part never has null in.
  if (top[1].getKind() != Kind::BAG_FILTER
      || top[1][1].getKind() != Kind::TABLE_AGGREGATE || d_rewriter == nullptr)
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  Node A = top[1][1];
  if (A[2].getKind() != Kind::BAG_UNION_DISJOINT
      || counterColumn(top[1][0], asLambda(A[0]), A[1]) < 0)
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  if (K.empty())
  {
    return BagsRewriteResponse(top, Rewrite::NONE);
  }
  std::vector<Node> parts;
  {
    std::vector<Node> todo{A[2]};
    while (!todo.empty())
    {
      Node c = todo.back();
      todo.pop_back();
      if (c.getKind() == Kind::BAG_UNION_DISJOINT)
      {
        todo.push_back(c[1]);
        todo.push_back(c[0]);
      }
      else
      {
        parts.push_back(c);
      }
    }
  }
  TypeNode et = A[2].getType().getBagElementType();
  Node w = rowVariable(et);
  // the constant key values a part's rows can have: the leaves of its key
  // columns' ite trees, or none when not constant; for the key column
  // (ite c 1 (as nullable.null (Nullable Int))) of a map, the values 1 and
  // null; at most 16 combinations
  auto keyLeaves = [&](const Node& U, std::vector<std::vector<Node>>& out) {
    std::vector<Node> cols;
    if (U.getKind() == Kind::BAG_MAKE && isTupleTerm(U[0]))
    {
      for (uint32_t k : K)
      {
        cols.push_back(U[0][k]);
      }
    }
    else if (U.getKind() == Kind::BAG_MAP)
    {
      Node g = asLambda(U[0]);
      if (g.getKind() != Kind::LAMBDA || !isTupleTerm(g[1]))
      {
        return false;
      }
      for (uint32_t k : K)
      {
        cols.push_back(g[1][k]);
      }
    }
    else
    {
      return false;
    }
    std::vector<std::vector<Node>> combos{{}};
    for (const Node& c : cols)
    {
      std::vector<Node> leaves;
      std::vector<Node> todo{c};
      while (!todo.empty())
      {
        Node e = todo.back();
        todo.pop_back();
        if (e.getKind() == Kind::ITE)
        {
          todo.push_back(e[1]);
          todo.push_back(e[2]);
        }
        else if (e.isConst())
        {
          leaves.push_back(e);
        }
        else
        {
          return false;
        }
      }
      std::vector<std::vector<Node>> next;
      for (const std::vector<Node>& p : combos)
      {
        for (const Node& l : leaves)
        {
          std::vector<Node> q = p;
          q.push_back(l);
          next.push_back(q);
        }
      }
      combos = next;
      if (combos.size() > 16)
      {
        return false;
      }
    }
    out = combos;
    return true;
  };
  // whether no row of U has the key values of a row of V
  auto disjoint = [&](const Node& U, const Node& V) {
    {
      // a key column U's rows have equal to a constant that V's rows cannot
      // have: (= ((_ tuple.select 0) w) 1) of U, and a condition of V false
      // with 1 for ((_ tuple.select 0) w)
      std::set<Node> cu, cv;
      elementConditions(U, w, cu);
      elementConditions(V, w, cv);
      for (const Node& c : cu)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        for (size_t sd = 0; sd < 2; sd++)
        {
          if (!c[sd].isConst() || c[1 - sd].getKind() != Kind::APPLY_SELECTOR
              || c[1 - sd][0] != w
              || std::find(K.begin(),
                           K.end(),
                           datatypes::utils::indexOf(c[1 - sd].getOperator()))
                     == K.end())
          {
            continue;
          }
          for (const Node& d : cv)
          {
            Node e = d.substitute(TNode(c[1 - sd]), TNode(c[sd]));
            if (e != d && !occursFree(e, w) && rewritesToFalse(e))
            {
              return true;
            }
          }
        }
      }
    }
    std::vector<std::vector<Node>> leaves;
    if (!keyLeaves(U, leaves))
    {
      return false;
    }
    std::set<Node> conds;
    elementConditions(V, w, conds);
    std::set<uint32_t> nn = nonNullColumns(V);
    for (const std::vector<Node>& key : leaves)
    {
      bool nullWhereNone = false;
      for (size_t k = 0; k < K.size(); k++)
      {
        nullWhereNone =
            nullWhereNone || (isNullConstant(key[k]) && nn.count(K[k]));
      }
      if (nullWhereNone)
      {
        continue;
      }
      std::vector<Node> from, to;
      for (size_t k = 0; k < K.size(); k++)
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(w, K[k]));
        to.push_back(key[k]);
      }
      bool refuted = false;
      for (const Node& c : conds)
      {
        Node v = c.substitute(from.begin(), from.end(), to.begin(), to.end());
        if (!occursFree(v, w) && rewritesToFalse(v))
        {
          refuted = true;
          break;
        }
      }
      if (!refuted)
      {
        return false;
      }
    }
    return true;
  };
  for (size_t a = 0; a < parts.size(); a++)
  {
    for (size_t b = a + 1; b < parts.size(); b++)
    {
      if (!disjoint(parts[a], parts[b]) && !disjoint(parts[b], parts[a]))
      {
        return BagsRewriteResponse(top, Rewrite::NONE);
      }
    }
  }
  // (bag.union_disjoint ((_ table.aggr 0) f i U1) ((_ table.aggr 0) f i U2))
  Node u;
  for (const Node& U : parts)
  {
    std::vector<Node> children{A.getOperator(), A[0], A[1], U};
    Node g = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    u = u.isNull() ? g : d_nm->mkNode(Kind::BAG_UNION_DISJOINT, u, g);
  }
  Node ret = d_nm->mkNode(
      Kind::BAG_MAP, top[0], d_nm->mkNode(Kind::BAG_FILTER, top[1][0], u));
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_UNION_DISJOINT_KEYS);
}

Node BagsRewriter::eagerAggregation(const Node& f,
                                    const Node& init,
                                    const Node& J,
                                    const std::vector<uint32_t>& K) const
{
  // Eager aggregation, the SQL rewrite that pushes an aggregate through a join.
  // f folds the rows of J = (bag.filter P (table.product X Y)), grouped by the
  // columns K of the rows of J (none for a fold), with P equating columns of X
  // with columns of Y besides conditions on X alone and on Y alone, and every
  // column of f a key copy, the counter, or a sum, minimum, maximum or count
  // over a column of one side. The groups of the join are made of the groups of
  // X and of Y by their join and key columns: over a pair of groups, the sum of
  // X is its sum times the rows of Y, a minimum is that of X, and a count that
  // of X times the rows of Y. Returns (SEXPR f3 J' (SEXPR k0 ..)), where f3
  // folds J', the join of those two aggregates, the same way from the same
  // initial value, and k0 .. are the columns of the rows of J' that hold the
  // group columns K; null when J is not of that shape. For SQL's
  //   SELECT x.k, SUM(y.b) FROM X x JOIN Y y ON x.a = y.a GROUP BY x.k
  // with X : (Bag (Tuple Int Int)) of rows (tuple k a), Y : (Bag (Tuple Int
  // (Nullable Int))) of rows (tuple a b),
  //   J = (bag.filter
  //         (lambda ((t (Tuple Int Int Int (Nullable Int))))
  //           (= ((_ tuple.select 1) t) ((_ tuple.select 2) t)))
  //         (table.product X Y))
  // f making the rows (tuple k sum-of-b counter), and K = {0}, the aggregates
  // of the sides are
  //   AX = ((_ table.aggr 1 0) fx ix X), rows (tuple a k rows-x counter-x)
  //   AY = ((_ table.aggr 0) fy iy Y), rows (tuple a sum-of-b rows-y counter-y)
  // with rows-x and rows-y COUNT(*) columns, (nullable.some 0) plus one per
  // row, and their join is
  //   J' = (bag.filter
  //          (lambda ((p (Tuple Int Int (Nullable Int) Int Int (Nullable Int)
  //                             (Nullable Int) Int)))
  //            (and (= ((_ tuple.select 0) p) ((_ tuple.select 4) p))
  //                 (>= ((_ tuple.select 3) p) 1)
  //                 (>= ((_ tuple.select 7) p) 1)))
  //          (table.product AX AY))
  // f3 copies k, ((_ tuple.select 1) p); takes the step of the sum of f with
  // the sum of Y times the rows of X for its argument,
  //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 5) p))
  //        (as nullable.null (Nullable Int))
  //        (nullable.some (* (nullable.val ((_ tuple.select 5) p))
  //                          (nullable.val ((_ tuple.select 2) p)))))
  // and adds (* ((_ tuple.select 3) p) ((_ tuple.select 7) p)) to the counter;
  // the group columns are (SEXPR 1), where AX has k.
  if (J.getKind() != Kind::BAG_FILTER || J[1].getKind() != Kind::TABLE_PRODUCT
      || J[1][1].getKind() == Kind::TABLE_PRODUCT || d_rewriter == nullptr)
  {
    return Node::null();
  }
  Node P = asLambda(J[0]);
  Node X = J[1][0];
  Node Y = J[1][1];
  auto aggregated = [&](Node B) {
    while (B.getKind() == Kind::BAG_FILTER || B.getKind() == Kind::BAG_MAP
           || B.getKind() == Kind::BAG_SETOF)
    {
      B = B.getKind() == Kind::BAG_SETOF ? B[0] : B[1];
    }
    return B.getKind() == Kind::TABLE_AGGREGATE;
  };
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1 || aggregated(X)
      || aggregated(Y) || !X.getType().getBagElementType().isTuple()
      || !Y.getType().getBagElementType().isTuple())
  {
    return Node::null();
  }
  Node r = P[0][0];
  size_t wx = X.getType().getBagElementType().getTupleLength();
  size_t wy = Y.getType().getBagElementType().getTupleLength();
  // the conjuncts: join equations (= ((_ tuple.select a) r)
  // ((_ tuple.select b) r)) with a a column of X and b one of Y, and
  // conditions on one side, onX over X's rows xv and onY over Y's rows yv
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  std::vector<std::pair<uint32_t, uint32_t>> joins;  // (X column, Y column)
  std::vector<Node> onX, onY;
  Node xv = rowVariable(X.getType().getBagElementType());
  Node yv = rowVariable(Y.getType().getBagElementType());
  std::vector<Node> rx, tx, ry, ty;
  for (size_t k = 0; k < wx; k++)
  {
    rx.push_back(datatypes::TupleUtils::nthElementOfTuple(r, k));
    tx.push_back(datatypes::TupleUtils::nthElementOfTuple(xv, k));
  }
  for (size_t k = 0; k < wy; k++)
  {
    ry.push_back(datatypes::TupleUtils::nthElementOfTuple(r, wx + k));
    ty.push_back(datatypes::TupleUtils::nthElementOfTuple(yv, k));
  }
  for (const Node& c : conjuncts)
  {
    std::set<uint32_t> pos;
    if (!readPositions(c, r, pos) || bindsVariable(c, r))
    {
      return Node::null();
    }
    bool inX = true, inY = true;
    for (uint32_t q : pos)
    {
      inX = inX && q < wx;
      inY = inY && q >= wx;
    }
    if (inX)
    {
      onX.push_back(c.substitute(rx.begin(), rx.end(), tx.begin(), tx.end()));
      continue;
    }
    if (inY)
    {
      onY.push_back(c.substitute(ry.begin(), ry.end(), ty.begin(), ty.end()));
      continue;
    }
    if (c.getKind() == Kind::EQUAL && c[0].getKind() == Kind::APPLY_SELECTOR
        && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
        && c[1][0] == r)
    {
      uint32_t a = datatypes::utils::indexOf(c[0].getOperator());
      uint32_t b = datatypes::utils::indexOf(c[1].getOperator());
      if (a > b)
      {
        std::swap(a, b);
      }
      if (a < wx && b >= wx)
      {
        joins.push_back({a, b - wx});
        continue;
      }
    }
    return Node::null();
  }
  if (joins.empty())
  {
    return Node::null();
  }
  // the inner group columns of each side: its join columns and its keys,
  // gx = {1, 0} and gy = {0} in the example
  std::vector<uint32_t> gx, gy;
  auto addTo = [](std::vector<uint32_t>& v, uint32_t c) {
    if (std::find(v.begin(), v.end(), c) == v.end())
    {
      v.push_back(c);
    }
  };
  for (const std::pair<uint32_t, uint32_t>& jn : joins)
  {
    addTo(gx, jn.first);
    addTo(gy, jn.second);
  }
  for (uint32_t k : K)
  {
    if (k < wx)
    {
      addTo(gx, k);
    }
    else
    {
      addTo(gy, k - wx);
    }
  }
  // the columns of f: a KEY copy ((_ tuple.select k) t) of a group column,
  // the COUNTER (+ ((_ tuple.select q) acc) 1) from 0, a SUM or an
  // extremum (EXT, a minimum or a maximum) of a column of X or of Y that
  // skips nulls (see nullAwareStepKind), a count of the rows where a column
  // of X or of Y is not null (CNT), or COUNT(*) (STAR); src[q] is the column
  // of J the role reads
  Node xr = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  enum Role
  {
    KEY,
    COUNTER,
    SUM_X,
    SUM_Y,
    EXT_X,
    EXT_Y,
    CNT_X,
    CNT_Y,
    STAR
  };
  std::vector<Role> role(w);
  std::vector<uint32_t> src(w, 0);
  for (size_t q = 0; q < w; q++)
  {
    Node e = f[1][q];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
    if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == xr)
    {
      uint32_t k = datatypes::utils::indexOf(e.getOperator());
      if (std::find(K.begin(), K.end(), k) == K.end())
      {
        return Node::null();
      }
      role[q] = KEY;
      src[q] = k;
      continue;
    }
    if (e.getKind() == Kind::ADD && e.getNumChildren() == 2
        && ((e[0] == own && e[1] == d_one) || (e[1] == own && e[0] == d_one))
        && init[q].isConst() && init[q].getConst<Rational>().isZero())
    {
      role[q] = COUNTER;
      continue;
    }
    std::set<uint32_t> accRead, read;
    if (!readPositions(e, acc, accRead) || accRead.size() > 1
        || (accRead.size() == 1 && !accRead.count(q))
        || !readPositions(e, xr, read) || read.size() > 1)
    {
      return Node::null();
    }
    Node arg;
    int k = isNullConstant(init[q]) ? nullAwareStepKind(e, own, arg) : -1;
    if (k >= 0 && read.size() == 1)
    {
      uint32_t c = *read.begin();
      role[q] = k == 0 ? (c < wx ? SUM_X : SUM_Y) : (c < wx ? EXT_X : EXT_Y);
      src[q] = c;
      continue;
    }
    if (isCountStep(e, own, init[q]))
    {
      if (read.empty())
      {
        role[q] = STAR;
        continue;
      }
      uint32_t c = *read.begin();
      role[q] = c < wx ? CNT_X : CNT_Y;
      src[q] = c;
      continue;
    }
    return Node::null();
  }
  // the inner aggregate of one side (Y when side, X otherwise), over the
  // side's rows that satisfy its conditions: its group columns copied, f's
  // steps of the side's columns, its COUNT(*) and a counter; at[q] is the
  // column of the inner rows that holds column q of f, starAt and counterAt
  // those of COUNT(*) and of the counter. In the example, AY's rows are
  // (tuple a sum-of-b rows-y counter-y), with the steps
  //   ((_ tuple.select 0) s), [f's sum over (_ tuple.select 1) of s],
  //   (nullable.some (+ (nullable.val ((_ tuple.select 2) acc)) 1)),
  //   (+ ((_ tuple.select 3) acc) 1)
  auto inner = [&](bool side,
                   std::vector<size_t>& at,
                   size_t& counterAt,
                   size_t& starAt) {
    Node B = side ? Y : X;
    const std::vector<Node>& cond = side ? onY : onX;
    const std::vector<uint32_t>& g = side ? gy : gx;
    size_t off = side ? wx : 0;
    size_t wb = side ? wy : wx;
    Node bv = rowVariable(B.getType().getBagElementType());
    if (!cond.empty())
    {
      Node v = side ? yv : xv;
      Node body = cond.size() == 1 ? cond[0] : d_nm->mkNode(Kind::AND, cond);
      B = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(v, body), B);
    }
    std::vector<Node> from, to;
    for (size_t k = 0; k < wb; k++)
    {
      from.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, off + k));
      to.push_back(datatypes::TupleUtils::nthElementOfTuple(bv, k));
    }
    std::vector<size_t> cols;
    for (size_t q = 0; q < w; q++)
    {
      bool mine =
          side ? (role[q] == SUM_Y || role[q] == EXT_Y || role[q] == CNT_Y)
               : (role[q] == SUM_X || role[q] == EXT_X || role[q] == CNT_X);
      if (mine)
      {
        cols.push_back(q);
      }
    }
    std::vector<TypeNode> types;
    std::vector<TypeNode> btypes =
        B.getType().getBagElementType().getTupleTypes();
    for (uint32_t c : g)
    {
      types.push_back(btypes[c]);
    }
    for (size_t q : cols)
    {
      types.push_back(f[1][q].getType());
    }
    types.push_back(d_nm->integerType());
    TypeNode accType = d_nm->mkTupleType(types);
    Node acc2 = NodeManager::mkBoundVar("acc", accType);
    std::vector<Node> cells, seeds;
    for (size_t k = 0; k < g.size(); k++)
    {
      // any value of the column's sort seeds it: a group's first row
      // replaces it
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(bv, g[k]));
      seeds.push_back(NodeManager::mkGroundValue(btypes[g[k]]));
    }
    at.assign(w, 0);
    for (size_t c = 0; c < cols.size(); c++)
    {
      size_t q = cols[c];
      at[q] = g.size() + c;
      std::vector<Node> f2 = from, t2 = to;
      f2.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, q));
      t2.push_back(
          datatypes::TupleUtils::nthElementOfTuple(acc2, g.size() + c));
      cells.push_back(
          f[1][q].substitute(f2.begin(), f2.end(), t2.begin(), t2.end()));
      seeds.push_back(init[q]);
    }
    // COUNT(*), the side's rows per group,
    // (nullable.some (+ (nullable.val ((_ tuple.select q) acc)) 1)) from
    // (nullable.some 0), then the counter
    {
      TypeNode ni = d_nm->mkNullableType(d_nm->integerType());
      const DType& dt = ni.getDType();
      size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
      size_t q = g.size() + cols.size();
      types.insert(types.end() - 1, ni);
      accType = d_nm->mkTupleType(types);
      Node acc3 = NodeManager::mkBoundVar("acc", accType);
      // re-point the cells already built at the wider accumulator
      std::vector<Node> o, nn;
      for (size_t k = 0; k < q; k++)
      {
        o.push_back(datatypes::TupleUtils::nthElementOfTuple(acc2, k));
        nn.push_back(datatypes::TupleUtils::nthElementOfTuple(acc3, k));
      }
      for (Node& c : cells)
      {
        c = c.substitute(o.begin(), o.end(), nn.begin(), nn.end());
      }
      acc2 = acc3;
      Node valAcc =
          d_nm->mkNode(Kind::APPLY_SELECTOR,
                       dt[si][0].getSelector(),
                       datatypes::TupleUtils::nthElementOfTuple(acc2, q));
      cells.push_back(d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                   dt[si].getConstructor(),
                                   d_nm->mkNode(Kind::ADD, valAcc, d_one)));
      seeds.push_back(d_nm->mkNode(
          Kind::APPLY_CONSTRUCTOR, dt[si].getConstructor(), d_zero));
      starAt = q;
    }
    counterAt = g.size() + cols.size() + 1;
    cells.push_back(
        d_nm->mkNode(Kind::ADD,
                     datatypes::TupleUtils::nthElementOfTuple(acc2, counterAt),
                     d_one));
    seeds.push_back(d_zero);
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType, cells, 0, cells.size() - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType, seeds, 0, seeds.size() - 1);
    Node fb = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, bv, acc2), body);
    for (size_t q = 0; q < w; q++)
    {
      if (role[q] == KEY)
      {
        uint32_t k = src[q];
        bool here = side ? k >= wx : k < wx;
        if (here)
        {
          at[q] = std::find(g.begin(), g.end(), k - off) - g.begin();
        }
      }
    }
    std::vector<uint32_t> idx(g.begin(), g.end());
    Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(idx));
    std::vector<Node> children{op, fb, seed, B};
    return d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  };
  std::vector<size_t> atX, atY;
  size_t cx = 0, cy = 0, sx = 0, sy = 0;
  Node AX = inner(false, atX, cx, sx);
  Node AY = inner(true, atY, cy, sy);
  // J' tests both counters positive, so a keyed inner aggregate is its
  // reached groups' rows, AGGREGATE_KEYED (see keyedAggregateRows): rows of
  // the same columns
  for (Node* side : {&AX, &AY})
  {
    Node rows = keyedAggregateRows(*side);
    if (!rows.isNull())
    {
      *side = rows;
    }
  }
  size_t wax = AX.getType().getBagElementType().getTupleLength();
  Node product = d_nm->mkNode(Kind::TABLE_PRODUCT, AX, AY);
  Node pr = rowVariable(product.getType().getBagElementType());
  auto colX = [&](size_t p) {
    return datatypes::TupleUtils::nthElementOfTuple(pr, p);
  };
  auto colY = [&](size_t p) {
    return datatypes::TupleUtils::nthElementOfTuple(pr, wax + p);
  };
  // J', the pairs of groups that join, each reached by a row: the join
  // equations over the copies of the join columns, and the two counters
  // positive
  std::vector<Node> cond;
  for (const std::pair<uint32_t, uint32_t>& jn : joins)
  {
    size_t a = std::find(gx.begin(), gx.end(), jn.first) - gx.begin();
    size_t b = std::find(gy.begin(), gy.end(), jn.second) - gy.begin();
    cond.push_back(colX(a).eqNode(colY(b)));
  }
  cond.push_back(d_nm->mkNode(Kind::GEQ, colX(cx), d_one));
  cond.push_back(d_nm->mkNode(Kind::GEQ, colY(cy), d_one));
  Node joined = d_nm->mkNode(
      Kind::BAG_FILTER, mkLambda(pr, d_nm->mkNode(Kind::AND, cond)), product);
  // the outer steps: f's columns over the pairs of groups, each side's rows
  // per group its COUNT(*); pairs is the number of joined rows a pair of
  // groups stands for,
  //   (* (nullable.val ((_ tuple.select sx) p))
  //      (nullable.val ((_ tuple.select sy) p)))
  Node acc3 = NodeManager::mkBoundVar("acc", acc.getType());
  std::vector<Node> cells;
  auto rowsOf = [&](bool side) {
    Node c = side ? colY(sy) : colX(sx);
    const DType& dt = c.getType().getDType();
    size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
    return d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), c);
  };
  Node pairs = d_nm->mkNode(Kind::MULT, {rowsOf(false), rowsOf(true)});
  for (size_t q = 0; q < w; q++)
  {
    Node own3 = datatypes::TupleUtils::nthElementOfTuple(acc3, q);
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
    Node e = f[1][q];
    TypeNode t = e.getType();
    switch (role[q])
    {
      case KEY:
        cells.push_back(src[q] < wx ? colX(atX[q]) : colY(atY[q]));
        break;
      case COUNTER:
        cells.push_back(d_nm->mkNode(
            Kind::ADD, own3, d_nm->mkNode(Kind::MULT, colX(cx), colY(cy))));
        break;
      case EXT_X:
      case EXT_Y:
      {
        Node v = role[q] == EXT_X ? colX(atX[q]) : colY(atY[q]);
        std::vector<Node> fr{
            datatypes::TupleUtils::nthElementOfTuple(xr, src[q]), own};
        std::vector<Node> tt{v, own3};
        cells.push_back(
            e.substitute(fr.begin(), fr.end(), tt.begin(), tt.end()));
        break;
      }
      case SUM_X:
      case SUM_Y:
      {
        // the side's sum times the other side's count, null when the sum is
        Node v = role[q] == SUM_X ? colX(atX[q]) : colY(atY[q]);
        Node times = rowsOf(role[q] == SUM_X);
        const DType& dt = t.getDType();
        size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
        Node null =
            d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, dt[1 - si].getConstructor());
        Node val =
            d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), v);
        if (val.getType().isReal() && !val.getType().isInteger())
        {
          times = d_nm->mkNode(Kind::TO_REAL, times);
        }
        Node m =
            d_nm->mkNode(Kind::ITE,
                         {null.eqNode(v),
                          null,
                          d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                       dt[si].getConstructor(),
                                       d_nm->mkNode(Kind::MULT, val, times))});
        std::vector<Node> fr{
            datatypes::TupleUtils::nthElementOfTuple(xr, src[q]), own};
        std::vector<Node> tt{m, own3};
        cells.push_back(
            e.substitute(fr.begin(), fr.end(), tt.begin(), tt.end()));
        break;
      }
      case CNT_X:
      case CNT_Y:
      case STAR:
      {
        // counts add up: the side's count, or the number of pairs, per pair of
        // groups
        const DType& dt = t.getDType();
        size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
        Node by;
        if (role[q] == STAR)
        {
          by = pairs;
        }
        else
        {
          Node v = role[q] == CNT_X ? colX(atX[q]) : colY(atY[q]);
          Node val =
              d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), v);
          by = d_nm->mkNode(Kind::MULT, val, rowsOf(role[q] == CNT_X));
        }
        Node valAcc =
            d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), own3);
        cells.push_back(d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                     dt[si].getConstructor(),
                                     d_nm->mkNode(Kind::ADD, valAcc, by)));
        break;
      }
    }
  }
  Node body = datatypes::TupleUtils::constructTupleFromElements(
      acc.getType(), cells, 0, w - 1);
  Node f3 = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, pr, acc3), body);
  // the outer keys: where the key copies are
  std::vector<Node> out{f3, joined};
  std::vector<Node> keyPos;
  for (uint32_t k : K)
  {
    size_t p =
        k < wx ? std::find(gx.begin(), gx.end(), k) - gx.begin()
               : wax + (std::find(gy.begin(), gy.end(), k - wx) - gy.begin());
    keyPos.push_back(d_nm->mkConstInt(Rational(p)));
  }
  out.push_back(d_nm->mkNode(
      Kind::SEXPR, keyPos.empty() ? std::vector<Node>{d_zero} : keyPos));
  return d_nm->mkNode(Kind::SEXPR, out);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateOverJoin(const TNode& n) const
{
  // AGGREGATE_OVER_JOIN: an aggregate over a join as the aggregate over the
  // join of the two sides' groups, see eagerAggregation,
  //   ((_ table.aggr K) f i (bag.filter P (table.product X Y)))
  //   ---> ((_ table.aggr K') f3 i J')
  // with (f3, J', K') from eagerAggregation; in its example,
  //   ((_ table.aggr 1) f3 i J')
  // the shape of both sides of Calcite's AggregateJoinTransposeRule pairs
  Node f = asLambda(n[0]);
  const std::vector<uint32_t>& K =
      n.getOperator().getConst<ProjectOp>().getIndices();
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(n[1]) || K.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node e = eagerAggregation(f, n[1], n[2], K);
  if (e.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<uint32_t> keys;
  for (const Node& k : e[2])
  {
    keys.push_back(k.getConst<Rational>().getNumerator().toUnsignedInt());
  }
  Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(keys));
  std::vector<Node> children{op, e[0], n[1], e[1]};
  return BagsRewriteResponse(d_nm->mkNode(Kind::TABLE_AGGREGATE, children),
                             Rewrite::AGGREGATE_OVER_JOIN);
}

BagsRewriteResponse BagsRewriter::rewriteProductAggregateColumns(
    const TNode& n) const
{
  // PRODUCT_AGGREGATE_DEAD_COLUMN, in
  // (bag.map h (bag.filter P (table.product C0 C1 ..))) or the same without the
  // filter: a column of an aggregate among the components that neither h nor P
  // reads, nor another step of its aggregate, goes; AGGREGATE_DEAD_COLUMNS does
  // it for an aggregate alone (see rewrites.h). h then reads each column of the
  // product after it one to the left, and the steps read the narrower
  // accumulator; the columns removed can only merge rows that h maps to one
  // image anyway.
  Node h = asLambda(n[0]);
  Node P;
  Node T = n[1];
  if (T.getKind() == Kind::BAG_FILTER)
  {
    P = asLambda(T[0]);
    T = T[1];
  }
  if (T.getKind() != Kind::TABLE_PRODUCT || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1
      || (!P.isNull()
          && (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> comps;
  std::vector<size_t> starts;
  {
    Node rest = T;
    size_t at = 0;
    while (true)
    {
      Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
      if (!c.getType().getBagElementType().isTuple())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      comps.push_back(c);
      starts.push_back(at);
      at += c.getType().getBagElementType().getTupleLength();
      if (rest.getKind() != Kind::TABLE_PRODUCT)
      {
        break;
      }
      rest = rest[1];
    }
  }
  Node hv = h[0][0];
  std::set<uint32_t> hRead, pRead;
  if (!readPositions(h[1], hv, hRead)
      || (!P.isNull() && !readPositions(P[1], P[0][0], pRead)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  for (size_t i = 0; i < comps.size(); i++)
  {
    const Node& A = comps[i];
    if (A.getKind() != Kind::TABLE_AGGREGATE)
    {
      continue;
    }
    Node f = asLambda(A[0]);
    if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
        || !isTupleTerm(f[1]) || !isTupleTerm(A[1]))
    {
      continue;
    }
    Node acc = f[0][1];
    size_t w = f[1].getNumChildren();
    // a column nothing reads
    for (size_t q = 0; q < w; q++)
    {
      size_t pos = starts[i] + q;
      if (hRead.count(pos) || pRead.count(pos) || w <= 1)
      {
        continue;
      }
      bool used = false;
      Node own = datatypes::TupleUtils::nthElementOfTuple(acc, q);
      for (size_t k = 0; k < w && !used; k++)
      {
        used = k != q && expr::hasSubterm(f[1][k], own);
      }
      if (used)
      {
        continue;
      }
      // the aggregate without column q, and every later column one to the
      // left, in the accumulator acc2 and in the rows of the product
      std::vector<TypeNode> types;
      std::vector<Node> cells, seeds;
      for (size_t k = 0; k < w; k++)
      {
        if (k != q)
        {
          types.push_back(f[1][k].getType());
        }
      }
      TypeNode accType = d_nm->mkTupleType(types);
      Node acc2 = NodeManager::mkBoundVar("acc", accType);
      std::vector<Node> from, to;
      for (size_t k = 0, j = 0; k < w; k++)
      {
        if (k != q)
        {
          from.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, k));
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(acc2, j++));
        }
      }
      for (size_t k = 0; k < w; k++)
      {
        if (k != q)
        {
          cells.push_back(f[1][k].substitute(
              from.begin(), from.end(), to.begin(), to.end()));
          seeds.push_back(A[1][k]);
        }
      }
      Node body = datatypes::TupleUtils::constructTupleFromElements(
          accType, cells, 0, cells.size() - 1);
      Node seed = datatypes::TupleUtils::constructTupleFromElements(
          accType, seeds, 0, seeds.size() - 1);
      Node f2 = d_nm->mkNode(Kind::LAMBDA,
                             d_nm->mkNode(Kind::BOUND_VAR_LIST, f[0][0], acc2),
                             body);
      std::vector<Node> children{A.getOperator(), f2, seed, A[2]};
      std::vector<Node> cs = comps;
      cs[i] = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      Node prod = cs.back();
      for (size_t k = cs.size() - 1; k-- > 0;)
      {
        prod = d_nm->mkNode(Kind::TABLE_PRODUCT, cs[k], prod);
      }
      Node r2 = rowVariable(prod.getType().getBagElementType());
      size_t total =
          starts.back()
          + comps.back().getType().getBagElementType().getTupleLength();
      // h or P over the narrower rows r2: ((_ tuple.select k) v) is
      // ((_ tuple.select k) r2) before the column, ((_ tuple.select k-1) r2)
      // after it
      auto remap = [&](const Node& lambda) {
        Node v = lambda[0][0];
        std::vector<Node> o, nn;
        for (size_t k = 0; k < total; k++)
        {
          if (k == pos)
          {
            continue;
          }
          o.push_back(datatypes::TupleUtils::nthElementOfTuple(v, k));
          nn.push_back(datatypes::TupleUtils::nthElementOfTuple(
              r2, k < pos ? k : k - 1));
        }
        return mkLambda(
            r2, lambda[1].substitute(o.begin(), o.end(), nn.begin(), nn.end()));
      };
      Node input =
          P.isNull() ? prod : d_nm->mkNode(Kind::BAG_FILTER, remap(P), prod);
      Node ret = d_nm->mkNode(Kind::BAG_MAP, remap(h), input);
      return BagsRewriteResponse(ret, Rewrite::PRODUCT_AGGREGATE_DEAD_COLUMN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateDuplicateColumn(
    const TNode& n) const
{
  // AGGREGATE_DUPLICATE_COLUMN: columns p < q of f fold alike, the same step of
  // their own accumulator from the same initial value, as for SELECT SUM(a),
  // SUM(a): one fold, read twice by a map above the aggregate (see rewrites.h).
  // The step of q is that of p with ((_ tuple.select q) acc) for
  // ((_ tuple.select p) acc), and no other step reads column q.
  Node f = asLambda(n[0]);
  Node init = n[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(init))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  for (size_t q = 1; q < w; q++)
  {
    Node oq = datatypes::TupleUtils::nthElementOfTuple(acc, q);
    for (size_t p = 0; p < q; p++)
    {
      Node op = datatypes::TupleUtils::nthElementOfTuple(acc, p);
      if (init[p] != init[q])
      {
        continue;
      }
      TypeNode pType = f[1][p].getType();
      TypeNode qType = f[1][q].getType();
      if (pType != qType || f[1][q].substitute(TNode(oq), TNode(op)) != f[1][p])
      {
        continue;
      }
      // no other step reads column q
      bool read = false;
      for (size_t k = 0; k < w && !read; k++)
      {
        read = k != q && expr::hasSubterm(f[1][k], oq);
      }
      if (read)
      {
        continue;
      }
      std::vector<TypeNode> types;
      for (size_t k = 0; k < w; k++)
      {
        if (k != q)
        {
          types.push_back(f[1][k].getType());
        }
      }
      TypeNode accType = d_nm->mkTupleType(types);
      Node acc2 = NodeManager::mkBoundVar("acc", accType);
      std::vector<Node> from, to;
      for (size_t k = 0, j = 0; k < w; k++)
      {
        if (k != q)
        {
          from.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, k));
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(acc2, j++));
        }
      }
      std::vector<Node> cells, seeds;
      for (size_t k = 0; k < w; k++)
      {
        if (k != q)
        {
          cells.push_back(f[1][k].substitute(
              from.begin(), from.end(), to.begin(), to.end()));
          seeds.push_back(init[k]);
        }
      }
      Node body = datatypes::TupleUtils::constructTupleFromElements(
          accType, cells, 0, cells.size() - 1);
      Node seed = datatypes::TupleUtils::constructTupleFromElements(
          accType, seeds, 0, seeds.size() - 1);
      Node f2 = d_nm->mkNode(Kind::LAMBDA,
                             d_nm->mkNode(Kind::BOUND_VAR_LIST, f[0][0], acc2),
                             body);
      std::vector<Node> children{n.getOperator(), f2, seed, n[2]};
      Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      // the map that reads column p twice, the map of the example
      Node r = rowVariable(accType);
      std::vector<Node> out;
      for (size_t k = 0; k < w; k++)
      {
        size_t from2 = k == q ? p : (k < q ? k : k - 1);
        out.push_back(datatypes::TupleUtils::nthElementOfTuple(r, from2));
      }
      Node back = mkLambda(r,
                           datatypes::TupleUtils::constructTupleFromElements(
                               n.getType().getBagElementType(), out, 0, w - 1));
      return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_MAP, back, aggr),
                                 Rewrite::AGGREGATE_DUPLICATE_COLUMN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for ((_ table.aggr K) f i X): X split into groups, the rows that
// agree on the columns K, and each group folded by the step f from the
// initial value i into one row. They are tried in this order; the first that
// applies returns:
// - NOT_NULL_COLUMNS, for f a lambda of a row and an accumulator, over rows
//   of tuples (assumeNonNull);
// - AGGREGATE_NO_KEYS, for K empty: one group, all of X;
// - AGGREGATE_SORT_OUTPUT (rewriteAggregateSortOutput);
// - CANONICAL_VARIABLE (canonicalLambda), for f a lambda node;
// - AGGREGATE_MAP, for X a map (rewriteAggregateOfMap);
// - AGGREGATE_CONST, for i and X constants: the aggregate is evaluated.
// The rules after AGGREGATE_NO_KEYS see only a K that is not empty. For
// X : (Bag (Tuple Int Int)) and
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int)))
//         (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t)))),
//   (table.aggr f (tuple 0) X)
//   ---> (bag (bag.fold f (tuple 0) X) 1)                 (AGGREGATE_NO_KEYS)
BagsRewriteResponse BagsRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);
  {
    // AGGREGATE_INTEGER_SUM, see rewriteAggregateIntegerSum
    BagsRewriteResponse r = rewriteAggregateIntegerSum(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_OVER_JOIN, see rewriteAggregateOverJoin
    BagsRewriteResponse r = rewriteAggregateOverJoin(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_DUPLICATE_COLUMN, see rewriteAggregateDuplicateColumn
    BagsRewriteResponse r = rewriteAggregateDuplicateColumn(n);
    if (r.d_node != n)
    {
      return r;
    }
  }

  {
    // NOT_NULL_COLUMNS: in the body of f, as a lambda (see asLambda), the null
    // tests of the columns of the row f[0][0] that no row of X has null in
    // (see nonNullColumns) are decided, as
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true for column 1
    // never null (see assumeNonNull). The new aggregate keeps f's variables
    // and the operator (_ table.aggr K), its first child.
    Node f = asLambda(n[0]);
    if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2
        && n[2].getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(f[1], f[0][0], nonNullColumns(n[2]));
      if (b != f[1])
      {
        Node lambda = d_nm->mkNode(Kind::LAMBDA, f[0], b);
        std::vector<Node> children{n.getOperator(), lambda, n[1], n[2]};
        Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  {
    // AGGREGATE_SEMI_JOIN, see rewriteAggregateSemiJoin
    BagsRewriteResponse r = rewriteAggregateSemiJoin(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[2].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    // AGGREGATE_UNION_OF_MAPS: a union of maps by one function g is the map
    // of the union,
    //   ((_ table.aggr K) f i (bag.union_disjoint (bag.map g X1)
    //                                             (bag.map g X2)))
    // is the aggregate over (bag.map g (bag.union_disjoint X1 X2)), whose
    // map AGGREGATE_MAP absorbs (see rewriteAggregateOfMap); the rule
    // applies only when that one does
    std::vector<Node> parts;
    std::vector<Node> todo{n[2]};
    while (!todo.empty())
    {
      Node c = todo.back();
      todo.pop_back();
      if (c.getKind() == Kind::BAG_UNION_DISJOINT)
      {
        todo.push_back(c[1]);
        todo.push_back(c[0]);
      }
      else
      {
        parts.push_back(c);
      }
    }
    bool sameMap = parts.size() > 1;
    for (const Node& c : parts)
    {
      sameMap = sameMap && c.getKind() == Kind::BAG_MAP && c[0] == parts[0][0];
    }
    if (sameMap)
    {
      Node u = parts[0][1];
      for (size_t k = 1; k < parts.size(); k++)
      {
        u = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, u, parts[k][1]);
      }
      Node mapped = d_nm->mkNode(Kind::BAG_MAP, parts[0][0], u);
      std::vector<Node> children{n.getOperator(), n[0], n[1], mapped};
      Node candidate = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      BagsRewriteResponse r = rewriteAggregateOfMap(candidate);
      if (r.d_node != candidate)
      {
        return BagsRewriteResponse(r.d_node, Rewrite::AGGREGATE_UNION_OF_MAPS);
      }
    }
  }
  if (n[2].getKind() == Kind::BAG_FILTER && n[0].getKind() == Kind::LAMBDA
      && n[0][0].getNumChildren() == 2)
  {
    // AGGREGATE_FIXED_COLUMNS: the rows of every group pass the filter, so they
    // have the constants that it fixes (see fixedColumns, readFixed): the step
    // reads those instead of the columns, and a group column that the filter
    // fixes splits no group and leaves the group columns (see rewrites.h)
    std::map<uint32_t, Node> fixed = fixedColumns(n[2][0]);
    if (!fixed.empty())
    {
      Node f = n[0];
      Node body = readFixed(f[1], f[0][0], fixed);
      const std::vector<uint32_t>& K =
          n.getOperator().getConst<ProjectOp>().getIndices();
      std::vector<uint32_t> keys;
      for (uint32_t k : K)
      {
        if (!fixed.count(k))
        {
          keys.push_back(k);
        }
      }
      if (body != f[1] || keys.size() != K.size())
      {
        Node lambda = d_nm->mkNode(Kind::LAMBDA, f[0], body);
        Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(keys));
        std::vector<Node> children{op, lambda, n[1], n[2]};
        Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
        return BagsRewriteResponse(ret, Rewrite::AGGREGATE_FIXED_COLUMNS);
      }
    }
  }
  if (n.getOperator().getConst<ProjectOp>().getIndices().empty())
  {
    // AGGREGATE_NO_KEYS: grouping by no column makes one group, all of X, also
    // when X is empty (table.group by no column of an empty table is one
    // empty part), so the result is that group folded, once:
    //   (table.aggr f i X) ---> (bag (bag.fold f i X) 1)
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, n[0], n[1], n[2]);
    Node ret = d_nm->mkNode(Kind::BAG_MAKE, fold, d_one);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_NO_KEYS);
  }
  {
    // SORTED_KEYS, see rewriteSortedKeys
    BagsRewriteResponse r = rewriteSortedKeys(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_SORT_OUTPUT: the columns of the aggregate's rows in one
    // order, the copies of the group columns first, under a map that puts
    // them back, so that two aggregates that compute the same columns in two
    // orders become one aggregate (see rewriteAggregateSortOutput, which
    // returns n when the rule does not apply)
    BagsRewriteResponse r = rewriteAggregateSortOutput(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N
    // the id of f's alpha key, a node that is the same for lambdas that differ
    // only in the names of their variables (see canonicalLambda)
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      std::vector<Node> children{n.getOperator(), canonical, n[1], n[2]};
      Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  if (n[2].getKind() == Kind::BAG_MAP)
  {
    // AGGREGATE_MAP: for X = (bag.map g Y), the aggregate of Y, grouped by
    // the columns of Y that g copies to the group columns, with g read inside
    // the step; only for a step whose value does not depend on the order of
    // the rows (see rewriteAggregateOfMap)
    BagsRewriteResponse r = rewriteAggregateOfMap(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  // AGGREGATE_CONST: the aggregate of a constant table, from a constant
  // initial value, is evaluated
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = BagsUtils::evaluateTableAggregate(n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rule for (table.product X Y), every row of X followed by the columns
// of every row of Y:
// - PRODUCT_EMPTY: a product with the empty table on either side is empty.
// (A product of two constants is evaluated before, see postRewrite.)
// For X : (Bag (Tuple Int)),
//   (table.product X (as bag.empty (Bag (Tuple Int))))
//   ---> (as bag.empty (Bag (Tuple Int Int)))                 (PRODUCT_EMPTY)
BagsRewriteResponse BagsRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyBag(tableType));
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // PRODUCT_EMPTY: a product with the empty table is empty, here the empty
    // table of the product's sort, whose rows have the columns of both sides
    return BagsRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  // the normal form keeps the maps and filters above the products, see
  // rewriteProductOfMap and rewriteProductOfFilter, so that a query becomes
  // (bag.map h (bag.filter P (table.product X1 (table.product X2 ..)))), the
  // shape of SELECT h FROM X1, X2, .. WHERE P
  for (size_t side = 0; side < 2; side++)
  {
    // PRODUCT_BAG_MAKE, see rewriteProductOfBagMake
    BagsRewriteResponse r = rewriteProductOfBagMake(n, side);
    if (r.d_node != n)
    {
      return r;
    }
  }
  // PRODUCT_MAP_LEFT, PRODUCT_MAP_RIGHT, PRODUCT_FILTER_LEFT and
  // PRODUCT_FILTER_RIGHT
  if (n[0].getKind() == Kind::BAG_MAP)
  {
    return rewriteProductOfMap(n, true);
  }
  if (n[1].getKind() == Kind::BAG_MAP)
  {
    return rewriteProductOfMap(n, false);
  }
  if (n[0].getKind() == Kind::BAG_FILTER)
  {
    return rewriteProductOfFilter(n, true);
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    return rewriteProductOfFilter(n, false);
  }
  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    // PRODUCT_UNION_DISJOINT, on either side:
    //   (table.product (bag.union_disjoint A B) C)
    //   ---> (bag.union_disjoint (table.product A C) (table.product B C))
    Node a = d_nm->mkNode(Kind::TABLE_PRODUCT, n[0][0], n[1]);
    Node b = d_nm->mkNode(Kind::TABLE_PRODUCT, n[0][1], n[1]);
    return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b),
                               Rewrite::PRODUCT_UNION_DISJOINT);
  }
  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    Node a = d_nm->mkNode(Kind::TABLE_PRODUCT, n[0], n[1][0]);
    Node b = d_nm->mkNode(Kind::TABLE_PRODUCT, n[0], n[1][1]);
    return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b),
                               Rewrite::PRODUCT_UNION_DISJOINT);
  }
  if (n[0].getKind() == Kind::TABLE_PRODUCT)
  {
    // PRODUCT_ASSOC: rows are flat tuples, so the nesting is a spelling,
    //   (table.product (table.product A B) C)
    //   ---> (table.product A (table.product B C))
    Node bc = d_nm->mkNode(Kind::TABLE_PRODUCT, n[0][1], n[1]);
    return BagsRewriteResponse(d_nm->mkNode(Kind::TABLE_PRODUCT, n[0][0], bc),
                               Rewrite::PRODUCT_ASSOC);
  }
  // PRODUCT_SWAP: the factors of a right-nested product in one order,
  // (table.product A (table.product B C)) with B < A becomes a column
  // permutation of (table.product B (table.product A C)), see
  // rewriteProductSwap
  Node first = n[0];
  Node second = n[1].getKind() == Kind::TABLE_PRODUCT ? n[1][0] : n[1];
  if (second < first && first.getKind() != Kind::TABLE_PRODUCT)
  {
    return rewriteProductSwap(n);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteProductOfFilter(const TNode& n,
                                                         bool left) const
{
  // PRODUCT_FILTER_LEFT and PRODUCT_FILTER_RIGHT: a filter of a factor is a
  // filter of the product, over the columns of the factor in its rows
  // (see rewrites.h). The predicate p is applied to the part of the row t of
  // the product that is the factor's,
  // (tuple ((_ tuple.select 2) t) ((_ tuple.select 3) t)) for B of two columns
  // on the right of A of two, and beta-reduced (see applyFunction).
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node filtered = left ? n[0] : n[1];
  Node other = left ? n[1] : n[0];
  Node p = filtered[0];
  if (!composable(p))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node A = left ? filtered[1] : other;
  Node B = left ? other : filtered[1];
  TypeNode typeA = A.getType().getBagElementType();
  TypeNode typeB = B.getType().getBagElementType();
  TypeNode productType = n.getType().getBagElementType();
  Node t = rowVariable(productType);
  uint32_t nA = typeA.getTupleLength();
  uint32_t nB = typeB.getTupleLength();
  std::vector<Node> elems;
  uint32_t offset = left ? 0 : nA;
  uint32_t len = left ? nA : nB;
  for (uint32_t i = 0; i < len; i++)
  {
    elems.push_back(datatypes::TupleUtils::nthElementOfTuple(t, offset + i));
  }
  Node side = datatypes::TupleUtils::constructTupleFromElements(
      left ? typeA : typeB, elems, 0, len - 1);
  Node body = applyFunction(p, side);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node product = d_nm->mkNode(Kind::TABLE_PRODUCT, A, B);
  Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), product);
  return BagsRewriteResponse(
      ret, left ? Rewrite::PRODUCT_FILTER_LEFT : Rewrite::PRODUCT_FILTER_RIGHT);
}

BagsRewriteResponse BagsRewriter::rewriteProductSwap(const TNode& n) const
{
  // PRODUCT_SWAP: the factors of a product in the order of their node ids,
  // under a map perm that puts the columns back in their order, so that two
  // joins that list their tables in different orders become one product
  // (see rewrites.h). For A, B and C of one column with B < A,
  // (table.product A (table.product B C)) becomes
  // (bag.map perm (table.product B (table.product A C))) with
  //   perm = (lambda ((t (Tuple Int Int Int)))
  //            (tuple ((_ tuple.select 1) t)
  //                   ((_ tuple.select 0) t)
  //                   ((_ tuple.select 2) t)))
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node A = n[0];
  bool nested = n[1].getKind() == Kind::TABLE_PRODUCT;
  Node B = nested ? n[1][0] : n[1];
  Node C = nested ? Node(n[1][1]) : Node::null();
  TypeNode typeA = A.getType().getBagElementType();
  TypeNode typeB = B.getType().getBagElementType();
  uint32_t nA = typeA.getTupleLength();
  uint32_t nB = typeB.getTupleLength();
  uint32_t nC = nested ? C.getType().getBagElementType().getTupleLength() : 0;
  Node inner = nested ? d_nm->mkNode(Kind::TABLE_PRODUCT, A, C) : A;
  Node swapped = d_nm->mkNode(Kind::TABLE_PRODUCT, B, inner);
  TypeNode swappedType = swapped.getType().getBagElementType();
  Node t = rowVariable(swappedType);
  // swapped rows are (B, A, C); the result rows are (A, B, C)
  std::vector<Node> result;
  for (uint32_t i = 0; i < nA; i++)
  {
    result.push_back(datatypes::TupleUtils::nthElementOfTuple(t, nB + i));
  }
  for (uint32_t i = 0; i < nB; i++)
  {
    result.push_back(datatypes::TupleUtils::nthElementOfTuple(t, i));
  }
  for (uint32_t i = 0; i < nC; i++)
  {
    result.push_back(datatypes::TupleUtils::nthElementOfTuple(t, nB + nA + i));
  }
  TypeNode resultType = n.getType().getBagElementType();
  Node resultTuple = datatypes::TupleUtils::constructTupleFromElements(
      resultType, result, 0, result.size() - 1);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, resultTuple), swapped);
  return BagsRewriteResponse(ret, Rewrite::PRODUCT_SWAP);
}

// Returns the bound variable that the rules use for a row of sort tupleType
// when they build a lambda over the rows of a bag. There is one such
// variable per sort: every call with (Tuple Int Int) returns the same
// variable row_N : (Tuple Int Int), where N is the node id of the constant
// (as bag.empty (Bag (Tuple Int Int))). So two lambdas that the rules build
// for the same operation, as
//   (lambda ((row_N (Tuple Int Int))) ((_ tuple.project 1 0) row_N))
// for the same projection, are one node, and purification turns them into
// one function symbol. Any sort works, not only a tuple sort (lambdaOf
// passes the argument sort of any function).
Node BagsRewriter::rowVariable(TypeNode tupleType) const
{
  // The empty bag of the row sort is a constant that only this sort has; the
  // variable is cached on the role "row" and that key (see mkRewriterVar).
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(tupleType)));
  return mkRewriterVar(
      d_nm, "row", key, "row_" + std::to_string(key.getId()), tupleType);
}

// Whether some closure in body (a lambda, a quantifier, or any other binder,
// body itself included) has var among its bound variables. It says nothing
// about free occurrences of var. Callers test it before they substitute for
// var in body, because Node::substitute is syntactic: it would also replace
// the occurrences of var that such an inner closure binds. For
// t : (Tuple Int Int) and X : (Bag (Tuple Int Int)), it is true for the body
//   (>= (bag.count ((_ tuple.project 0) t)
//                  (bag.map (lambda ((t (Tuple Int Int)))
//                             ((_ tuple.project 1) t))
//                           X))
//       1)
// whose inner lambda binds t again, and false for (> ((_ tuple.select 0) t) 3).
bool BagsRewriter::bindsVariable(const Node& body, const Node& var) const
{
  // Visit each node of the DAG of body once; a leaf binds nothing.
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo = {body};
  while (!todo.empty())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second || cur.getNumChildren() == 0)
    {
      continue;
    }
    if (cur.isClosure())
    {
      // The first child of a closure is the list of the variables it binds.
      for (const TNode& v : cur[0])
      {
        if (v == var)
        {
          return true;
        }
      }
    }
    for (const TNode& c : cur)
    {
      todo.push_back(c);
    }
  }
  return false;
}

// Whether the bound variable v occurs free in n, that is, somewhere outside
// every closure of n that binds v. For t : (Tuple Int Int) and
// X : (Bag (Tuple Int Int)), it is true for
//   ((_ tuple.select 0) t)
// and false for
//   (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.select 0) t)) X)
// whose only occurrence of t is bound by the lambda.
bool BagsRewriter::occursFree(const Node& n, const Node& v) const
{
  // Cheap test first: a term that does not contain v has no free v.
  if (!expr::hasSubterm(n, v))
  {
    return false;
  }
  // Otherwise collect the bound variables that occur free in n.
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(n, fvs);
  return fvs.find(v) != fvs.end();
}

// Returns f as a lambda when f is a function array constant, and f itself
// otherwise (a lambda, or a function symbol such as a declared function).
// The rewriter stores a lambda whose body is a constant, or an ite over
// constants, as a function array constant (kind FUNCTION_ARRAY_CONST), so a
// rule that needs the variable and the body of a lambda reads such an f back
// first. For example, the predicate of the filter that keeps every row,
//   (lambda ((t (Tuple Int Int))) true),
// is a function array constant, and asLambda returns this lambda again (with
// a bound variable that FunctionConst::toLambda chooses).
Node BagsRewriter::asLambda(const Node& f) const
{
  if (f.getKind() == Kind::FUNCTION_ARRAY_CONST)
  {
    // toLambda returns the null node when it cannot convert f; f is then
    // returned unchanged.
    Node lambda = uf::FunctionConst::toLambda(f);
    if (!lambda.isNull())
    {
      return lambda;
    }
  }
  return f;
}

// Returns the application (fn x) beta-reduced, i.e. the body of the lambda
// fn with its variable replaced by x. For
//   fn = (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3))
// and x = (tuple a b), it returns
//   (> ((_ tuple.select 1) (tuple a b)) 3),
// which is not rewritten here; the rewriter later simplifies it to (> b 3).
// It returns the null node when the substitution could capture a variable,
// and the unreduced application (fn x), an APPLY_UF, when fn is not a lambda
// of one variable, as a declared function symbol.
Node BagsRewriter::applyFunction(const Node& fn, const Node& x) const
{
  // A function array constant is read as the lambda it stands for.
  Node f = asLambda(fn);
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    TNode var = f[0][0];
    if (var == x)
    {
      // (f var) is the body itself.
      return f[1];
    }
    if (bindsVariable(f[1], var) || bindsVariable(x, var))
    {
      // A closure in f's body that binds var again would have its own
      // occurrences of var replaced too, since substitute is syntactic. The
      // code also gives up when x contains a closure that binds var, which
      // is stricter than avoiding capture requires.
      return Node::null();
    }
    // A closure in f's body must not bind a variable that is free in x:
    // the copies of x placed under it would then refer to its variable.
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(x, fvs);
    for (const Node& v : fvs)
    {
      if (bindsVariable(f[1], v))
      {
        return Node::null();
      }
    }
    return f[1].substitute(var, TNode(x));
  }
  // Not a lambda of one variable: keep the application of the original fn.
  return d_nm->mkNode(Kind::APPLY_UF, fn, x);
}

// Returns the variable and the body of the lambda that the function f stands
// for, as a pair. For a lambda of one variable,
//   f = (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t))),
// it is (t, (tuple ((_ tuple.select 1) t))). For any other f, as a declared
// function h : (-> (Tuple Int Int) (Tuple Int)), it is (row_N, (h row_N)),
// with row_N the row variable of the argument sort (see rowVariable): f is
// then read as (lambda ((row_N (Tuple Int Int))) (h row_N)). f is not read
// through asLambda, so a function array constant also takes the second form;
// the rewriter beta-reduces such an application later.
std::pair<Node, Node> BagsRewriter::lambdaOf(const Node& f) const
{
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    return std::make_pair(f[0][0], f[1]);
  }
  // f has a function sort (-> T R): its variable has the sort T.
  TypeNode domain = f.getType().getArgTypes()[0];
  Node t = rowVariable(domain);
  return std::make_pair(t, d_nm->mkNode(Kind::APPLY_UF, f, t));
}

// Adds to positions the columns of the row var that body reads, a column
// being k in ((_ tuple.select k) var), and returns whether body reads var
// only through such selectors. For t : (Tuple Int Int Int) and
//   body = (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)),
// it adds {0, 2} and returns true. It returns false for (= t (tuple a b)),
// which reads the whole row, and for any occurrence of a var that is not a
// tuple: the selectors of another datatype, as (nullable.val t) for
// t : (Nullable Int), are not columns. A body without var gives true and adds
// nothing. Binders are not looked at, so an occurrence of var bound by a
// closure inside body counts too (callers test bindsVariable for that). On
// false, positions may already hold some columns.
bool BagsRewriter::readPositions(const Node& body,
                                 const Node& var,
                                 std::set<uint32_t>& positions) const
{
  bool tuple = var.getType().isTuple();
  // Visit each node of the DAG of body once.
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo = {body};
  while (!todo.empty())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (cur == var)
    {
      // The row itself, reached other than as the argument of a selector:
      // body reads the whole row.
      return false;
    }
    if (tuple && cur.getKind() == Kind::APPLY_SELECTOR && cur[0] == var)
    {
      // ((_ tuple.select k) var): record column k, and do not descend to var.
      positions.insert(datatypes::utils::indexOf(cur.getOperator()));
      continue;
    }
    for (const TNode& c : cur)
    {
      todo.push_back(c);
    }
  }
  return true;
}

// Whether the rules that compose functions, FILTER_MAP and MAP_MAP, may use
// the function f of a filter or a map: f must be a lambda of one variable, or
// a function array constant of one argument (see asLambda), since these rules
// build a new lambda from f's body. True for
//   (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
// and false for a declared function h : (-> (Tuple Int Int) (Tuple Int)).
// A declared function stays as it is, as cvc5 left it before these rules:
// composing it would build (lambda ((t (Tuple Int Int))) (h t)), a lambda
// that the input did not have, around a function whose value the model
// chooses.
bool BagsRewriter::composable(const Node& f) const
{
  Node l = asLambda(f);
  return l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 1;
}

// Returns the lambda of the one variable var with the body body: for
// t : (Tuple Int Int) and the body (> ((_ tuple.select 0) t) 3), it is
//   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3)).
Node BagsRewriter::mkLambda(const Node& var, const Node& body) const
{
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
}

BagsRewriteResponse BagsRewriter::rewriteFilterOfFilter(const TNode& n) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // FILTER_FILTER: two filters are one, by the conjunction of p[s := t] and q
  // for the outer filter (lambda ((s ..)) p) and the inner one
  // (lambda ((t ..)) q) (see rewrites.h)
  Node p = n[0];
  Node q = n[1][0];
  Node A = n[1][1];
  if (!composable(p) || !composable(q))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::pair<Node, Node> lq = lambdaOf(q);
  Node t = lq.first;
  Node pt = applyFunction(p, t);
  if (pt.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node body = d_nm->mkNode(Kind::AND, pt, lq.second);
  Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), A);
  return BagsRewriteResponse(ret, Rewrite::FILTER_FILTER);
}

// FILTER_MAP: a filter of a map becomes a map of a filter, which moves
// filters below maps. For n = (bag.filter p (bag.map f A)) with
// p = (lambda ((s S)) b) and f = (lambda ((t T)) e), the new filter keeps the
// rows t of A whose image e satisfies p:
//   (bag.map f (bag.filter (lambda ((t T)) b[s := e]) A)).
// This is sound for bags: the copies of an image y come from the rows t with
// e = y, and p keeps or drops all of them together, as b[s := e] does. For
// X : (Bag (Tuple Int Int)),
//   (bag.filter (lambda ((s (Tuple Int))) (> ((_ tuple.select 0) s) 3))
//               (bag.map (lambda ((t (Tuple Int Int)))
//                          (tuple ((_ tuple.select 1) t)))
//                        X))
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) t)))
//                 (bag.filter (lambda ((t (Tuple Int Int)))
//                               (> ((_ tuple.select 1) t) 3))
//                             X))                          (FILTER_MAP)
// once the rewriter simplifies ((_ tuple.select 0) (tuple ..)) in b[s := e].
BagsRewriteResponse BagsRewriter::rewriteFilterOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a new lambda, which the theory of uninterpreted
    // functions accepts only in a higher-order logic (see the constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // p, the filter's predicate over the rows s of the map; f, the map's
  // function over the rows t of A.
  Node p = n[0];
  Node f = n[1][0];
  Node A = n[1][1];
  if (!composable(p) || !composable(f))
  {
    // A declared function symbol is left alone (see composable).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t and e: the variable of f, a row of A, and f's body, its image.
  std::pair<Node, Node> lf = lambdaOf(f);
  Node t = lf.first;
  // b[s := e], the predicate p applied to the image of t; null when the
  // substitution would capture a variable (see applyFunction).
  Node body = applyFunction(p, lf.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // (bag.filter (lambda ((t T)) b[s := e]) A), under the original map f.
  Node filtered = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), A);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, f, filtered);
  return BagsRewriteResponse(ret, Rewrite::FILTER_MAP);
}

// MAP_MAP: a map of a map becomes one map, by the composition of the two
// functions. For n = (bag.map f (bag.map g A)) with f = (lambda ((s S)) e)
// and g = (lambda ((t T)) d), each row t of A is mapped to e[s := d]:
//   (bag.map (lambda ((t T)) e[s := d]) A).
// It is sound for bags since a row t of A, with its multiplicity, ends as the
// same row f(g(t)) either way. For X : (Bag (Tuple Int Int)),
//   (bag.map (lambda ((s (Tuple Int))) (tuple (+ ((_ tuple.select 0) s) 1)))
//            (bag.map (lambda ((t (Tuple Int Int)))
//                       (tuple ((_ tuple.select 1) t)))
//                     X))
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   (tuple (+ ((_ tuple.select 1) t) 1)))
//                 X)                                       (MAP_MAP)
// once the rewriter simplifies ((_ tuple.select 0) (tuple ..)) in e[s := d].
BagsRewriteResponse BagsRewriter::rewriteMapOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a new lambda, which the theory of uninterpreted
    // functions accepts only in a higher-order logic (see the constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // f, the outer map's function over the rows s of the inner map; g, the
  // inner map's function over the rows t of A.
  Node f = n[0];
  Node g = n[1][0];
  Node A = n[1][1];
  if (!composable(f) || !composable(g))
  {
    // A declared function symbol is left alone (see composable).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t and d: the variable of g, a row of A, and g's body, its image.
  std::pair<Node, Node> lg = lambdaOf(g);
  Node t = lg.first;
  // e[s := d], f applied to the image of t; null when the substitution
  // would capture a variable (see applyFunction).
  Node body = applyFunction(f, lg.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // (bag.map (lambda ((t T)) e[s := d]) A)
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, body), A);
  return BagsRewriteResponse(ret, Rewrite::MAP_MAP);
}

BagsRewriteResponse BagsRewriter::rewriteProductOfMap(const TNode& n,
                                                      bool left) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // PRODUCT_MAP_LEFT and PRODUCT_MAP_RIGHT: a map of a factor is a map of the
  // product, which keeps the columns of the other factor (see rewrites.h). The
  // function f is applied to the part of the row t of the product that is the
  // factor's, (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)) for A of
  // two columns on the left; on the right, the image goes after the columns of
  // the left factor.
  Node mapped = left ? n[0] : n[1];
  Node other = left ? n[1] : n[0];
  Node f = mapped[0];
  Node inner = mapped[1];
  if (!composable(f))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node A = left ? inner : other;
  Node B = left ? other : inner;
  TypeNode typeA = A.getType().getBagElementType();
  TypeNode typeB = B.getType().getBagElementType();
  if (!typeA.isTuple() || !typeB.isTuple())
  {
    // the map builds rows from something that is not a table: no product of
    // its argument exists
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode productType = datatypes::TupleUtils::concatTupleTypes(typeA, typeB);
  Node t = rowVariable(productType);
  uint32_t nA = typeA.getTupleLength();
  uint32_t nB = typeB.getTupleLength();
  std::vector<Node> elemsA, elemsB;
  for (uint32_t i = 0; i < nA; i++)
  {
    elemsA.push_back(datatypes::TupleUtils::nthElementOfTuple(t, i));
  }
  for (uint32_t i = 0; i < nB; i++)
  {
    elemsB.push_back(datatypes::TupleUtils::nthElementOfTuple(t, nA + i));
  }
  Node tupleA = datatypes::TupleUtils::constructTupleFromElements(
      typeA, elemsA, 0, nA - 1);
  Node tupleB = datatypes::TupleUtils::constructTupleFromElements(
      typeB, elemsB, 0, nB - 1);
  Node image = applyFunction(f, left ? tupleA : tupleB);
  if (image.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode imageType = f.getType().getRangeType();
  uint32_t nI = imageType.getTupleLength();
  std::vector<Node> result;
  if (left)
  {
    for (uint32_t i = 0; i < nI; i++)
    {
      result.push_back(datatypes::TupleUtils::nthElementOfTuple(image, i));
    }
    result.insert(result.end(), elemsB.begin(), elemsB.end());
  }
  else
  {
    result.insert(result.end(), elemsA.begin(), elemsA.end());
    for (uint32_t i = 0; i < nI; i++)
    {
      result.push_back(datatypes::TupleUtils::nthElementOfTuple(image, i));
    }
  }
  TypeNode resultType = n.getType().getBagElementType();
  Node resultTuple = datatypes::TupleUtils::constructTupleFromElements(
      resultType, result, 0, result.size() - 1);
  Node product = d_nm->mkNode(Kind::TABLE_PRODUCT, A, B);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, resultTuple), product);
  return BagsRewriteResponse(
      ret, left ? Rewrite::PRODUCT_MAP_LEFT : Rewrite::PRODUCT_MAP_RIGHT);
}

// PROJECT_TO_MAP: a projection of a table becomes the map of tuple.project
// over its rows, with the same columns, so that the rules for maps, as
// MAP_MAP and FILTER_MAP, also apply to projections. For
// X : (Bag (Tuple Int Int)),
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   ((_ tuple.project 1 0) t))
//                 X)                                       (PROJECT_TO_MAP)
// where t is the row variable of X's row sort (see rowVariable), so that
// two equal projections become one lambda.
BagsRewriteResponse BagsRewriter::postRewriteProject(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a lambda where the term has none, which the theory of
    // uninterpreted functions accepts only in a higher-order logic (see the
    // constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Assert(n.getKind() == Kind::TABLE_PROJECT);
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  // The columns of table.project, kept in a ProjectOp, become the operator
  // of tuple.project.
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = d_nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  // ((_ tuple.project J) t) for t, a row of A.
  Node t = rowVariable(elementType);
  Node projection = d_nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, projection), A);
  return BagsRewriteResponse(ret, Rewrite::PROJECT_TO_MAP);
}

// Returns the columns that a projection lambda selects, in order, and an
// empty vector when f is not a projection. A projection is a lambda of one
// row x whose body is one of
//   (tuple ((_ tuple.select j0) x) .. ((_ tuple.select jm) x))
//   ((_ tuple.project j0 .. jm) x)
// and the result is then j0, .., jm. Both
//   (lambda ((t (Tuple Int Int Int)))
//     (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
// and
//   (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 2 0) t))
// give {2, 0}. A column may repeat: the body
//   (tuple ((_ tuple.select 1) t) ((_ tuple.select 1) t))
// gives {1, 1}. A projection onto no column also gives the empty vector.
std::vector<uint32_t> BagsRewriter::projectionIndices(const Node& f) const
{
  std::vector<uint32_t> out;
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return out;
  }
  Node x = f[0][0];
  Node body = f[1];
  if (body.getKind() == Kind::TUPLE_PROJECT && body[0] == x)
  {
    // ((_ tuple.project j0 .. jm) x): the indices of the operator.
    return body.getOperator().getConst<ProjectOp>().getIndices();
  }
  // Otherwise the body must build a tuple from a row x that is a tuple
  // itself: the selectors of a row of another datatype, as (field1 x), are
  // not columns.
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple()
      || !x.getType().isTuple())
  {
    return out;
  }
  for (const Node& c : body)
  {
    // Each component must be ((_ tuple.select j) x), a copy of column j of
    // x; any other component, as a constant or (+ ((_ tuple.select 0) x) 1),
    // means f is not a projection.
    if (c.getKind() != Kind::APPLY_SELECTOR || c[0] != x)
    {
      return std::vector<uint32_t>();
    }
    out.push_back(datatypes::utils::indexOf(c.getOperator()));
  }
  return out;
}

// AGGREGATE_MAP: an aggregate of a map becomes an aggregate of the map's
// argument. n = ((_ table.aggr K) f i (bag.map g X)) groups the rows of the
// map by their columns K and folds each group with the step f from the
// initial value i; a step is the function (lambda ((t R) (acc A)) e) that a
// fold applies to each row t and the accumulator acc, the value so far. The
// rule instead groups X by the columns JK of X that g copies to the group
// columns, and folds with f[t := (g x)], which reads each row x of X through
// g. For X : (Bag (Tuple Int Int Int)),
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t)
//              (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
//     (tuple 0 0)
//     (bag.map (lambda ((t (Tuple Int Int Int)))
//                (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
//              X))
//   ---> ((_ table.aggr 2)
//          (lambda ((x (Tuple Int Int Int)) (acc (Tuple Int Int)))
//            (tuple ((_ tuple.select 2) x)
//                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) x))))
//          (tuple 0 0)
//          X)                                              (AGGREGATE_MAP)
// once the rewriter simplifies the selectors of (g x). Each group of the map
// is then the image under g of one group of X. The rule also needs a step
// whose result does not depend on the order of the rows
// (see orderIndependentStep).
BagsRewriteResponse BagsRewriter::rewriteAggregateOfMap(const TNode& n) const
{
  // Unlike FILTER_MAP, this rule does not test the higher-order flag: its new
  // lambda replaces the lambda f that the term already has.
  // f, the step, must be a lambda of a row and an accumulator (it is not
  // read through asLambda), and g, the map's function, a lambda whose body
  // builds a tuple (tuple c0 .. cm), so that column k of a row of the map is
  // the term ck.
  Node f = n[0];
  Node i = n[1];
  Node g = asLambda(n[2][0]);
  Node X = n[2][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
      || g[1].getKind() != Kind::APPLY_CONSTRUCTOR || !g[1].getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // gv, the variable of g, is a row of X. Each group column k of the map's
  // rows is one of three kinds, by the term ck that g puts there:
  // - a copy ((_ tuple.select j) gv) of column j of X, whose j goes to JK;
  // - a term that reads gv otherwise, as (+ ((_ tuple.select 0) gv) 42),
  //   collected in computed and checked below;
  // - a term that does not read gv, as the constant 7: every row of the map
  //   has the same value there, so it splits no group and is dropped.
  Node gv = g[0][0];
  std::vector<uint32_t> K = n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<uint32_t> JK;
  std::vector<Node> computed;
  for (uint32_t k : K)
  {
    if (k >= g[1].getNumChildren())
    {
      // K names a column that g's tuple does not have.
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node c = g[1][k];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == gv)
    {
      JK.push_back(datatypes::utils::indexOf(c.getOperator()));
    }
    else if (occursFree(c, gv))
    {
      computed.push_back(c);
    }
  }
  for (const Node& c : computed)
  {
    // A computed group column must read only columns of gv that are also
    // copied to group columns, i.e. columns in JK, through
    // ((_ tuple.select j) gv), with no closure inside it binding gv again.
    // Then two rows of X that agree on JK agree on it too, so it splits no
    // group that the copied columns do not: (+ ((_ tuple.select 0) gv) 42)
    // beside ((_ tuple.select 0) gv), as deptno + 42 beside deptno in SQL.
    std::set<uint32_t> positions;
    if (!readPositions(c, gv, positions) || bindsVariable(c, gv))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    for (uint32_t pos : positions)
    {
      if (std::find(JK.begin(), JK.end(), pos) == JK.end())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
  }
  // JK, sorted and without duplicates, holds the group columns of the new
  // aggregate. Two rows of X agree on JK exactly when their images under g
  // agree on K, so grouping X by JK and the map by K give matching groups.
  std::sort(JK.begin(), JK.end());
  JK.erase(std::unique(JK.begin(), JK.end()), JK.end());
  TypeNode rowType = X.getType().getBagElementType();
  if (!rowType.isTuple())
  {
    // The rows of X must be tuples, else the selectors of gv above are not
    // columns.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // A group of the map and the group of X it comes from are two different
  // bags, and cvc5 may fold each in an order of its own. So the rule applies
  // only to a step whose result is the same in every order. The rows of a
  // group of the map all agree on the columns K, and nonNullColumns gives
  // the columns of the map's rows that are never null.
  std::set<uint32_t> same(K.begin(), K.end());
  if (!orderIndependentStep(f, same, nonNullColumns(n[2])))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // The new step is (lambda ((x R) (y A)) f's body[t := (g x)]): x, the row
  // variable of X's row sort, y, f's own accumulator, and gx = (g x)
  // beta-reduced.
  Node x = rowVariable(rowType);
  Node y = f[0][1];
  Node gx = applyFunction(n[2][0], x);
  // Give up when computing (g x) would capture a variable (gx is null), when
  // a closure in f's body binds x (the copies of gx under it would refer to
  // that closure's variable), or when x is f's accumulator y itself, which
  // the new lambda would bind twice.
  if (gx.isNull() || bindsVariable(f[1], x) || x == y)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node body = f[1].substitute(TNode(f[0][0]), TNode(gx));
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, y), body);
  // ((_ table.aggr JK) new step i X)
  Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(JK));
  std::vector<Node> children{op, lambda, i, X};
  Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_MAP);
}

// Whether folding a bag with the step f gives the same value whatever the
// order of its rows. A step is the function (lambda ((x R) (acc A)) e) that a
// fold applies to each row x and the accumulator acc, the value so far. cvc5
// folds each bag in an order of its own (see
// BagReduction::reduceFoldOperator), so a rule that replaces the bag being
// folded by another with the same rows, as AGGREGATE_MAP does, keeps the
// value only for such a step. same holds the columns of x that all rows
// folded together share (the group columns of an aggregate), and nonNull the
// columns of x that are never null. With same {0}, it is true for the step
//   (lambda ((x (Tuple Int Int)) (acc (Tuple Int Int)))
//     (tuple ((_ tuple.select 0) x)
//            (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) x))))
// (the group column and a sum), and false for
//   (lambda ((x (Tuple Int Int)) (acc Int)) ((_ tuple.select 1) x))
// whose value is column 1 of whichever row comes last. The accepted shapes,
// sums, counts, minimums, maximums, SQL's null-skipping SUM, MIN and MAX,
// and copies of shared columns, are listed in the lambda column below.
bool BagsRewriter::orderIndependentStep(const Node& f,
                                        const std::set<uint32_t>& same,
                                        const std::set<uint32_t>& nonNull) const
{
  // When the step builds a tuple of the accumulator's sort, each column of
  // the tuple is checked on its own, with its own component of acc as its
  // accumulator; a column may read no other component (see column below).
  // The columns then fold independently of each other, and when each one's
  // value is the same in any order, so is the tuple's.
  Node l = asLambda(f);
  if (l.getKind() != Kind::LAMBDA || l[0].getNumChildren() != 2)
  {
    return false;
  }
  // x, the row; acc, the accumulator.
  Node x = l[0][0];
  Node acc = l[0][1];
  // free(e): whether e reads no accumulator, i.e. acc is not free in e.
  auto free = [&](const Node& e) { return !occursFree(e, acc); };
  // valueOf(t), for t of a nullable sort (Nullable S): the value v when t is
  // (nullable.some v), and otherwise the term (nullable.val t), built with
  // the selector of the constructor that has one argument.
  auto valueOf = [&](const Node& t) {
    if (t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getNumChildren() == 1)
    {
      return t[0];
    }
    const DType& dt = t.getType().getDType();
    size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
    return d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), t);
  };
  // compares(c, a, b): whether c compares a and b, which are both numbers or
  // both strings: c is one of (< a b), (<= a b), (> a b), (>= a b), or
  // (str.< a b), (str.<= a b), with a and b either way round. c and each
  // candidate are compared after rewriting, so c may be written in any form
  // that the rewriter brings to the same normal form. Without a rewriter
  // (d_rewriter null) no c compares.
  auto compares = [&](const Node& c, const Node& a, const Node& b) {
    bool numbers = a.getType().isRealOrInt() && b.getType().isRealOrInt();
    bool strings = a.getType().isString() && b.getType().isString();
    if (d_rewriter == nullptr || !(numbers || strings))
    {
      return false;
    }
    Node rc = d_rewriter->rewrite(c);
    std::vector<Kind> kinds =
        numbers ? std::vector<Kind>{Kind::LT, Kind::LEQ, Kind::GT, Kind::GEQ}
                : std::vector<Kind>{Kind::STRING_LT, Kind::STRING_LEQ};
    for (Kind k : kinds)
    {
      // Each kind with (a, b) and with (b, a).
      for (size_t s = 0; s < 2; s++)
      {
        Node cmp = s == 0 ? d_nm->mkNode(k, a, b) : d_nm->mkNode(k, b, a);
        if (rc == d_rewriter->rewrite(cmp))
        {
          return true;
        }
      }
    }
    return false;
  };
  // combines(c, a, b), for nullable a and b that are both not null where c
  // is used: whether c is their sum, minimum or maximum. The sum is
  // (nullable.some s) with s equal to (+ (nullable.val a) (nullable.val b))
  // up to rewriting; the minimum or the maximum is (ite cmp a b) or
  // (ite cmp b a) with cmp comparing their values, as
  // (ite (< (nullable.val a) (nullable.val b)) a b). Each is commutative and
  // associative, so it combines the rows in any order to one value.
  auto combines = [&](const Node& c, const Node& a, const Node& b) {
    if (c.getKind() == Kind::APPLY_CONSTRUCTOR && c.getNumChildren() == 1)
    {
      // (nullable.some s): s must have the sort of the sum, and the rewriter
      // must reduce (= s sum) to true.
      Node sum = d_nm->mkNode(Kind::ADD, {valueOf(a), valueOf(b)});
      TypeNode t = c[0].getType();
      if (d_rewriter == nullptr || t != sum.getType())
      {
        return false;
      }
      Node r = d_rewriter->rewrite(c[0].eqNode(sum));
      return r.isConst() && r.getConst<bool>();
    }
    // An ite that returns a or b by a comparison of their values (any
    // comparison of the two picks the smaller or the larger one).
    if (c.getKind() != Kind::ITE
        || !((c[1] == a && c[2] == b) || (c[1] == b && c[2] == a)))
    {
      return false;
    }
    Node va = valueOf(a);
    Node vb = valueOf(b);
    return compares(c[0], va, vb);
  };
  // nullTested(c): the term t that c tests for null, for
  // c = (= (as nullable.null (Nullable Int)) t) or the same equality the
  // other way round; the null node for any other c.
  auto nullTested = [](const Node& c) {
    if (c.getKind() == Kind::EQUAL)
    {
      for (size_t s = 0; s < 2; s++)
      {
        if (isNullConstant(c[s]))
        {
          return c[1 - s];
        }
      }
    }
    return Node::null();
  };
  // sumOf(e, own): whether e is a sum (+ own e1 .. em) of own, exactly once,
  // and terms ei that read no accumulator (they may read the row x). Each
  // row adds its own amount, so the total is the same in any order.
  auto sumOf = [&](const Node& e, const Node& own) {
    if (e.getKind() != Kind::ADD)
    {
      return false;
    }
    size_t owns = 0;
    for (const Node& c : e)
    {
      if (c == own)
      {
        owns++;
      }
      else if (!free(c))
      {
        return false;
      }
    }
    return owns == 1;
  };
  // column(e, own): whether e, the term that computes the new value of the
  // accumulator own (a component ((_ tuple.select q) acc), or acc itself),
  // gives the same final value in every order of the rows. Below, v and a
  // stand for terms that read no accumulator; they may read the row x.
  std::function<bool(const Node&, const Node&)> column;
  column = [&](const Node& e, const Node& own) {
    if (free(e))
    {
      // A term that reads no accumulator: the final value is e of the last
      // row folded. That is one value in any order when e reads no column of
      // x, as a constant, or reads only columns in same, which all rows
      // folded together share, as the copy ((_ tuple.select 0) x) of a group
      // column 0. A term that reads x other than through the selectors
      // ((_ tuple.select k) x) is rejected.
      std::set<uint32_t> read;
      return !occursFree(e, x)
             || (readPositions(e, x, read)
                 && std::includes(
                     same.begin(), same.end(), read.begin(), read.end()));
    }
    if (e == own)
    {
      // own unchanged: the column keeps its initial value.
      return true;
    }
    {
      // Every other shape must read the accumulator through own only: with
      // own replaced by a fresh variable mark, acc must no longer occur free
      // in e. A column that reads another component of acc is rejected.
      Node mark = NodeManager::mkBoundVar("own", own.getType());
      if (occursFree(e.substitute(TNode(own), TNode(mark)), acc))
      {
        return false;
      }
    }
    // A sum: (+ own v ..), as the counter (+ own 1); or, for a nullable own,
    // (nullable.some (+ (nullable.val own) v ..)).
    TypeNode ownType = own.getType();
    bool nullable = ownType.isNullable();
    if (sumOf(e, own)
        || (nullable && e.getKind() == Kind::APPLY_CONSTRUCTOR
            && e.getNumChildren() == 1 && sumOf(e[0], valueOf(own))))
    {
      return true;
    }
    // Every remaining shape is an ite.
    if (e.getKind() != Kind::ITE)
    {
      return false;
    }
    if (free(e[0]))
    {
      // The condition reads no accumulator. SQL's SUM, MIN or MAX of a
      // nullable argument a: a null a keeps own, a non-null a replaces a
      // null own, and otherwise combines with own (see combines):
      //   (ite (= (as nullable.null (Nullable Int)) a)
      //        own
      //        (ite (= (as nullable.null (Nullable Int)) own) a C))
      // with C the sum, minimum or maximum of a and own. The result does not
      // depend on the order: it is the sum, minimum or maximum of the values
      // that are not null among own's initial value and the a of the rows,
      // and null when there is none.
      Node a = nullTested(e[0]);
      if (nullable && !a.isNull() && e[1] == own && free(a)
          && a.getType() == ownType && e[2].getKind() == Kind::ITE
          && nullTested(e[2][0]) == own && e[2][1] == a
          && combines(e[2][2], a, own))
      {
        return true;
      }
      // An accepted shape u applied only to the rows on which the condition
      // c fails, (ite c own u), or holds, (ite c u own). Since c reads no
      // accumulator, these rows form a sub-bag fixed by the rows alone, so u
      // must be accepted itself. SQL's COUNT of a nullable column 1, which
      // counts the rows where it is not null, is
      //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
      //        own
      //        (+ own 1)).
      if (e[1] == own)
      {
        return column(e[2], own);
      }
      if (e[2] == own)
      {
        return column(e[1], own);
      }
      return false;
    }
    // The condition reads the accumulator. A minimum or a maximum: the ite
    // returns v or own by a comparison of v and own (see compares), as
    // (ite (> v own) v own), the maximum of own's initial value and the v of
    // the rows, or (ite (< own v) own v), their minimum.
    for (size_t s = 1; s < 3; s++)
    {
      if (e[3 - s] == own && free(e[s]) && compares(e[0], e[s], own))
      {
        return true;
      }
    }
    // SQL's SUM, MIN or MAX as above, of an argument a that is never null
    // (nonNullTerm, given the columns nonNull of x that are never null): the
    // test of a for null has been decided false and removed, which leaves
    //   (ite (= (as nullable.null (Nullable Int)) own) a C)
    // with C the sum, minimum or maximum of a and own. Without knowing that a
    // is never null, this shape could depend on the order, so the test is
    // needed.
    return nullable && nullTested(e[0]) == own && free(e[1])
           && e[1].getType() == ownType
           && nonNullTerm(e[1], x, nonNull, Node::null(), {})
           && combines(e[2], e[1], own);
  };
  Node body = l[1];
  TypeNode accType = acc.getType();
  if (body.getKind() == Kind::APPLY_CONSTRUCTOR && accType.isTuple()
      && body.getType() == accType)
  {
    // The step builds a tuple (tuple e0 .. em) of the accumulator's sort:
    // check each ei with ((_ tuple.select i) acc) as its own accumulator.
    for (size_t q = 0, w = body.getNumChildren(); q < w; q++)
    {
      if (!column(body[q], datatypes::TupleUtils::nthElementOfTuple(acc, q)))
      {
        return false;
      }
    }
    return true;
  }
  // Any other body is checked as one column, with acc as its accumulator.
  return column(body, acc);
}

// Whether the formula n rewrites to false: true exactly when the full
// rewriter d_rewriter turns n into the constant false. For instance
//   (>= ((_ tuple.select 2) (tuple 0 0 0)) 1)
// rewrites to (>= 0 1) and then to false, so the answer is true; for
//   (>= ((_ tuple.select 2) r) 1)
// with r a variable it is false, as a formula that the rewriter does not
// decide is not known to be false. d_rewriter must not be null: the callers
// check it (see rejectsInitialRow).
bool BagsRewriter::rewritesToFalse(const Node& n) const
{
  Node r = d_rewriter->rewrite(n);
  return r.isConst() && !r.getConst<bool>();
}

// Whether the predicate P is false on the row of initial values i of an
// aggregate ((_ table.aggr K) f i X), that is, whether (P i) rewrites to
// false. That row is the one row of the aggregate of an empty table: for an
// empty X, table.group gives one empty group, which folds to i, so the
// aggregate is (bag i 1) although no row of X made it. A filter by such a P
// drops that row anyway, which lets AGGREGATE_KEYED replace the aggregate
// under it by rows that lack it (see keyedAggregateRows). The answer is true
// for a test that a count of rows, which starts at 0, is positive:
//   P = (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int)))
//         (>= ((_ tuple.select 2) r) 1))
//   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
// as (P i) is (>= ((_ tuple.select 2) i) 1), which rewrites to (>= 0 1),
// that is, to false.
bool BagsRewriter::rejectsInitialRow(const Node& P, const Node& i) const
{
  // Without the rewriter (P i) cannot be decided: answer false, which makes
  // the callers leave their term as it is.
  if (d_rewriter == nullptr)
  {
    return false;
  }
  // (P i) beta-reduced, P's variable replaced by i (see applyFunction). It is
  // null when the replacement would capture a variable, and the answer is
  // then false too. For a P that is not a lambda, it is the application
  // (P i) as an APPLY_UF.
  Node applied = applyFunction(P, i);
  return !applied.isNull() && rewritesToFalse(applied);
}

// For an aggregate A = ((_ table.aggr K) f i X) whose group columns K contain
// a key of X, the rows of the groups that some row of X reached; null for any
// other A. A key of X is a set of columns on which no two rows of X agree, a
// second copy of a row counting as another row (see rowKeys). The rows of one
// group agree on K, hence on that key, so every group is one row t of X, once,
// folded once from i to (f t i): the result is the map of X by
// (lambda ((t T)) (f t i)), with (f t i) beta-reduced, T the sort of X's rows.
// It is A except for an empty X: then table.group gives one empty group,
// folded to the row of initial values, so A is (bag i 1), which the map does
// not have. The callers use it where that row is dropped (see
// rejectsInitialRow). For X : (Bag (Tuple Int Int)) with the key {0},
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
//     (tuple 0 0)
//     X)
// gives
//   (bag.map (lambda ((t (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t)
//                     (+ ((_ tuple.select 1) (tuple 0 0)) 1)))
//            X)
// which the rewriter then simplifies to a map by
// (tuple ((_ tuple.select 0) t) 1), each group counting one row.
Node BagsRewriter::keyedAggregateRows(const Node& A) const
{
  // K: the group columns, the indices of the operator (_ table.aggr K). f: the
  // step, read as a lambda when the rewriter keeps it as a function array
  // constant (see asLambda).
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  Node f = asLambda(A[0]);
  // The rule needs some group column (an aggregate by no column has one group,
  // all of X, see AGGREGATE_NO_KEYS) and a step that is a lambda of a row and
  // an accumulator, so that (f t i) can be beta-reduced.
  if (K.empty() || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2)
  {
    return Node::null();
  }
  // keyed: whether some key of X, read off X's structure, lies inside K.
  std::set<uint32_t> grouped(K.begin(), K.end());
  bool keyed = false;
  for (const std::set<uint32_t>& key : rowKeys(A[2]))
  {
    bool inside = true;
    for (uint32_t c : key)
    {
      inside = inside && grouped.count(c) > 0;
    }
    keyed = keyed || inside;
  }
  if (!keyed)
  {
    return Node::null();
  }
  // (f t i): f's body with its accumulator variable f[0][1] replaced by i.
  // f's row variable t = f[0][0] stays and becomes the variable of the map's
  // lambda. Two rows with equal results give that result twice, in the map as
  // in A, since table.aggr maps the groups to their folds with bag.map.
  Node body = f[1].substitute(TNode(f[0][1]), TNode(A[1]));
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(f[0][0], body), A[2]);
}

BagsRewriteResponse BagsRewriter::rewriteFilterOfAggregate(const TNode& n) const
{
  // FILTER_AGGREGATE: a conjunct of p that reads only columns of the rows where
  // f copies a group column filters the groups by their keys, which is
  // filtering the rows of X by the same columns before grouping: every group is
  // kept or dropped whole (see rewrites.h). The conjuncts that stay must reject
  // the row of initial values i, as the test of the counter does
  // (see rejectsInitialRow): when no row of X passes the moved conjuncts, the
  // aggregate of the empty bag still has that row, (bag i 1), which the moved
  // conjuncts would have dropped.
  Node p = asLambda(n[0]);
  Node aggr = n[1];
  Node f = asLambda(aggr[0]);
  Node i = aggr[1];
  Node X = aggr[2];
  if (p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple()
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      aggr.getOperator().getConst<ProjectOp>().getIndices();
  std::set<uint32_t> keys(K.begin(), K.end());
  Node fx = f[0][0];
  // result position -> the key column of the row it copies
  std::map<uint32_t, uint32_t> copies;
  for (size_t q = 0, m = f[1].getNumChildren(); q < m; q++)
  {
    Node c = f[1][q];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == fx)
    {
      uint32_t column = datatypes::utils::indexOf(c.getOperator());
      if (keys.count(column))
      {
        copies[q] = column;
      }
    }
  }
  if (copies.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node r = p[0][0];
  std::vector<Node> conjuncts;
  if (p[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
  }
  else
  {
    conjuncts.push_back(p[1]);
  }
  std::vector<Node> onKeys, rest;
  for (const Node& c : conjuncts)
  {
    std::set<uint32_t> positions;
    bool keysOnly = readPositions(c, r, positions) && !bindsVariable(c, r);
    for (uint32_t pos : positions)
    {
      if (!copies.count(pos))
      {
        keysOnly = false;
      }
    }
    (keysOnly ? onKeys : rest).push_back(c);
  }
  if (onKeys.empty() || rest.empty()
      || !rejectsInitialRow(
          mkLambda(r,
                   rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::AND, rest)),
          i))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the predicate on a row of X: the result row whose key positions are the
  // row's key columns and whose other positions are the initial values, which
  // the conjuncts do not read
  TypeNode rowType = X.getType().getBagElementType();
  Node x = rowVariable(rowType);
  std::vector<Node> elems;
  for (size_t q = 0, m = f[1].getNumChildren(); q < m; q++)
  {
    std::map<uint32_t, uint32_t>::iterator it = copies.find(q);
    elems.push_back(
        it != copies.end()
            ? datatypes::TupleUtils::nthElementOfTuple(x, it->second)
            : i[q]);
  }
  Node row = datatypes::TupleUtils::constructTupleFromElements(
      r.getType(), elems, 0, elems.size() - 1);
  Node keysBody =
      onKeys.size() == 1 ? onKeys[0] : d_nm->mkNode(Kind::AND, onKeys);
  if (bindsVariable(keysBody, x) || (x != r && expr::hasSubterm(keysBody, x)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node onX = keysBody.substitute(TNode(r), TNode(row));
  Node filteredX = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(x, onX), X);
  std::vector<Node> children{aggr.getOperator(), f, i, filteredX};
  Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  if (!rest.empty())
  {
    Node restBody = rest.size() == 1 ? rest[0] : d_nm->mkNode(Kind::AND, rest);
    ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, restBody), ret);
  }
  return BagsRewriteResponse(ret, Rewrite::FILTER_AGGREGATE);
}

BagsRewriteResponse BagsRewriter::rewriteSortedKeys(const TNode& n) const
{
  // SORTED_KEYS: grouping partitions the rows by equality on the key
  // columns, so the order and repetitions of the keys in the operator do not
  // matter: keep them sorted and distinct, which makes two groupings by the
  // same columns equal,
  //   ((_ table.aggr 2 0 2) f i X) ---> ((_ table.aggr 0 2) f i X)
  //   ((_ table.group 1 0) X) ---> ((_ table.group 0 1) X)
  Assert(n.getKind() == Kind::TABLE_GROUP
         || n.getKind() == Kind::TABLE_AGGREGATE);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<uint32_t> sorted(indices.begin(), indices.end());
  std::sort(sorted.begin(), sorted.end());
  sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
  if (sorted == indices)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Kind opKind = n.getKind() == Kind::TABLE_GROUP ? Kind::TABLE_GROUP_OP
                                                 : Kind::TABLE_AGGREGATE_OP;
  Node op = d_nm->mkConst(opKind, ProjectOp(sorted));
  std::vector<Node> children{op};
  children.insert(children.end(), n.begin(), n.end());
  Node ret = d_nm->mkNode(n.getKind(), children);
  return BagsRewriteResponse(ret, Rewrite::SORTED_KEYS);
}

BagsRewriteResponse BagsRewriter::postRewriteGroup(const TNode& n) const
{
  // SORTED_KEYS, see rewriteSortedKeys
  Assert(n.getKind() == Kind::TABLE_GROUP);
  return rewriteSortedKeys(n);
}

// The bound variable that the rules use as the accumulator, the second
// variable, of the step of an aggregate or a fold that they build: one
// variable per sort S of the accumulator, so that two steps built the same way
// are one node. It is named accrow_N, N the id of the node
// (as bag.empty (Bag S)) that it is cached on. Like rowVariable, it comes from
// mkRewriterVar, here with the role "accumulator", which keeps it apart from
// the row variable of the same sort: for S = (Tuple Int Int) the accumulator
// is accrow_N and the row variable is row_N, with the same N, and they are
// two variables, so a lambda can bind both.
Node BagsRewriter::accumulatorVariable(TypeNode type) const
{
  // the key (as bag.empty (Bag S)) is a node that depends only on S
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(type)));
  return mkRewriterVar(
      d_nm, "accumulator", key, "accrow_" + std::to_string(key.getId()), type);
}

// The alpha key of the lambda f: a node that is the same for two lambdas that
// differ only in the names of their variables. It is f with every variable
// that f binds, at any depth, replaced by a placeholder for its binding depth
// (f's own variables are depths 0, 1, ..., and those of a lambda inside f
// come next), every variable free in f by one placeholder per sort, the
// arguments of commutative operators sorted and arithmetic atoms oriented
// (see alphaKeyScope). It does not change when a lambda inside f or around f
// renames its variables. The key is used only for its identity, as a cache
// key and by its node id, never as a term of the problem. The keys of
//   (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
//   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
// are one node, (lambda ((b0 (Tuple Int Int))) (> ((_ tuple.select 0) b0) 3))
// with the atom in the arithmetic rewriter's form, writing b0 for the
// placeholder of depth 0. A variable r free in f, such as the variable of an
// enclosing lambda, becomes the placeholder of its sort, so the key of
//   (lambda ((t (Tuple Int Int)))
//     (= ((_ tuple.select 0) t) ((_ tuple.select 0) r)))
// does not depend on the name of r either. Lambdas that read different free
// variables of one sort thus share a key, which only means that they get the
// same canonical names (see canonicalLambda). Keys are cached in d_alphaKeys.
Node BagsRewriter::alphaKey(const Node& f) const
{
  std::unordered_map<Node, Node>::iterator it = d_alphaKeys.find(f);
  if (it != d_alphaKeys.end())
  {
    return it->second;
  }
  // f is the outermost binder: no variable is bound around it, at depth 0
  std::unordered_map<TNode, Node> bound;
  Node key = alphaKeyScope(f, bound, 0);
  d_alphaKeys[f] = key;
  return key;
}

// The alpha key of root (see alphaKey), where root is the lambda whose key is
// computed or a part of it: bound maps the variables of the binders around
// root, inside that lambda, to their placeholders, and depth is the number of
// variables those binders bind, which is the depth that the next variable
// bound gets (both are empty and 0 for the lambda itself). A placeholder is a
// bound variable made by mkRewriterVar, one per role, number and sort, so the
// same depth and sort give the same node. For
//   (lambda ((s (Tuple Int Int)))
//     (bag.map (lambda ((u (Tuple Int Int)))
//                (tuple ((_ tuple.select 0) s) ((_ tuple.select 1) u)))
//              Y))
// the key is the same lambda with b0 for s and b1 for u, writing bk for the
// placeholder of depth k. The key of the inner lambda alone has b0 for u and,
// as s is free in it, the placeholder of the sort (Tuple Int Int) for s.
// Leaves that are not variables, such as Y, stay: lambdas that read different
// tables have different keys. The arguments of commutative operators are
// sorted, arithmetic atoms and ites over a negation are normalized, and the
// operator of a parameterized node is converted like an argument; the
// comments below say how each keeps the key the same when variables are
// renamed.
Node BagsRewriter::alphaKeyScope(TNode root,
                                 std::unordered_map<TNode, Node>& bound,
                                 size_t depth) const
{
  // The terms of one scope, each converted once, as the bodies of lambdas
  // share subterms. The terms under a binder inside root are converted by a
  // recursive call with its own cache, since more variables are bound there.
  std::unordered_map<TNode, Node> cache;
  // A traversal in post-order: a node is converted once its operator and its
  // children are.
  std::vector<TNode> todo{root};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    // A variable. When a binder around it binds it, it becomes that binder's
    // placeholder for it. Otherwise it is free in the lambda whose key is
    // computed (for instance the variable of an enclosing lambda) and becomes
    // the one placeholder of its sort, so that the key does not depend on its
    // name either.
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      std::unordered_map<TNode, Node>::iterator b = bound.find(n);
      if (b != bound.end())
      {
        cache[n] = b->second;
      }
      else
      {
        // the free placeholder of this sort: role "alpha-free", number 0
        Node zero = d_nm->mkConstInt(Rational(0));
        cache[n] = mkRewriterVar(d_nm, "alpha-free", zero, n.getType());
      }
      todo.pop_back();
      continue;
    }
    // Any other leaf, such as a constant or a declared constant like a table,
    // is its own key.
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    if (n.isClosure())
    {
      // A binder, such as a lambda. A lambda of the variables s and acc at
      // depth d becomes the lambda of the placeholders b_d and b_d+1, and its
      // body is converted in the scope of those placeholders, by a recursive
      // call at depth d + 2. The binder is converted at once, not after its
      // children as the other nodes are.
      todo.pop_back();
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> vars;
      std::vector<std::pair<TNode, Node>> saved;
      for (size_t i = 0; i < nvars; i++)
      {
        TNode v = n[0][i];
        // the bound placeholder of depth depth + i: role "alpha-bound"
        Node index = d_nm->mkConstInt(Rational(depth + i));
        Node p = mkRewriterVar(d_nm, "alpha-bound", index, v.getType());
        // A binder around this one may bind v too, which this one shadows:
        // save the placeholder it gave v, to restore it after the body.
        std::unordered_map<TNode, Node>::iterator b = bound.find(v);
        saved.push_back({v, b != bound.end() ? b->second : Node::null()});
        bound[v] = p;
        vars.push_back(p);
      }
      // the binder's operator, if it has one, is kept as is
      std::vector<Node> children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      children.push_back(d_nm->mkNode(Kind::BOUND_VAR_LIST, vars));
      // the children after the variable list: the body, and for a quantifier
      // its patterns, if any
      for (size_t i = 1, nc = n.getNumChildren(); i < nc; i++)
      {
        children.push_back(alphaKeyScope(n[i], bound, depth + nvars));
      }
      // restore bound to what it was around this binder
      for (const std::pair<TNode, Node>& s : saved)
      {
        if (s.second.isNull())
        {
          bound.erase(s.first);
        }
        else
        {
          bound[s.first] = s.second;
        }
      }
      cache[n] = d_nm->mkNode(n.getKind(), children);
      continue;
    }
    // Any other node. The operator of a parameterized node (as of an
    // APPLY_UF, a selector or a constructor application) is converted like
    // its arguments, since it can be a bound variable: in
    // (lambda ((f (-> Int Int))) (f 0)), f is the operator of (f 0). A
    // selector or a constructor is a leaf and stays.
    bool parameterized = n.getMetaKind() == kind::metakind::PARAMETERIZED;
    Node op = parameterized ? n.getOperator() : Node::null();
    // convert the operator and the children first, if not yet done; n stays
    // on todo and is converted when the traversal comes back to it
    bool ready = true;
    if (parameterized && !cache.count(op))
    {
      todo.push_back(op);
      ready = false;
    }
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // n over its converted operator and children. changed records whether
    // any of them differs from the original: when none does, n is its own
    // key and no node is built. The operator must count: in (f 0) above only
    // the operator changes, and keeping n would leave the name of f in the
    // key. A key that holds the name of a variable that a lambda binds
    // changes each time canonicalLambda renames that variable, so the renamed
    // lambda would get a new key, hence new names, and so on: the rewriter
    // would never reach a fixed point.
    std::vector<Node> children;
    bool changed = false;
    if (parameterized)
    {
      children.push_back(cache[op]);
      changed = cache[op] != op;
    }
    // first: the index of the first argument, after the operator if any
    size_t first = children.size();
    for (const Node& c : n)
    {
      Node cc = cache[c];
      changed = changed || cc != c;
      children.push_back(cc);
    }
    switch (n.getKind())
    {
      // Commutative operators. The rewriter sorts their arguments by node id,
      // and renaming a variable gives the arguments that read it other ids,
      // so after a renaming the rewriter may put them in another order. The
      // key sorts the converted arguments, which do not depend on the names,
      // so that both orders have one key. changed is set so that the sorted
      // order is used even when no argument changed.
      case Kind::EQUAL:
      case Kind::DISTINCT:
      case Kind::AND:
      case Kind::OR:
      case Kind::XOR:
      case Kind::ADD:
      case Kind::MULT:
      case Kind::NONLINEAR_MULT:
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      case Kind::BAG_INTER_MIN:
        std::sort(children.begin() + first, children.end());
        changed = true;
        break;
      default: break;
    }
    Node built = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
    Kind k = n.getKind();
    auto atom = [](Kind a) {
      return a == Kind::GEQ || a == Kind::GT || a == Kind::LEQ || a == Kind::LT;
    };
    if (d_rewriter != nullptr
        && (atom(k)
            || (k == Kind::NOT && built.getKind() == Kind::NOT
                && (atom(built[0].getKind())
                    || built[0].getKind() == Kind::NOT))))
    {
      // An arithmetic atom (>=, >, <= or <), or a negation whose converted
      // argument is an atom or a negation. The arithmetic rewriter writes an
      // atom in a normal form oriented by the order of the terms it reads,
      // which is by node id: for integers a and b, (>= (- a b) 0) and
      // (not (>= (- b a) 1)) say the same, and which of them it writes depends
      // on whether a or b comes first. Renaming a lambda's variables can thus
      // flip the form. Here the converted atom, over the placeholders, is
      // rewritten, so that the two forms have one key. A negation is
      // rewritten too, since the rewriting of the atom inside it may have
      // negated it again, giving (not (not c)). The rewriter rewrites the
      // whole atom, any term inside it included; the result still depends
      // only on the converted atom.
      built = d_rewriter->rewrite(built);
    }
    if (k == Kind::ITE && built.getKind() == Kind::ITE
        && built[0].getKind() == Kind::NOT)
    {
      // (ite (not c) a b) is (ite c b a), and the Boolean rewriter writes it
      // so. The converted condition may be a negation that the lambda's own
      // ite did not have, when the rewriting of an atom above negated it, so
      // the key flips the ite too: both forms have one key.
      built = d_nm->mkNode(Kind::ITE, built[0][0], built[2], built[1]);
    }
    cache[n] = built;
  }
  return cache[root];
}

// body with every subterm (ite (= a b) b a) replaced by a, and every
// (ite (= a b) a b) by b, at any depth, under binders too. Both are sound:
// the result is the else branch, and when a = b the then branch has the same
// value. The null-aware steps that sqleq's translator writes for SQL
// aggregates leave such ites once an accumulator is known, for instance the
// step of a minimum,
//   (ite (= (as nullable.null (Nullable Int)) acc) a (ite ...))
// with acc the accumulator column of a, the one that holds its minimum. For
// t : (Tuple Int Int),
//   (ite (= ((_ tuple.select 0) t) ((_ tuple.select 1) t))
//        ((_ tuple.select 1) t)
//        ((_ tuple.select 0) t))
// becomes ((_ tuple.select 0) t).
Node BagsRewriter::simplifyIteSame(const Node& body) const
{
  // A traversal in post-order: a node is simplified after its children, and
  // each distinct subterm once.
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{body};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    // a leaf stays
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    // simplify the children first; n stays on todo until they are done
    bool ready = true;
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // m: n over its simplified children, or n itself when none changed. The
    // operator of a parameterized node is kept as it is, not simplified.
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      changed = changed || cache[c] != c;
      children.push_back(cache[c]);
    }
    Node m = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
    // m = (ite (= a b) x y): replaced by a when x is b and y is a, by b when
    // x is a and y is b. The result is a part of m's condition, which is
    // simplified already, and m's parent is checked with this result, so one
    // pass leaves no such ite, except in the operators kept as they are.
    if (m.getKind() == Kind::ITE && m[0].getKind() == Kind::EQUAL)
    {
      const Node& a = m[0][0];
      const Node& b = m[0][1];
      if (m[1] == b && m[2] == a)
      {
        m = a;
      }
      else if (m[1] == a && m[2] == b)
      {
        m = b;
      }
    }
    cache[n] = m;
  }
  return cache[body];
}

// CANONICAL_VARIABLE: the lambda f with its variables renamed to canonical
// ones, named after f's alpha key (see alphaKey: a node that is the same for
// lambdas that differ only in the names of their variables). With N the node
// id of the key, the variable of a lambda of one variable, as of a filter or
// a map, is renamed to t_N, and the two of a lambda of two, as of a fold or
// an aggregate, to t_N and acc_N. Lambdas that differ only in the names of
// their variables thus become one node, which the solver purifies into one
// function symbol (see rewrites.h). For X : (Bag (Tuple Int Int)),
//   (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3)) X)
//   ---> (bag.filter
//          (lambda ((t_N (Tuple Int Int))) (> ((_ tuple.select 0) t_N) 3))
//          X)
// and the same filter over a variable t instead of s gives the same term,
// for the same N. First, f's body is simplified (see simplifyIteSame), so that
// (ite (= a b) b a) in it is a. Two lambdas one inside the other have
// different keys, as the key of the outer one holds the converted inner one,
// so canonical names never shadow each other. The key does not change when a
// lambda inside or around f is renamed, so renaming terminates.
Node BagsRewriter::canonicalLambda(const Node& f) const
{
  Assert(f.getKind() == Kind::LAMBDA);
  {
    // Simplify the body first, then canonicalize the simplified lambda, so
    // that the key and the names come from the simplified body. The body of
    // that lambda has nothing left to simplify, so the recursion stops there.
    Node simpler = simplifyIteSame(f[1]);
    if (simpler != f[1])
    {
      return canonicalLambda(d_nm->mkNode(Kind::LAMBDA, f[0], simpler));
    }
  }
  size_t arity = f[0].getNumChildren();
  std::vector<Node> vars(f[0].begin(), f[0].end());
  Node key = alphaKey(f);
  // The canonical variable of position k: the bound variable that the
  // BoundVarManager gives for the id BAGS_FIRST_INDEX, the cache node
  // (SEXPR "canonical" (SEXPR key k)) and the sort of f's k-th variable (see
  // mkRewriterVar). The manager returns one variable per id, cache node and
  // sort, so two lambdas with one key get the same canonical variables. The
  // role "canonical" keeps them apart from the row, accumulator and
  // placeholder variables, which have other roles, and the bag reductions,
  // the other users of BAGS_FIRST_INDEX, cache on the bag terms they reduce,
  // never on an SEXPR. This gives one node per class of lambdas that differ
  // only in the names of their variables: such lambdas get the same
  // variables, and renaming makes their bodies one node, since the lambdas
  // inside them have been rewritten first and are canonical already.
  std::vector<Node> canonical;
  for (size_t k = 0; k < arity; k++)
  {
    Node cache = d_nm->mkNode(Kind::SEXPR, key, d_nm->mkConstInt(Rational(k)));
    // Named apart: the name holds N, so canonical variables of different keys
    // print with different names. A printed problem binds by name, and if a
    // lambda and a variable free in it had one name, the printed lambda would
    // capture that variable. Every position after the first is named acc_N;
    // the callers pass lambdas of at most two variables.
    std::string name = (k == 0 ? "t_" : "acc_") + std::to_string(key.getId());
    canonical.push_back(
        mkRewriterVar(d_nm, "canonical", cache, name, vars[k].getType()));
  }
  // f is canonical already: the fixed point. The rewriter rewrites the
  // renamed lambda again, which may reorder the arguments or orient the atoms
  // in its body by the ids of the new variables; the key is built to stay
  // the same under these changes (see alphaKeyScope), so the rewritten
  // lambda gets the same canonical variables and ends here.
  if (canonical == vars)
  {
    return f;
  }
  // A canonical variable that is not the variable it replaces occurs in the
  // body already, free in it or bound by a lambda inside it: renaming would
  // capture it or merge it with f's variable, so f is left as it is. This
  // keeps the renaming sound even if the keys above did not keep the names
  // apart.
  Node body = f[1];
  for (size_t k = 0; k < arity; k++)
  {
    if (canonical[k] != vars[k] && expr::hasSubterm(body, canonical[k]))
    {
      return f;
    }
  }
  // rename all the variables at once and bind the canonical ones
  Node newBody = body.substitute(
      vars.begin(), vars.end(), canonical.begin(), canonical.end());
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, canonical), newBody);
}

// AGGREGATE_SORT_OUTPUT: for n = ((_ table.aggr K) f i X), puts the columns
// of the aggregate's rows in one canonical order, under a bag.map that puts
// them back in their old order. Two aggregates that compute the same columns
// in different orders then become one aggregate under two different maps.
// Here f = (lambda ((t R) (acc T)) (tuple e_0 .. e_(m-1))), with t : R a row
// of X and acc : T the accumulator, and column q of the result is computed by
// e_q from the initial value i_q. The columns that copy a group column of t
// (a column of X that the aggregate groups its rows by, one of K) come first,
// ordered by that column; the other columns follow, ordered by what they
// compute when each e_q reads no column of acc but its own, and otherwise
// left in their order.
// For X : (Bag (Tuple Int Int)),
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t))
//              ((_ tuple.select 0) t)))
//     (tuple 0 0) X)
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
//          ((_ table.aggr 0)
//            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t)
//                     (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
//            (tuple 0 0) X))                       (AGGREGATE_SORT_OUTPUT)
BagsRewriteResponse BagsRewriter::rewriteAggregateSortOutput(
    const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
  // f must be a lambda of the row and the accumulator whose body is a tuple
  // (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as many
  // components: the rule permutes the components of both
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple()
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      n.getOperator().getConst<ProjectOp>().getIndices();
  std::set<uint32_t> keys(K.begin(), K.end());
  // x is the row t of X, y the old accumulator acc
  Node x = f[0][0];
  Node y = f[0][1];
  size_t m = f[1].getNumChildren();
  // Each column q gets a sort key (class, rank). Class 0 holds the copies of
  // group columns, ((_ tuple.select k) x) with k in K, ranked by k. Class 1
  // holds the other columns. These are ranked by what they compute (the alpha
  // key of their step and their initial value) when every e_q is
  // independent, that is, reads no column of y but its own column q: then
  // e_q with i_q is a computation of its own, which looks the same at any
  // position. Otherwise they are ranked by position, keeping their order.
  // readPositions fails when e_q reads y other than through a selector.
  bool independent = true;
  for (uint32_t q = 0; q < m && independent; q++)
  {
    std::set<uint32_t> pos;
    independent = readPositions(f[1][q], y, pos) && pos.size() <= 1
                  && (pos.empty() || pos.count(q));
  }
  std::vector<std::pair<std::pair<int, uint64_t>, uint32_t>> order;
  for (uint32_t q = 0; q < m; q++)
  {
    Node c = f[1][q];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == x
        && keys.count(datatypes::utils::indexOf(c.getOperator())))
    {
      // e_q = ((_ tuple.select k) x), a copy of the group column k: every
      // row of a group has the same value there. Class 0, ranked by k
      order.push_back({{0, datatypes::utils::indexOf(c.getOperator())}, q});
    }
    else if (independent)
    {
      // ranked by what e_q computes: the alpha key (see alphaKey) of the
      // step (lambda ((x R) (v S)) e_q), with its own column
      // ((_ tuple.select q) y) read as a fresh variable v of its sort S,
      // together with i_q.
      // This key does not depend on q or on the names of the variables. The
      // rank is the id of the node (SEXPR key i_q): an arbitrary order, but
      // the same rank for the same column of any other aggregate, since that
      // column gives the same node
      Node own = datatypes::TupleUtils::nthElementOfTuple(y, q);
      Node v = NodeManager::mkBoundVar("v", own.getType());
      Node step = d_nm->mkNode(Kind::LAMBDA,
                               {d_nm->mkNode(Kind::BOUND_VAR_LIST, x, v),
                                c.substitute(TNode(own), TNode(v))});
      Node key = d_nm->mkNode(Kind::SEXPR, alphaKey(step), i[q]);
      order.push_back({{1, key.getId()}, q});
    }
    else
    {
      // some e_p reads a column of y other than its own: ranked by position
      order.push_back({{1, q}, q});
    }
  }
  // stable, so columns with equal sort keys, as two copies of one group
  // column, keep their order
  std::stable_sort(order.begin(), order.end());
  std::vector<uint32_t> sigma;  // new position -> old position
  bool identity = true;
  for (uint32_t q = 0; q < m; q++)
  {
    sigma.push_back(order[q].second);
    identity = identity && order[q].second == q;
  }
  if (identity)
  {
    // the columns are in order already; in particular the rule does not
    // apply again to its own result
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<uint32_t> inverse(m);  // old position -> new position
  for (uint32_t q = 0; q < m; q++)
  {
    inverse[sigma[q]] = q;
  }
  // newType, the sort of the sorted rows: the column sorts permuted by sigma
  TypeNode oldType = f[1].getType();
  std::vector<TypeNode> types;
  for (uint32_t q = 0; q < m; q++)
  {
    types.push_back(oldType.getTupleTypes()[sigma[q]]);
  }
  TypeNode newType = d_nm->mkTupleType(types);
  // acc, the new accumulator, is the rewriter's variable for accumulators of
  // newType. It must not be the row variable x, nor occur in the body unless
  // it is y itself, which the substitution below replaces
  Node acc = accumulatorVariable(newType);
  if (acc == x || (acc != y && expr::hasSubterm(f[1], acc)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // The old accumulator expressed through the new one: old column p is new
  // column inverse[p], so it is the tuple of the ((_ tuple.select inverse[p])
  // acc); in the example above, (tuple ((_ tuple.select 1) acc)
  // ((_ tuple.select 0) acc)). With it for y, the body reads the sorted
  // accumulator
  std::vector<Node> oldAcc;
  for (uint32_t p = 0; p < m; p++)
  {
    oldAcc.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, inverse[p]));
  }
  Node unsortedAcc = datatypes::TupleUtils::constructTupleFromElements(
      oldType, oldAcc, 0, m - 1);
  Node body = f[1].substitute(TNode(y), TNode(unsortedAcc));
  // Column q of the new step and of the new initial value is column sigma[q]
  // of the old ones. Over the rows of a group, the new accumulator is then
  // always the old one with its columns sorted, so the new fold computes the
  // sorted rows of the old one
  std::vector<Node> newElems, newInit;
  for (uint32_t q = 0; q < m; q++)
  {
    newElems.push_back(body[sigma[q]]);
    newInit.push_back(i[sigma[q]]);
  }
  Node newBody = datatypes::TupleUtils::constructTupleFromElements(
      newType, newElems, 0, m - 1);
  Node newI = datatypes::TupleUtils::constructTupleFromElements(
      newType, newInit, 0, m - 1);
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc), newBody);
  // the same operator, so the same group columns K of X: the order of the
  // output columns does not change the groups
  std::vector<Node> children{n.getOperator(), lambda, newI, X};
  Node sortedAggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  // The map that puts the columns back: column p of an old row is column
  // inverse[p] of the row r of the sorted aggregate. It is a bijection
  // between the two row sorts, so the bag.map keeps every multiplicity
  Node r = rowVariable(newType);
  std::vector<Node> back;
  for (uint32_t p = 0; p < m; p++)
  {
    back.push_back(datatypes::TupleUtils::nthElementOfTuple(r, inverse[p]));
  }
  Node unsort = mkLambda(r,
                         datatypes::TupleUtils::constructTupleFromElements(
                             oldType, back, 0, m - 1));
  Node ret = d_nm->mkNode(Kind::BAG_MAP, unsort, sortedAggr);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_SORT_OUTPUT);
}

// FOLD_TUPLE: for n = (bag.fold f i X) with a tuple accumulator, splits the
// fold into the tuple of one fold per component. This needs f =
// (lambda ((t E) (acc T)) (tuple e_0 .. e_(m-1))), t : E an element of X and
// acc : T the accumulator, with each e_k reading acc only through its own
// component ((_ tuple.select k) acc). Fold k then has the step e_k, with that
// component read as an accumulator a of its own, and starts from component k
// of i.
// The folds over X read its elements in one order, so each component of the
// old accumulator is, after every element, the accumulator of its own fold.
// For X : (Bag (Tuple Int)),
//   (bag.fold (lambda ((t (Tuple Int)) (acc (Tuple Int Int)))
//               (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t))
//                      (+ ((_ tuple.select 1) acc) 1)))
//             (tuple 0 0) X)
//   ---> (tuple (bag.fold (lambda ((t (Tuple Int)) (a Int))
//                           (+ a ((_ tuple.select 0) t)))
//                         0 X)
//               (bag.fold (lambda ((t (Tuple Int)) (a Int)) (+ a 1)) 0 X))
//                                                            (FOLD_TUPLE)
// that is, the sum and the count of the rows of X.
BagsRewriteResponse BagsRewriter::rewriteFoldOfTuple(const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
  // f must be a lambda of the element and the accumulator whose body builds a
  // tuple, (tuple e_0 .. e_(m-1)), so that its components can be split
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  Node body = f[1];
  size_t m = body.getNumChildren();
  if (m == 0)
  {
    // the empty tuple has no component to fold
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // components[k] is the fold of e_k
  std::vector<Node> components;
  for (size_t k = 0; k < m; k++)
  {
    // e_k must read acc only through selectors, ((_ tuple.select p) acc),
    // never whole, and no lambda inside e_k may bind acc again (a read of
    // that inner variable is no read of the accumulator)
    std::set<uint32_t> positions;
    if (!readPositions(body[k], acc, positions) || bindsVariable(body[k], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // and only its own component, p = k; it may also read none
    for (uint32_t pos : positions)
    {
      if (pos != k)
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
    // a, the accumulator of fold k, is the rewriter's variable for
    // accumulators of the sort of e_k. It must not be the element variable
    // x, nor occur in e_k already, or the substitution below would mix it up
    // with the occurrences there
    TypeNode type = body[k].getType();
    Node a = accumulatorVariable(type);
    if (a == x || expr::hasSubterm(body[k], a))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // the step of fold k: e_k with ((_ tuple.select k) acc) read as a; the
    // checks above leave no other occurrence of acc, and this one makes sure
    Node selected = datatypes::TupleUtils::nthElementOfTuple(acc, k);
    Node step = body[k].substitute(TNode(selected), TNode(a));
    if (expr::hasSubterm(step, acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // (bag.fold (lambda ((x E) (a S)) step) i_k X), S the sort of e_k and
    // i_k component k of i: i[k] when i is a tuple (tuple i_0 ..), else
    // ((_ tuple.select k) i)
    Node lambda = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, a), step);
    Node seed = datatypes::TupleUtils::nthElementOfTuple(i, k);
    components.push_back(d_nm->mkNode(Kind::BAG_FOLD, lambda, seed, X));
  }
  Node ret = datatypes::TupleUtils::constructTupleFromElements(
      n.getType(), components, 0, m - 1);
  return BagsRewriteResponse(ret, Rewrite::FOLD_TUPLE);
}

BagsRewriteResponse BagsRewriter::rewriteProductOfBagMake(const TNode& n,
                                                          size_t side) const
{
  // PRODUCT_BAG_MAKE: a product with a single row e, present once or when b
  // holds, is a map of the other factor that appends e, under a filter by b
  // when there is one; b and e do not read the rows of A (see rewrites.h). The
  // map is injective, and each row of A meets the one row e, once if b; with
  // side 0 the bag is the left factor and e comes first.
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node m = n[side];
  Node A = n[1 - side];
  if (m.getKind() != Kind::BAG_MAKE)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node c = m[1];
  Node cond;
  if (c.isConst())
  {
    if (!c.getConst<Rational>().isOne())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  else if (c.getKind() == Kind::ITE && c[1].isConst() && c[2].isConst())
  {
    const Rational& r1 = c[1].getConst<Rational>();
    const Rational& r2 = c[2].getConst<Rational>();
    if (r1.isOne() && r2.isZero())
    {
      cond = c[0];
    }
    else if (r1.isZero() && r2.isOne())
    {
      cond = c[0].notNode();
    }
    else
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  else
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode aType = A.getType().getBagElementType();
  TypeNode eType = m[0].getType();
  if (!aType.isTuple() || !eType.isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node t = rowVariable(aType);
  if (occursFree(m[0], t) || (!cond.isNull() && occursFree(cond, t)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode rowType = n.getType().getBagElementType();
  Node first = side == 1 ? t : m[0];
  Node second = side == 1 ? m[0] : t;
  std::vector<Node> elems;
  for (size_t k = 0, w = first.getType().getTupleLength(); k < w; k++)
  {
    elems.push_back(datatypes::TupleUtils::nthElementOfTuple(first, k));
  }
  for (size_t k = 0, w = second.getType().getTupleLength(); k < w; k++)
  {
    elems.push_back(datatypes::TupleUtils::nthElementOfTuple(second, k));
  }
  if (elems.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node row = datatypes::TupleUtils::constructTupleFromElements(
      rowType, elems, 0, elems.size() - 1);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, row), A);
  if (!cond.isNull())
  {
    Node r = rowVariable(rowType);
    if (occursFree(cond, r))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, cond), ret);
  }
  return BagsRewriteResponse(ret, Rewrite::PRODUCT_BAG_MAKE);
}

// SETOF_PROJECTION_SORT: for n = (bag.setof (bag.map f Y)), where f maps a
// row t of Y to a tuple of its columns ((_ tuple.select j) t) that are not
// in strictly increasing order of j (out of order, or a column twice),
// returns the set of the projection onto those columns sorted, each once,
// under a bag.map that puts them back in f's order. That map is injective,
// so it commutes with removing duplicates.
// Queries that select the same columns of Y in different orders then share
// one set term. For Y : (Bag (Tuple Int Int Int)),
//   (bag.setof
//     (bag.map (lambda ((t (Tuple Int Int Int)))
//                (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
//              Y))
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
//          (bag.setof
//            (bag.map (lambda ((t (Tuple Int Int Int)))
//                       (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
//                     Y)))                          (SETOF_PROJECTION_SORT)
BagsRewriteResponse BagsRewriter::rewriteSetofOfMap(const TNode& n) const
{
  // SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, the set of a map
  // (see rewrites.h):
  // * for f a constant c, the bag of c, once when Y is not empty;
  // * for f a projection onto columns in another order than theirs, the set of
  //   the projection onto the sorted columns, under a map that puts them back,
  //   which is injective and so commutes with removing duplicates;
  // * for f a tuple some of whose components are constants, the set of the
  //   other components, under an injective map that puts the constants back.
  // n = (bag.setof (bag.map f Y)), with f read as a lambda of one variable,
  // a row t of Y, even when it is kept as a function constant
  Node f = asLambda(n[0][0]);
  Node Y = n[0][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node var = f[0][0];
  Node body = f[1];
  if (!occursFree(body, var))
  {
    Node empty = d_nm->mkConst(EmptyBag(Y.getType()));
    Node count = d_nm->mkNode(Kind::ITE, Y.eqNode(empty), d_zero, d_one);
    Node ret = d_nm->mkNode(Kind::BAG_MAKE, body, count);
    return BagsRewriteResponse(ret, Rewrite::SETOF_MAP_CONSTANT);
  }
  // f's body must be written as a tuple, (tuple e_0 .. e_(k-1))
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  {
    // J: the columns f selects, in f's order, as [2, 0] in the example
    // above; empty when some e_k is not a column ((_ tuple.select j) t)
    std::vector<uint32_t> J = projectionIndices(f);
    if (!J.empty())
    {
      // sorted: the columns of J in increasing order, each once, as [0, 2].
      // It differs from J when J is out of order or has a column twice
      std::vector<uint32_t> sorted = J;
      std::sort(sorted.begin(), sorted.end());
      sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
      if (sorted != J)
      {
        // g, the projection onto the sorted columns, and inner =
        // (bag.setof (bag.map g Y)); in the example, g is
        //   (lambda ((t (Tuple Int Int Int)))
        //     (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
        TypeNode rowType = Y.getType().getBagElementType();
        std::vector<Node> cols;
        std::vector<TypeNode> types;
        for (uint32_t j : sorted)
        {
          cols.push_back(datatypes::TupleUtils::nthElementOfTuple(var, j));
          types.push_back(rowType.getTupleTypes()[j]);
        }
        TypeNode sortedType = d_nm->mkTupleType(types);
        Node g = mkLambda(var,
                          datatypes::TupleUtils::constructTupleFromElements(
                              sortedType, cols, 0, cols.size() - 1));
        Node inner =
            d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, g, Y));
        // unsort, the map back to f's order, for r a row of inner: its
        // component k is column j = J[k] of t, which is component at of r,
        // the position of j in sorted; in the example, (tuple
        // ((_ tuple.select 1) r) ((_ tuple.select 0) r)). f is g followed by
        // unsort. unsort reads every component of r, so it is injective, and
        // maps a set to a set: the set of (bag.map unsort (bag.map g Y)) is
        // (bag.map unsort (bag.setof (bag.map g Y)))
        Node r = rowVariable(sortedType);
        std::vector<Node> back;
        for (uint32_t j : J)
        {
          size_t at = std::lower_bound(sorted.begin(), sorted.end(), j)
                      - sorted.begin();
          back.push_back(datatypes::TupleUtils::nthElementOfTuple(r, at));
        }
        Node unsort =
            mkLambda(r,
                     datatypes::TupleUtils::constructTupleFromElements(
                         body.getType(), back, 0, back.size() - 1));
        Node ret = d_nm->mkNode(Kind::BAG_MAP, unsort, inner);
        return BagsRewriteResponse(ret, Rewrite::SETOF_PROJECTION_SORT);
      }
    }
  }
  std::vector<Node> kept;
  std::vector<TypeNode> keptTypes;
  std::vector<int> where;  // component -> position among the kept ones, or -1
  for (const Node& c : body)
  {
    if (occursFree(c, var))
    {
      where.push_back(static_cast<int>(kept.size()));
      kept.push_back(c);
      keptTypes.push_back(c.getType());
    }
    else
    {
      where.push_back(-1);
    }
  }
  if (kept.size() == body.getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode keptType = d_nm->mkTupleType(keptTypes);
  Node g = mkLambda(var,
                    datatypes::TupleUtils::constructTupleFromElements(
                        keptType, kept, 0, kept.size() - 1));
  Node inner = d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, g, Y));
  Node r = rowVariable(keptType);
  std::vector<Node> cells;
  for (size_t k = 0; k < body.getNumChildren(); k++)
  {
    if (where[k] < 0)
    {
      if (occursFree(body[k], r))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      cells.push_back(body[k]);
    }
    else
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(r, where[k]));
    }
  }
  Node back = mkLambda(r,
                       datatypes::TupleUtils::constructTupleFromElements(
                           body.getType(), cells, 0, cells.size() - 1));
  Node ret = d_nm->mkNode(Kind::BAG_MAP, back, inner);
  return BagsRewriteResponse(ret, Rewrite::SETOF_MAP_CONSTANT);
}

BagsRewriteResponse BagsRewriter::rewriteSemiJoin(const TNode& n,
                                                  size_t side) const
{
  // SEMI_JOIN, for
  // (bag.map f (bag.filter p (table.product X0 (table.product X1 ..)))) with a
  // component B = Xj that is a set, a bag.setof or a table with a key, whose
  // rows are distinct; f reading none of its columns, or only columns that p
  // equates to columns of the others; and p having, for every column of B or
  // for every column of a key of B, a conjunct (= ((_ tuple.select c) t) e)
  // with e reading no column of B: a row of the other components meets at most
  // one row of B that passes, so the product passes each of their rows once
  // when one does (see rewrites.h). The result is the product A of the other
  // components, filtered by pA, the conjuncts reading no column of B, and by
  // the existence of a row of B that passes pAB, the others: the shape of SQL's
  // EXISTS and IN, which other rules decorrelate (see rewriteEmptyFilter).
  // Called with side 0 only; every component is tried, the one with the
  // smallest node first, so that one join written in two orders is rewritten
  // alike.
  if (side != 0)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node f = asLambda(n[0]);
  Node p = asLambda(n[1][0]);
  Node prod = n[1][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1
      || p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the components, left to right, and where each one's columns start
  std::vector<Node> comps;
  Node rest = prod;
  while (rest.getKind() == Kind::TABLE_PRODUCT)
  {
    comps.push_back(rest[0]);
    rest = rest[1];
  }
  comps.push_back(rest);
  std::vector<size_t> starts, widths;
  size_t at = 0;
  for (const Node& c : comps)
  {
    TypeNode t = c.getType().getBagElementType();
    if (!t.isTuple())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    starts.push_back(at);
    widths.push_back(t.getTupleLength());
    at += t.getTupleLength();
  }
  Node ft = f[0][0];
  Node pt = p[0][0];
  std::set<uint32_t> fPositions;
  if (!readPositions(f[1], ft, fPositions) || bindsVariable(f[1], ft)
      || bindsVariable(p[1], pt))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> conjuncts;
  if (p[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
  }
  else
  {
    conjuncts.push_back(p[1]);
  }
  std::vector<std::set<uint32_t>> reads(conjuncts.size());
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (!readPositions(conjuncts[k], pt, reads[k]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // the component to join away: of those that qualify, the one with the
  // smallest node, so that one join written in two orders is rewritten alike
  std::vector<size_t> order(comps.size());
  for (size_t k = 0; k < order.size(); k++)
  {
    order[k] = k;
  }
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return comps[a].getId() < comps[b].getId();
  });
  for (size_t j : order)
  {
    Node B = comps[j];
    std::vector<std::set<uint32_t>> keys = keysOf(B);
    if (B.getType().getBagElementType().isTuple())
    {
      std::vector<std::set<uint32_t>> more = rowKeys(B);
      keys.insert(keys.end(), more.begin(), more.end());
    }
    if (!isSet(B) && keys.empty())
    {
      continue;
    }
    size_t bStart = starts[j], wb = widths[j];
    auto inB = [&](uint32_t pos) { return pos >= bStart && pos < bStart + wb; };
    std::vector<Node> onA, onAB;
    std::set<uint32_t> determined;
    // a column of B that an equation sets equal to a column of the others
    std::map<uint32_t, uint32_t> aliases;
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      const Node& c = conjuncts[k];
      bool readsB = false;
      for (uint32_t pos : reads[k])
      {
        readsB = readsB || inB(pos);
      }
      (readsB ? onAB : onA).push_back(c);
      if (!readsB || c.getKind() != Kind::EQUAL)
      {
        continue;
      }
      for (size_t sd = 0; sd < 2; sd++)
      {
        Node col = c[sd];
        std::set<uint32_t> other;
        if (col.getKind() == Kind::APPLY_SELECTOR && col[0] == pt
            && readPositions(c[1 - sd], pt, other))
        {
          uint32_t pos = datatypes::utils::indexOf(col.getOperator());
          bool fromRest = inB(pos);
          for (uint32_t o : other)
          {
            fromRest = fromRest && !inB(o);
          }
          if (fromRest)
          {
            determined.insert(pos - bStart);
            Node e = c[1 - sd];
            if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == pt)
            {
              aliases[pos] = datatypes::utils::indexOf(e.getOperator());
            }
          }
        }
      }
    }
    // f reads B only through columns equal to columns of the others, aliases
    // maps such a column of B to that column of the others
    bool fReadsB = false;
    for (uint32_t pos : fPositions)
    {
      fReadsB = fReadsB || (inB(pos) && !aliases.count(pos));
    }
    if (fReadsB)
    {
      continue;
    }
    bool fixesRow = determined.size() == wb;
    for (const std::set<uint32_t>& key : keys)
    {
      bool all = true;
      for (uint32_t c : key)
      {
        all = all && determined.count(c) > 0;
      }
      fixesRow = fixesRow || all;
    }
    if (onAB.empty() || !fixesRow)
    {
      continue;
    }
    // A: the product of the other components, right-nested in their order
    std::vector<Node> others;
    for (size_t k = 0; k < comps.size(); k++)
    {
      if (k != j)
      {
        others.push_back(comps[k]);
      }
    }
    Node A = others.back();
    for (size_t k = others.size() - 1; k-- > 0;)
    {
      A = d_nm->mkNode(Kind::TABLE_PRODUCT, others[k], A);
    }
    TypeNode aType = A.getType().getBagElementType();
    TypeNode bType = B.getType().getBagElementType();
    // a, the rows of A, and b, the rows of B: two variables even when A and
    // B have one row sort
    Node a = rowVariable(aType);
    Node b = aType == bType ? accumulatorVariable(bType) : rowVariable(bType);
    if (expr::hasSubterm(p[1], a) || expr::hasSubterm(p[1], b)
        || expr::hasSubterm(f[1], a))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // a column of the whole row, read from a or from b
    std::vector<Node> from, to;
    size_t aPos = 0;
    for (size_t k = 0; k < comps.size(); k++)
    {
      for (size_t c = 0; c < widths[k]; c++)
      {
        Node whole =
            datatypes::TupleUtils::nthElementOfTuple(pt, starts[k] + c);
        if (k == j)
        {
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(b, c));
        }
        else
        {
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(a, aPos++));
        }
        from.push_back(whole);
      }
    }
    // f reads an aliased column of B as the column of the others it equals
    std::vector<Node> fFrom, fTo;
    {
      std::map<uint32_t, Node> aCell;
      size_t ap = 0;
      for (size_t k = 0; k < comps.size(); k++)
      {
        for (size_t c = 0; c < widths[k]; c++)
        {
          if (k != j)
          {
            aCell[starts[k] + c] =
                datatypes::TupleUtils::nthElementOfTuple(a, ap++);
          }
        }
      }
      for (size_t k = 0; k < comps.size(); k++)
      {
        for (size_t c = 0; c < widths[k]; c++)
        {
          uint32_t pos = starts[k] + c;
          if (k == j && !aliases.count(pos))
          {
            continue;
          }
          fFrom.push_back(datatypes::TupleUtils::nthElementOfTuple(ft, pos));
          fTo.push_back(aCell[k == j ? aliases[pos] : pos]);
        }
      }
    }
    Node pA = onA.empty()
                  ? d_nm->mkConst(true)
                  : (onA.size() == 1 ? onA[0] : d_nm->mkNode(Kind::AND, onA));
    Node pAB = onAB.size() == 1 ? onAB[0] : d_nm->mkNode(Kind::AND, onAB);
    pA = pA.substitute(from.begin(), from.end(), to.begin(), to.end());
    pAB = pAB.substitute(from.begin(), from.end(), to.begin(), to.end());
    Node fBody =
        f[1].substitute(fFrom.begin(), fFrom.end(), fTo.begin(), fTo.end());
    if (occursFree(pA, pt) || occursFree(pAB, pt) || occursFree(fBody, ft)
        || occursFree(pA, b) || occursFree(fBody, b))
    {
      continue;
    }
    // some row of B passes pAB: the filter of B by pAB is not empty
    Node matches = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(b, pAB), B);
    Node empty = d_nm->mkConst(EmptyBag(B.getType()));
    Node exists = matches.eqNode(empty).notNode();
    Node filtered =
        d_nm->mkNode(Kind::BAG_FILTER, mkLambda(a, pA.andNode(exists)), A);
    Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(a, fBody), filtered);
    return BagsRewriteResponse(ret, Rewrite::SEMI_JOIN);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteMapSplitClosed(const TNode& n) const
{
  // MAP_SPLIT_CLOSED: a map whose body has a Boolean subterm c that asks about
  // a bag and reads no variable but the row, such as EXISTS or IN of a subquery
  // as a column, splits on c: the map with true for c over the rows where c
  // holds, and the map with false for c over the others (see rewrites.h). The
  // question becomes a filter, which the filter rules decorrelate.
  Node f = n[0];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node t = f[0][0];
  Node body = f[1];
  if (bindsVariable(body, t))
  {
    // an inner binder of t: a subterm equal to c there would read another t
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node c;
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo{body};
  while (!todo.empty() && c.isNull())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second || cur.isConst())
    {
      continue;
    }
    if (cur.getType().isBoolean()
        && expr::hasSubtermKinds({Kind::BAG_FILTER,
                                  Kind::BAG_MAP,
                                  Kind::BAG_COUNT,
                                  Kind::BAG_SETOF,
                                  Kind::TABLE_PRODUCT,
                                  Kind::TABLE_AGGREGATE,
                                  Kind::TABLE_PROJECT},
                                 cur))
    {
      // a question about a bag, the row's own (IN (subquery)) or not
      // (EXISTS (subquery)), reading no other variable
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(cur, fvs);
      fvs.erase(t);
      if (fvs.empty())
      {
        c = cur;
        break;
      }
    }
    if (cur.isClosure())
    {
      continue;
    }
    for (const Node& ch : cur)
    {
      todo.push_back(ch);
    }
  }
  if (c.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node X = n[1];
  Node yes = body.substitute(TNode(c), TNode(d_nm->mkConst(true)));
  Node no = body.substitute(TNode(c), TNode(d_nm->mkConst(false)));
  Node a = d_nm->mkNode(
      Kind::BAG_MAP,
      {mkLambda(t, yes), d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, c), X)});
  Node b = d_nm->mkNode(
      Kind::BAG_MAP,
      {mkLambda(t, no),
       d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, c.notNode()), X)});
  Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
  return BagsRewriteResponse(ret, Rewrite::MAP_SPLIT_CLOSED);
}

Node BagsRewriter::rewriteEmptyFilter(const Node& F) const
{
  // EQ_EMPTY_FILTER_DECORRELATE, for the emptiness of a filter F in the body of
  // an enclosing lambda over a row r: F filters X by c, q and equations, where
  // c reads no row of X, only r or nothing, q reads only the row s of X, and
  // each equation ties a column of s to a term E that reads no s, such as
  // (= ((_ tuple.select 1) s) ((_ tuple.select 0) r)). No row of X passes when
  // c fails, or when the tuple of the E is not among those columns of the rows
  // that pass q. For X : (Bag (Tuple Int Int)), r : (Tuple Int Int) and
  //   F = (bag.filter
  //         (lambda ((s (Tuple Int Int)))
  //           (and (> ((_ tuple.select 0) r) 3)
  //                (< ((_ tuple.select 0) s) 7)
  //                (= ((_ tuple.select 1) s) ((_ tuple.select 0) r))))
  //         X)
  // (= (as bag.empty (Bag (Tuple Int Int))) F) is
  //   (or (not (> ((_ tuple.select 0) r) 3))
  //       (not (>= (bag.count (tuple ((_ tuple.select 0) r))
  //                           (bag.map
  //                             (lambda ((s (Tuple Int Int)))
  //                               (tuple ((_ tuple.select 1) s)))
  //                             (bag.filter
  //                               (lambda ((s (Tuple Int Int)))
  //                                 (< ((_ tuple.select 0) s) 7))
  //                               X)))
  //                1)))
  // The bag no longer depends on the enclosing row, so a filter over this
  // predicate is not a new bag per row the solver reads. Returns that formula,
  // or null when F is not of that shape.
  Node P = asLambda(F[0]);
  Node X = F[1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)
  {
    return Node::null();
  }
  Node sv = P[0][0];
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  std::vector<Node> outer, inner, keysS, keysE;
  for (const Node& c : conjuncts)
  {
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(c, fvs);
    bool hasS = fvs.erase(sv) > 0;
    if (!hasS)
    {
      outer.push_back(c);
      continue;
    }
    bool matched = false;
    if (fvs.empty())
    {
      // an equation between a column and a constant is a key as well: the
      // emptiness of the filter of X by (= ((_ tuple.select 1) s) 10) says that
      // 10 is not among the values of the column
      if (c.getKind() == Kind::EQUAL)
      {
        for (size_t side = 0; side < 2 && !matched; side++)
        {
          if (c[side].getKind() == Kind::APPLY_SELECTOR && c[side][0] == sv
              && c[1 - side].isConst())
          {
            keysS.push_back(c[side]);
            keysE.push_back(c[1 - side]);
            matched = true;
          }
        }
      }
      if (!matched)
      {
        inner.push_back(c);
      }
      continue;
    }
    if (c.getKind() == Kind::EQUAL)
    {
      for (size_t side = 0; side < 2 && !matched; side++)
      {
        if (c[side].getKind() == Kind::APPLY_SELECTOR && c[side][0] == sv
            && !occursFree(c[1 - side], sv))
        {
          keysS.push_back(c[side]);
          keysE.push_back(c[1 - side]);
          matched = true;
        }
      }
    }
    if (!matched)
    {
      return Node::null();
    }
  }
  if (outer.empty() && keysS.empty())
  {
    return Node::null();
  }
  {
    // the keys in the order of their columns, so that one join written two
    // ways probes one tuple in one bag
    std::vector<size_t> order(keysS.size());
    for (size_t k = 0; k < order.size(); k++)
    {
      order[k] = k;
    }
    std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
      uint32_t ia = datatypes::utils::indexOf(keysS[a].getOperator());
      uint32_t ib = datatypes::utils::indexOf(keysS[b].getOperator());
      return ia < ib;
    });
    std::vector<Node> ks, ke;
    for (size_t k : order)
    {
      ks.push_back(keysS[k]);
      ke.push_back(keysE[k]);
    }
    keysS = ks;
    keysE = ke;
  }
  if (!keysS.empty())
  {
    // an inner conjunct that reads only equated columns says the same of the
    // expressions they equal: (nullable.is_some ((_ tuple.select 1) s)) with
    // (= ((_ tuple.select 1) s) E) is (nullable.is_some E). Moved out, it no
    // longer depends on which side of the equation was written first (the
    // three-valued = tests its first operand for NULL)
    std::vector<Node> from, to;
    std::set<uint32_t> keyPositions;
    for (size_t k = 0; k < keysS.size(); k++)
    {
      uint32_t pos = datatypes::utils::indexOf(keysS[k].getOperator());
      if (keyPositions.insert(pos).second)
      {
        from.push_back(keysS[k]);
        to.push_back(keysE[k]);
      }
    }
    std::vector<Node> stays;
    for (const Node& c : inner)
    {
      std::set<uint32_t> positions;
      bool onKeys = readPositions(c, sv, positions) && !bindsVariable(c, sv);
      for (uint32_t pos : positions)
      {
        onKeys = onKeys && keyPositions.count(pos) > 0;
      }
      if (onKeys && !positions.empty())
      {
        Node moved =
            c.substitute(from.begin(), from.end(), to.begin(), to.end());
        if (!occursFree(moved, sv))
        {
          outer.push_back(moved);
          continue;
        }
      }
      stays.push_back(c);
    }
    inner = stays;
  }
  Node rest =
      inner.empty()
          ? d_nm->mkConst(true)
          : (inner.size() == 1 ? inner[0] : d_nm->mkNode(Kind::AND, inner));
  Node passing = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(sv, rest), X);
  Node none;
  if (keysS.empty())
  {
    none = passing.eqNode(d_nm->mkConst(EmptyBag(X.getType())));
  }
  else
  {
    std::vector<TypeNode> types;
    for (const Node& k : keysS)
    {
      types.push_back(k.getType());
    }
    TypeNode keyType = d_nm->mkTupleType(types);
    Node columns = mkLambda(sv,
                            datatypes::TupleUtils::constructTupleFromElements(
                                keyType, keysS, 0, keysS.size() - 1));
    Node projected = d_nm->mkNode(Kind::BAG_MAP, columns, passing);
    Node probe = datatypes::TupleUtils::constructTupleFromElements(
        keyType, keysE, 0, keysE.size() - 1);
    Node count = d_nm->mkNode(Kind::BAG_COUNT, probe, projected);
    none = d_nm->mkNode(Kind::GEQ, count, d_one).notNode();
  }
  std::vector<Node> disjuncts;
  for (const Node& c : outer)
  {
    disjuncts.push_back(c.notNode());
  }
  disjuncts.push_back(none);
  return disjuncts.size() == 1 ? disjuncts[0]
                               : d_nm->mkNode(Kind::OR, disjuncts);
}

Node BagsRewriter::emptinessAtom(const Node& atom) const
{
  // an atom of a lambda body that asks about a bag, as the formula it stands
  // for, or null:
  //   (>= (bag.count e (bag.inter_min X Y)) 1)
  //   ---> (and (>= (bag.count e X) 1) (>= (bag.count e Y) 1))
  //   (>= (bag.count e (bag.setof X)) 1) ---> (>= (bag.count e X) 1)
  //   (>= (ite b x 0) 1) ---> (and b (>= x 1))
  //   (= (nullable.val (bag.fold f (nullable.some 0) X)) 0)
  //   ---> (= X (as bag.empty (Bag T))), for f counting the rows of X
  //   (= (as bag.empty (Bag V)) (bag.filter Q ((_ table.aggr K) f i Y)))
  //   ---> (= Y (as bag.empty (Bag T))), for Q the counter test alone: the
  //        groups some row reached, none exactly when there is no row
  //   (= (as bag.empty (Bag T)) F) for a filter F, decorrelated, see
  //   rewriteEmptyFilter
  //   (= (as bag.empty (Bag T)) (bag.inter_min X Y)), whose filters fix
  //   every column of an element to a term E of the enclosing rows
  //   ---> (not (and (>= (bag.count E X) 1) (>= (bag.count E Y) 1)))
  //   (= (as bag.empty (Bag T)) (bag x c)) ---> (<= c 0)
  // Done here, from the bodies (normalizeEmptiness), rather than by the
  // rewriting of the equality, which must stay an equality.
  if (atom.getKind() == Kind::GEQ && atom[1].isConst()
      && atom[1].getConst<Rational>() == Rational(1))
  {
    Node c = atom[0];
    // (>= (bag.count e (bag.inter_min X Y)) 1) is membership in both
    if (c.getKind() == Kind::BAG_COUNT && c[1].getKind() == Kind::BAG_INTER_MIN)
    {
      Node x = d_nm->mkNode(Kind::BAG_COUNT, c[0], c[1][0]);
      Node y = d_nm->mkNode(Kind::BAG_COUNT, c[0], c[1][1]);
      return d_nm->mkNode(Kind::AND,
                          {d_nm->mkNode(Kind::GEQ, x, d_one),
                           d_nm->mkNode(Kind::GEQ, y, d_one)});
    }
    // (>= (bag.count e (bag.setof X)) 1) is membership in X
    if (c.getKind() == Kind::BAG_COUNT && c[1].getKind() == Kind::BAG_SETOF)
    {
      Node x = d_nm->mkNode(Kind::BAG_COUNT, c[0], c[1][0]);
      return d_nm->mkNode(Kind::GEQ, x, d_one);
    }
    // (>= (ite b x 0) 1) is b and (>= x 1)
    if (c.getKind() == Kind::ITE && c[2].isConst()
        && c[2].getConst<Rational>() < Rational(1))
    {
      return d_nm->mkNode(
          Kind::AND, c[0], d_nm->mkNode(Kind::GEQ, c[1], d_one));
    }
    return Node::null();
  }
  if (atom.getKind() == Kind::EQUAL && atom[0].getType().isInteger())
  {
    // (= (nullable.val F) 0) with F counting the rows of X from (some 0):
    // X has no row
    for (size_t i = 0; i < 2; i++)
    {
      const Node& z = atom[i];
      const Node& v = atom[1 - i];
      if (!z.isConst() || !z.getConst<Rational>().isZero()
          || v.getKind() != Kind::APPLY_SELECTOR
          || v[0].getKind() != Kind::BAG_FOLD)
      {
        continue;
      }
      Node F = v[0];
      Node l = asLambda(F[0]);
      if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2
          && isCountStep(l[1], l[0][1], F[1]) && l[1].getKind() != Kind::ITE)
      {
        return F[2].eqNode(d_nm->mkConst(EmptyBag(F[2].getType())));
      }
    }
    return Node::null();
  }
  if (atom.getKind() != Kind::EQUAL || !atom[0].getType().isBag())
  {
    return Node::null();
  }
  for (size_t i = 0; i < 2; i++)
  {
    if (atom[i].getKind() != Kind::BAG_EMPTY)
    {
      continue;
    }
    Node F = atom[1 - i];
    if (F.getKind() == Kind::BAG_FILTER
        && F[1].getKind() == Kind::TABLE_AGGREGATE
        && !F[1].getOperator().getConst<ProjectOp>().getIndices().empty()
        && asLambda(F[0]).getKind() == Kind::LAMBDA
        && asLambda(F[0])[1].getKind() != Kind::AND
        && counterColumn(F[0], asLambda(F[1][0]), F[1][1]) >= 0)
    {
      // the groups some row reached: none exactly when there is no row
      Node Y = F[1][2];
      if (Y.getKind() == Kind::BAG_FILTER)
      {
        return rewriteEmptyFilter(Y);
      }
      return Y.eqNode(d_nm->mkConst(EmptyBag(Y.getType())));
    }
    if (F.getKind() == Kind::BAG_FILTER)
    {
      return rewriteEmptyFilter(F);
    }
    if (F.getKind() == Kind::BAG_INTER_MIN
        && F.getType().getBagElementType().isTuple())
    {
      // (= bag.empty (bag.inter_min X Y)) where the filters of X and Y fix
      // every column of an element to an expression of the enclosing rows:
      // that tuple E is the only candidate,
      //   (not (and (>= (bag.count E X) 1) (>= (bag.count E Y) 1)))
      TypeNode et = F.getType().getBagElementType();
      Node w = rowVariable(et);
      std::set<Node> conds;
      elementConditions(F, w, conds);
      size_t m = et.getTupleLength();
      std::vector<Node> cols(m);
      for (const Node& c : conds)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        for (size_t sd = 0; sd < 2; sd++)
        {
          if (c[sd].getKind() == Kind::APPLY_SELECTOR && c[sd][0] == w
              && !occursFree(c[1 - sd], w))
          {
            size_t k = datatypes::utils::indexOf(c[sd].getOperator());
            if (cols[k].isNull())
            {
              cols[k] = c[1 - sd];
            }
          }
        }
      }
      if (std::find(cols.begin(), cols.end(), Node::null()) == cols.end())
      {
        Node E = datatypes::TupleUtils::constructTupleFromElements(
            et, cols, 0, m - 1);
        Node inX = d_nm->mkNode(
            Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, E, F[0]), d_one);
        Node inY = d_nm->mkNode(
            Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, E, F[1]), d_one);
        return d_nm->mkNode(Kind::AND, inX, inY).notNode();
      }
    }
    if (F.getKind() == Kind::BAG_MAKE)
    {
      return d_nm->mkNode(Kind::LEQ, F[1], d_zero);
    }
  }
  return Node::null();
}

// Returns the formula that says the nullable Boolean X : (Nullable Bool) is
// true, (= X (nullable.some true)), when X is built of ites whose leaves are
// (nullable.some b) or (as nullable.null (Nullable Bool)); returns the null
// Node for any other X. In SQL's three-valued logic, which (Nullable Bool)
// encodes, null is not true, so a null leaf says false. For c, b : Bool,
//   X = (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
//   ---> returns (ite c b false)
// and nested ites give nested ites of the same shape. For X a variable of
// sort (Nullable Bool) it returns the null Node.
Node BagsRewriter::truthOf(const Node& X) const
{
  if (X.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // a leaf: (nullable.some b), the constructor of one argument, is true
    // when b is; (as nullable.null (Nullable Bool)), of none, never is
    return X.getNumChildren() == 1 ? X[0] : d_nm->mkConst(false);
  }
  if (X.getKind() == Kind::ITE)
  {
    // (ite c X1 X2) is true when X1 is, if c holds, and when X2 is, if not
    Node a = truthOf(X[1]);
    Node b = truthOf(X[2]);
    if (a.isNull() || b.isNull())
    {
      return Node::null();
    }
    return d_nm->mkNode(Kind::ITE, X[0], a, b);
  }
  // another term, as a variable or a column of a row: no formula
  return Node::null();
}

// FILTER_NULLABLE_TRUTH: body is the body of a filter's predicate. SQL's
// WHERE keeps a row when its three-valued condition X : (Nullable Bool) is
// true, which can be written as two conjuncts, (nullable.is_some X) and
// (nullable.val X). When X is an ite that truthOf reads, both conjuncts are
// replaced by the one formula truthOf(X) that they say together, at the
// place of the first of them; the other conjuncts are kept in their order.
// So a WHERE over a three-valued condition is one formula, whether it was
// written as the two conjuncts or as the formula. For
// t : (Tuple Int (Nullable Int)) and
//   X = (ite (nullable.is_some ((_ tuple.select 1) t))
//            (nullable.some (> (nullable.val ((_ tuple.select 1) t)) 3))
//            (as nullable.null (Nullable Bool))),
//   (and (nullable.is_some X) (nullable.val X) (> ((_ tuple.select 0) t) 0))
//   ---> (and (ite (nullable.is_some ((_ tuple.select 1) t))
//                  (> (nullable.val ((_ tuple.select 1) t)) 3)
//                  false)
//             (> ((_ tuple.select 0) t) 0))
// which the rewriter then simplifies further. Returns body itself when it has
// no such pair of conjuncts.
Node BagsRewriter::normalizeTruth(const Node& body) const
{
  // the top-level conjuncts of body, or body itself as the one conjunct
  std::vector<Node> conjuncts;
  if (body.getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), body.begin(), body.end());
  }
  else
  {
    conjuncts.push_back(body);
  }
  // vals: the terms X, ites of a nullable sort, for which body has the
  // conjunct (nullable.val X), nullable.val being the one selector of a
  // nullable sort; the conjunct is a formula, so X : (Nullable Bool)
  std::set<Node> vals;
  for (const Node& c : conjuncts)
  {
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0].getType().isNullable()
        && c[0].getKind() == Kind::ITE)
    {
      vals.insert(c[0]);
    }
  }
  if (vals.empty())
  {
    return body;
  }
  // out: the new conjuncts; done: the X whose formula is in out already
  std::vector<Node> out;
  bool changed = false;
  std::set<Node> done;
  for (const Node& c : conjuncts)
  {
    // X, the term of vals that c is about: c = (nullable.val X), or c a
    // tester of X; isTester returns the index of the constructor it tests,
    // -1 for no tester, and sets a to the tested term
    Node X;
    Node a;
    if (c.getKind() == Kind::APPLY_SELECTOR && vals.count(c[0]))
    {
      X = c[0];
    }
    else if (datatypes::utils::isTester(c, a) >= 0 && vals.count(a))
    {
      X = a;
    }
    if (!X.isNull())
    {
      Node t = truthOf(X);
      if (!t.isNull())
      {
        // Both conjuncts become the one formula t, provided that body also
        // has the conjunct (nullable.is_some X), the tester of the
        // constructor of one argument. A lone (nullable.val X) is kept: its
        // value when X is null is unspecified, so it is not t. When the pair
        // is there, c is dropped, whichever constructor it tests, and t is
        // added once per X. A (nullable.is_null X) conjunct does not occur
        // in the rewritten bodies seen here: the datatypes rewriter writes it
        // as an equality with null, which is no tester
        bool hasTester = false;
        for (const Node& d : conjuncts)
        {
          Node b;
          int ci = datatypes::utils::isTester(d, b);
          hasTester = hasTester
                      || (ci >= 0 && b == X
                          && X.getType().getDType()[ci].getNumArgs() == 1);
        }
        if (hasTester)
        {
          if (done.insert(X).second)
          {
            out.push_back(t);
          }
          changed = true;
          continue;
        }
      }
    }
    // any other conjunct is kept as it is
    out.push_back(c);
  }
  if (!changed)
  {
    return body;
  }
  return out.size() == 1 ? out[0] : d_nm->mkNode(Kind::AND, out);
}

Node BagsRewriter::normalizeEmptiness(const Node& body) const
{
  // EQ_EMPTY_FILTER_DECORRELATE: the emptiness atoms of body outside of any
  // binder inside it, replaced by emptinessAtom; those under an inner binder
  // belong to that lambda's own filter or map, which does the same when it
  // is rewritten
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{body};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    if (n.isClosure() || n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    Node replaced = emptinessAtom(n);
    if (!replaced.isNull())
    {
      cache[n] = replaced;
      todo.pop_back();
      continue;
    }
    bool ready = true;
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      changed = changed || cache[c] != c;
      children.push_back(cache[c]);
    }
    cache[n] = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
  }
  return cache[body];
}

// AGGREGATE_DEAD_COLUMNS: for n = (bag.map h A) or n = (bag.map h
// (bag.filter P A)), with A = ((_ table.aggr K) f i X), removes from A the
// dead columns: the columns of A's rows that the rest of the term never
// reads. A column q is dead when neither h nor P reads it, and the step f
// computes it from the row of X and from column q of the accumulator only,
// a column of the accumulator that no other column of f reads. Then column q
// changes no column that is read. The aggregate groups the rows of X by its
// group columns K, columns of X and not of its output, so no group changes.
// table.aggr gives one row per group, and two groups whose rows differ only
// in dead columns give equal new rows, which h maps as it mapped the old
// ones, so the multiplicities agree too. For X : (Bag (Tuple Int Int)) and
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
//         (tuple ((_ tuple.select 0) t)
//                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
//                (+ ((_ tuple.select 2) acc) 1))),
//   (bag.map (lambda ((r (Tuple Int Int Int)))
//              (tuple ((_ tuple.select 0) r) ((_ tuple.select 2) r)))
//            ((_ table.aggr 0) f (tuple 0 0 0) X))
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
//          ((_ table.aggr 0)
//            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
//            (tuple 0 0) X))                       (AGGREGATE_DEAD_COLUMNS)
// Here the map reads the group column 0 and the count of rows, column 2, and
// the sum in column 1 is dead. With a filter (bag.filter P A) in between, P
// is rewritten as h is, to read the new rows.
BagsRewriteResponse BagsRewriter::rewriteAggregateDeadColumns(
    const TNode& n) const
{
  // Phase 1, the shape. n = (bag.map h Y); when Y is a filter
  // (bag.filter P A), P is its predicate and Y becomes A. h and P are read
  // as lambdas of one variable, a row r of A, even when they are kept as
  // function constants
  Node h = asLambda(n[0]);
  Node Y = n[1];
  Node P;
  if (Y.getKind() == Kind::BAG_FILTER)
  {
    P = asLambda(Y[0]);
    Y = Y[1];
  }
  if (Y.getKind() != Kind::TABLE_AGGREGATE || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1
      || (!P.isNull()
          && (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // Y = ((_ table.aggr K) f i X), with f = (lambda ((t R) (acc T))
  // (tuple e_0 .. e_(m-1))), t : R a row of X and acc : T the accumulator,
  // and i = (tuple i_0 .. i_(m-1)): column q of A's rows is computed by e_q
  // from i_q, so a column can be removed by removing e_q and i_q
  Node f = Y[0];
  Node i = Y[1];
  Node X = Y[2];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple()
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  size_t m = f[1].getNumChildren();
  // Phase 2, the columns of A's rows that are read. read collects the
  // columns k that h reads, as ((_ tuple.select k) r), and those that P
  // reads. h and P must read their row only through such selectors, never
  // whole, and no lambda inside them may bind their variable again (a read
  // of that inner variable is not a read of A's row)
  std::set<uint32_t> read;
  if (!readPositions(h[1], h[0][0], read) || bindsVariable(h[1], h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  if (!P.isNull()
      && (!readPositions(P[1], P[0][0], read) || bindsVariable(P[1], P[0][0])))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  // reads[q]: the columns of the accumulator acc that e_q reads, by the same
  // rules; in the example above, {1} for e_1 and {2} for e_2
  std::vector<std::set<uint32_t>> reads(m);
  for (size_t q = 0; q < m; q++)
  {
    if (!readPositions(f[1][q], acc, reads[q]) || bindsVariable(f[1][q], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // Phase 3, the dead columns. Column q is dead, keep[q] false, when it is
  // not in read, e_q reads no column of acc but q (self), and no other e_o
  // reads column q of acc (readByOthers). In the example, read is {0, 2}
  // and column 1 is dead
  std::vector<bool> keep(m, true);
  bool dropped = false;
  for (size_t q = 0; q < m; q++)
  {
    if (read.count(q))
    {
      continue;
    }
    bool self = true;
    for (uint32_t p : reads[q])
    {
      self = self && p == q;
    }
    bool readByOthers = false;
    for (size_t o = 0; o < m; o++)
    {
      readByOthers = readByOthers || (o != q && reads[o].count(q) > 0);
    }
    if (self && !readByOthers)
    {
      keep[q] = false;
      dropped = true;
    }
  }
  if (!dropped)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // Phase 4, the new row sort. newIndex[q] is the position of a kept column
  // q in the new rows, which have the kept columns in their order, of sort
  // newType: in the example, columns 0 and 2 become 0 and 1, of sort
  // (Tuple Int Int)
  std::vector<uint32_t> newIndex(m, 0);
  std::vector<TypeNode> types;
  uint32_t next = 0;
  TypeNode oldType = f[1].getType();
  for (size_t q = 0; q < m; q++)
  {
    if (keep[q])
    {
      newIndex[q] = next++;
      types.push_back(oldType.getTupleTypes()[q]);
    }
  }
  if (types.empty())
  {
    // every column is dead, as for an h that reads none: the rule does not
    // build an aggregate whose rows have no column
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // acc2 and r2, the rewriter's variables for an accumulator and for a row of
  // newType, are the variables of the new step and of the new h and P. acc2
  // must not be the row variable x nor occur in f's body, and r2 must not
  // occur in the bodies of h and P: the substitutions below would mix them
  // up with those occurrences
  TypeNode newType = d_nm->mkTupleType(types);
  Node acc2 = accumulatorVariable(newType);
  Node r2 = rowVariable(newType);
  if (acc2 == x || expr::hasSubterm(f[1], acc2) || expr::hasSubterm(h[1], r2)
      || (!P.isNull() && expr::hasSubterm(P[1], r2)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // reindex(body, var, to): body with each read ((_ tuple.select q) var) of
  // a kept column q replaced by ((_ tuple.select newIndex[q]) to), the same
  // column in the new tuple to. Reads of dead columns stay as they are; the
  // checks after each use make sure that var no longer occurs
  auto reindex = [&](const Node& body, const Node& var, const Node& to) {
    std::vector<Node> from, into;
    for (size_t q = 0; q < m; q++)
    {
      if (keep[q])
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(var, q));
        into.push_back(
            datatypes::TupleUtils::nthElementOfTuple(to, newIndex[q]));
      }
    }
    return body.substitute(from.begin(), from.end(), into.begin(), into.end());
  };
  // Phase 5, the smaller step and initial value: the e_q and i_q of the
  // kept columns, each e_q reading acc2 in place of acc. In the example,
  // e_2 = (+ ((_ tuple.select 2) acc) 1) becomes
  // (+ ((_ tuple.select 1) acc2) 1). A kept e_q reads no dead column of acc,
  // as no dead column is read by another, so acc is gone; the check makes
  // sure
  std::vector<Node> elems, init;
  for (size_t q = 0; q < m; q++)
  {
    if (keep[q])
    {
      elems.push_back(reindex(f[1][q], acc, acc2));
      init.push_back(i[q]);
    }
  }
  Node body = datatypes::TupleUtils::constructTupleFromElements(
      newType, elems, 0, elems.size() - 1);
  if (occursFree(body, acc))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the new aggregate ((_ table.aggr K) f2 i2 X): the same operator, so the
  // same group columns K, and f2 = (lambda ((x R) (acc2 newType)) body).
  // Its row for a group is the old row for that group without the dead
  // columns, and so is its row of initial values for an empty X
  Node f2 = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
  Node i2 = datatypes::TupleUtils::constructTupleFromElements(
      newType, init, 0, init.size() - 1);
  std::vector<Node> children{Y.getOperator(), f2, i2, X};
  Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  // Phase 6, the map and the filter over the new rows: h, and P if there is
  // one, reading the row r2 of the new aggregate. They read no dead column,
  // so their variable is gone; the checks make sure
  Node h2body = reindex(h[1], h[0][0], r2);
  if (occursFree(h2body, h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node below = aggr;
  if (!P.isNull())
  {
    // (bag.filter (lambda ((r2 newType)) p2body) aggr)
    Node p2body = reindex(P[1], P[0][0], r2);
    if (occursFree(p2body, P[0][0]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    below = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r2, p2body), aggr);
  }
  // (bag.map (lambda ((r2 newType)) h2body) below)
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(r2, h2body), below);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_DEAD_COLUMNS);
}

// Returns the columns that the filter predicate p fixes to constants, as a
// map from column index to constant: k -> c for each top-level conjunct
// (= ((_ tuple.select k) t) c) or (= c ((_ tuple.select k) t)) of p's body,
// with t the variable of p and c a constant. Every row that passes the
// filter has c in column k. For t : (Tuple Int Int),
//   (lambda ((t (Tuple Int Int)))
//     (and (= ((_ tuple.select 1) t) 5) (> ((_ tuple.select 0) t) 3)))
//   ---> returns {1 -> 5}
// The map is empty when p is not a lambda of one variable of a tuple sort.
std::map<uint32_t, Node> BagsRewriter::fixedColumns(const Node& p) const
{
  std::map<uint32_t, Node> fixed;
  // p may be kept as a function constant, read as the lambda it stands for
  Node lambda = asLambda(p);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1)
  {
    return fixed;
  }
  Node t = lambda[0][0];
  if (!t.getType().isTuple())
  {
    // the selectors of a row that is no tuple are no columns: in a filter
    // over a (Bag (Nullable Int)), (= (nullable.val t) 5) fixes no column
    return fixed;
  }
  // the top-level conjuncts of p's body, or the body as the one conjunct
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  for (const Node& c : conjuncts)
  {
    if (c.getKind() != Kind::EQUAL)
    {
      continue;
    }
    // the column on either side of the equality, the constant on the other.
    // When two conjuncts fix one column, the later one is kept; if their
    // constants differ, no row passes the filter, and either constant is
    // right for all the rows that do
    for (size_t side = 0; side < 2; side++)
    {
      if (c[side].getKind() == Kind::APPLY_SELECTOR && c[side][0] == t
          && c[1 - side].isConst())
      {
        fixed[datatypes::utils::indexOf(c[side].getOperator())] = c[1 - side];
      }
    }
  }
  return fixed;
}

// Returns body with each read ((_ tuple.select k) var) of a column k that
// fixed maps to a constant c replaced by c. fixed comes from fixedColumns or
// reachedGroupConstants, so that every row var ranges over has c in column
// k. For t : (Tuple Int Int) and fixed = {1 -> 5},
//   (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0)
//   ---> returns (tuple ((_ tuple.select 0) t) 5 0)
Node BagsRewriter::readFixed(const Node& body,
                             const Node& var,
                             const std::map<uint32_t, Node>& fixed) const
{
  // Nothing to replace for an empty map. When a lambda inside body binds
  // var again, the reads of that inner variable are not reads of the row,
  // and the substitution below would replace them too; body is then kept
  if (fixed.empty() || bindsVariable(body, var))
  {
    return body;
  }
  std::vector<Node> from, to;
  for (const std::pair<const uint32_t, Node>& fc : fixed)
  {
    from.push_back(datatypes::TupleUtils::nthElementOfTuple(var, fc.first));
    to.push_back(fc.second);
  }
  return body.substitute(from.begin(), from.end(), to.begin(), to.end());
}

// For F = (bag.filter P A), A = ((_ table.aggr K) f i X), returns a map from
// each column that has one constant in every row P keeps to that constant,
// when P keeps only reached groups; an empty map otherwise. A reached group
// is a group that some row of X falls in. Every group of a non-empty X is
// one, but an aggregate of an empty X still has one row, made of the initial
// values i, which comes from no reached group.
// P keeps only reached groups when it has a conjunct
// (>= ((_ tuple.select c) r) 1), r P's variable, on a counter column c: a
// column whose step adds 1 per row, (+ ((_ tuple.select c) acc) 1), from the
// initial value 0, as SQL's COUNT(*); it is at least 1 exactly in the
// reached groups. A reached group folds at least one row, so a column whose
// step is a constant has that constant, and a column the step keeps as it
// is, ((_ tuple.select q) acc), has its initial value. For
// X : (Bag (Tuple Int Int)) and r, acc : (Tuple Int Int Int Int),
//   F = (bag.filter (lambda ((r (Tuple Int Int Int Int)))
//                     (>= ((_ tuple.select 3) r) 1))
//         ((_ table.aggr 0)
//           (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int Int)))
//             (tuple ((_ tuple.select 0) t) 7 ((_ tuple.select 2) acc)
//                    (+ ((_ tuple.select 3) acc) 1)))
//           (tuple 0 0 4 0) X))
//   ---> returns {1 -> 7, 2 -> 4}
std::map<uint32_t, Node> BagsRewriter::reachedGroupConstants(
    const Node& F) const
{
  // F[1] is the aggregate A (the caller checks it). P must be a lambda of one
  // variable, f a lambda of the row and the accumulator whose body is a tuple
  // (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as many
  // components
  std::map<uint32_t, Node> constants;
  Node P = asLambda(F[0]);
  Node aggr = F[1];
  Node f = aggr[0];
  Node i = aggr[1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i)
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return constants;
  }
  // r, a row of the aggregate's result; x, a row of X; acc, the accumulator
  Node r = P[0][0];
  Node x = f[0][0];
  Node acc = f[0][1];
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  // reached: whether P tests a counter column positive, by the same checks
  // as counterColumn
  bool reached = false;
  for (const Node& c : conjuncts)
  {
    // c = (>= ((_ tuple.select col) r) 1), for a column col of A's rows
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::APPLY_SELECTOR || c[0][0] != r)
    {
      continue;
    }
    uint32_t col = datatypes::utils::indexOf(c[0].getOperator());
    if (col >= f[1].getNumChildren())
    {
      continue;
    }
    // e_col = (+ ((_ tuple.select col) acc) 1), or (+ 1 ..), and i_col = 0
    Node step = f[1][col];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, col);
    bool increment = step.getKind() == Kind::ADD && step.getNumChildren() == 2
                     && ((step[0] == own && step[1] == d_one)
                         || (step[1] == own && step[0] == d_one));
    if (increment && i[col].isConst()
        && i[col].getConst<Rational>() == Rational(0))
    {
      reached = true;
    }
  }
  if (!reached)
  {
    return constants;
  }
  for (size_t q = 0, m = f[1].getNumChildren(); q < m; q++)
  {
    Node c = f[1][q];
    if (c.isConst() && !occursFree(c, x) && !occursFree(c, acc))
    {
      // a constant step e_q = c: after the first row of the group, column q
      // is c, and it stays c
      constants[q] = c;
    }
    else if (c == datatypes::TupleUtils::nthElementOfTuple(acc, q)
             && i[q].isConst())
    {
      // a column the step keeps as it is, e_q = ((_ tuple.select q) acc),
      // with a constant initial value i_q: column q is i_q
      constants[q] = i[q];
    }
  }
  return constants;
}

// Returns the counter column of an aggregate ((_ table.aggr K) f i X) that
// the filter predicate P tests positive, or -1 when there is none. A counter
// column is a column c whose step adds 1 per row,
// (+ ((_ tuple.select c) acc) 1) or (+ 1 ((_ tuple.select c) acc)), from the
// initial value 0, as SQL's COUNT(*). P tests it positive when it has the
// top-level conjunct (>= ((_ tuple.select c) r) 1), r its variable, the form
// the arithmetic rewriter gives (> ((_ tuple.select c) r) 0) on integers.
// sqleq's translator from SQL adds such a counter and test to every
// aggregate with group columns: SQL's GROUP BY makes no group of an empty
// table, while table.aggr of an empty table has one row, of the initial
// values, whose count 0 the test rejects. A filter by P thus keeps only the
// reached groups, those that some row of X falls in.
// For X : (Bag (Tuple Int Int)),
//   P = (lambda ((r (Tuple Int Int Int)))
//         (and (>= ((_ tuple.select 2) r) 1) (>= ((_ tuple.select 1) r) 10)))
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
//         (tuple ((_ tuple.select 0) t)
//                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
//                (+ ((_ tuple.select 2) acc) 1)))
//   i = (tuple 0 0 0)
//   ---> returns 2
int BagsRewriter::counterColumn(const Node& P,
                                const Node& f,
                                const Node& i) const
{
  // P must be a lambda of one variable (or a function constant that stands
  // for one), f a lambda of the row and the accumulator whose body is a
  // tuple (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as
  // many components
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i)
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return -1;
  }
  // r, a row of the aggregate's result; acc, the accumulator of f
  Node r = lambda[0][0];
  Node acc = f[0][1];
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  for (const Node& c : conjuncts)
  {
    // c = (>= ((_ tuple.select col) r) 1), for a column col of the rows
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::APPLY_SELECTOR || c[0][0] != r)
    {
      continue;
    }
    uint32_t col = datatypes::utils::indexOf(c[0].getOperator());
    if (col >= f[1].getNumChildren())
    {
      continue;
    }
    // e_col adds the integer 1 to its own column of acc, and i_col is 0
    Node step = f[1][col];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, col);
    bool increment = step.getKind() == Kind::ADD && step.getNumChildren() == 2
                     && ((step[0] == own && step[1] == d_one)
                         || (step[1] == own && step[0] == d_one));
    if (increment && i[col].isConst()
        && i[col].getConst<Rational>() == Rational(0))
    {
      return static_cast<int>(col);
    }
  }
  return -1;
}

int BagsRewriter::nullAwareStepKind(const Node& step,
                                    const Node& acc,
                                    Node& arg) const
{
  // step =
  //   (ite (= (as nullable.null (Nullable Int)) A)
  //        acc
  //        (ite (= (as nullable.null (Nullable Int)) acc) A C))
  // with C combining A and acc, or (ite (= .. acc) A C) for an A never null:
  // the step of SQL's SUM, MIN or MAX, which skips nulls and is null over no
  // value. Returns 0 for a sum, 1 for a minimum, 2 for a maximum, -1 for
  // anything else; arg is set to A. Which one C is, is decided by evaluating
  // C at two points, A = (nullable.some 2) with acc = (nullable.some 3) and
  // the other way round: a sum gives 5 both times, a minimum 2, a maximum 3
  if (step.getKind() != Kind::ITE || step[0].getKind() != Kind::EQUAL)
  {
    return -1;
  }
  Node A;
  Node inner;
  if (step[1] == acc && step[2].getKind() == Kind::ITE)
  {
    for (size_t s = 0; s < 2; s++)
    {
      if (step[0][s].isConst() && step[0][s].getNumChildren() == 0
          && step[0][s].getType().isDatatype())
      {
        A = step[0][1 - s];
      }
    }
    inner = step[2];
  }
  if (A.isNull())
  {
    // the argument's null test decided away
    A = step[1];
    inner = step;
  }
  if (A.isNull() || inner[0].getKind() != Kind::EQUAL || inner[1] != A)
  {
    return -1;
  }
  bool accIsNull = false;
  for (size_t s = 0; s < 2; s++)
  {
    accIsNull = accIsNull
                || (inner[0][s] == acc && inner[0][1 - s].isConst()
                    && inner[0][1 - s].getNumChildren() == 0);
  }
  if (!accIsNull)
  {
    return -1;
  }
  TypeNode aType = A.getType();
  TypeNode accType = acc.getType();
  if (aType != accType || !aType.isDatatype())
  {
    return -1;
  }
  // evaluate the combination at two points
  const DType& dt = A.getType().getDType();
  if (dt.getNumConstructors() != 2)
  {
    return -1;
  }
  // the constructor with one argument is some
  size_t someIndex = dt[0].getNumArgs() == 1 ? 0 : 1;
  TypeNode valueType = dt[someIndex][0].getRangeType();
  if (!valueType.isInteger() && !valueType.isReal())
  {
    return -1;
  }
  Node someOp = dt[someIndex].getConstructor();
  auto value = [&](int k) {
    Node c = valueType.isInteger() ? d_nm->mkConstInt(Rational(k))
                                   : d_nm->mkConstReal(Rational(k));
    return d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, someOp, c);
  };
  auto raw = [&](int k) {
    return valueType.isInteger() ? d_nm->mkConstInt(Rational(k))
                                 : d_nm->mkConstReal(Rational(k));
  };
  auto at = [&](int a, int b) {
    Node e = inner[2].substitute(TNode(A), TNode(value(a)));
    if (A.getKind() == Kind::APPLY_CONSTRUCTOR && A.getNumChildren() == 1)
    {
      // the value of a (nullable.some v) argument, read as v, and of an
      // integer v read as a real, (to_real v), which arithmetic reads as v
      e = e.substitute(TNode(A[0]), TNode(raw(a)));
      if (A[0].getKind() == Kind::TO_REAL)
      {
        e = e.substitute(TNode(A[0][0]), TNode(d_nm->mkConstInt(Rational(a))));
      }
    }
    e = e.substitute(TNode(acc), TNode(value(b)));
    return d_rewriter->rewrite(e);
  };
  if (d_rewriter == nullptr)
  {
    return -1;
  }
  Node e23 = at(2, 3);
  Node e32 = at(3, 2);
  if (e23 == value(5) && e32 == value(5))
  {
    arg = A;
    return 0;
  }
  if (e23 == value(2) && e32 == value(2))
  {
    arg = A;
    return 1;
  }
  if (e23 == value(3) && e32 == value(3))
  {
    arg = A;
    return 2;
  }
  return -1;
}

bool BagsRewriter::isCountStep(const Node& step,
                               const Node& acc,
                               const Node& seed) const
{
  // (nullable.some (+ (nullable.val acc) 1)) from (nullable.some 0), or an
  // ite that keeps acc on some rows and does that on the others: COUNT(*)
  // and COUNT(x), the latter as
  //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) t))
  //        acc
  //        (nullable.some (+ (nullable.val acc) 1)))
  auto increments = [&](const Node& t) {
    if (t.getKind() != Kind::APPLY_CONSTRUCTOR || t.getNumChildren() != 1
        || t[0].getKind() != Kind::ADD || t[0].getNumChildren() != 2)
    {
      return false;
    }
    for (size_t k = 0; k < 2; k++)
    {
      if (t[0][1 - k] == d_one && t[0][k].getKind() == Kind::APPLY_SELECTOR
          && t[0][k][0] == acc)
      {
        return true;
      }
    }
    return false;
  };
  bool zero = seed.getKind() == Kind::APPLY_CONSTRUCTOR
              && seed.getNumChildren() == 1 && seed[0].isConst()
              && seed[0].getConst<Rational>().isZero();
  if (!zero)
  {
    return false;
  }
  if (increments(step))
  {
    return true;
  }
  return step.getKind() == Kind::ITE && !occursFree(step[0], acc)
         && ((step[1] == acc && increments(step[2]))
             || (step[2] == acc && increments(step[1])));
}

BagsRewriteResponse BagsRewriter::rewriteAggregateRollup(const TNode& n) const
{
  // AGGREGATE_ROLLUP, for an aggregate of an aggregate,
  //   (bag.map h (bag.filter Q ((_ table.aggr Ko) g j
  //                               (bag.filter P ((_ table.aggr K) f i X)))))
  // the outer aggregate grouping the inner groups by some of their group
  // columns, Ko. Every outer column is a group column; the outer counter, which
  // Q reads only through (>= c 1) and h not at all; a merge of an inner
  // aggregate, a sum of sums or counts, a minimum of minimums or a maximum of
  // maximums; or an aggregate over an inner group column c outside Ko when K is
  // Ko and c: over the inner groups of a key, c takes each of its values once,
  // so that is the aggregate over the distinct values of c. So the outer rows
  // are those of an aggregate over X by Ko of the merged columns, joined on the
  // keys with an aggregate by Ko over the distinct (Ko, c) of X of the others
  // (see rewrites.h). That is how Calcite writes a query with DISTINCT and
  // plain aggregates:
  //   SELECT k, SUM(a), COUNT(DISTINCT c) FROM X GROUP BY k
  // as
  //   SELECT k, SUM(s), COUNT(c)
  //   FROM (SELECT k, c, SUM(a) AS s FROM X GROUP BY k, c) GROUP BY k
  Node h = asLambda(n[0]);
  if (n[1].getKind() != Kind::BAG_FILTER || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node Q = asLambda(n[1][0]);
  Node O = n[1][1];
  if (O.getKind() != Kind::TABLE_AGGREGATE || Q.getKind() != Kind::LAMBDA
      || Q[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node g = asLambda(O[0]);
  Node j = O[1];
  Node Y = O[2];
  if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 2
      || !isTupleTerm(g[1]) || !isTupleTerm(j)
      || Y.getKind() != Kind::BAG_FILTER
      || Y[1].getKind() != Kind::TABLE_AGGREGATE || d_rewriter == nullptr)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node I = Y[1];
  Node f = asLambda(I[0]);
  Node i0 = I[1];
  Node X = I[2];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i0))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  int co = counterColumn(n[1][0], g, j);
  int ci = counterColumn(Y[0], f, i0);
  Node P = asLambda(Y[0]);
  if (co < 0 || ci < 0 || P[1].getKind() == Kind::AND)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // h and Q's other conjuncts never read the outer counter
  {
    std::set<uint32_t> read;
    if (!readPositions(h[1], h[0][0], read) || read.count(co))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node r = Q[0][0];
    std::vector<Node> conjuncts;
    if (Q[1].getKind() == Kind::AND)
    {
      conjuncts.insert(conjuncts.end(), Q[1].begin(), Q[1].end());
    }
    else
    {
      conjuncts.push_back(Q[1]);
    }
    for (const Node& c : conjuncts)
    {
      std::set<uint32_t> pos;
      bool counter = c.getKind() == Kind::GEQ
                     && c[0].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
                     && datatypes::utils::indexOf(c[0].getOperator())
                            == static_cast<size_t>(co);
      if (!counter && (!readPositions(c, r, pos) || pos.count(co)))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
  }
  Node x = f[0][0];
  Node a = f[0][1];
  Node t = g[0][0];
  Node b = g[0][1];
  size_t wI = f[1].getNumChildren();
  size_t wO = g[1].getNumChildren();
  const std::vector<uint32_t>& K =
      I.getOperator().getConst<ProjectOp>().getIndices();
  const std::vector<uint32_t>& Ko =
      O.getOperator().getConst<ProjectOp>().getIndices();
  std::set<uint32_t> Kset(K.begin(), K.end());
  if (Ko.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the inner columns: keys (their column of X) and aggregates (their kind,
  // as nullAwareStepKind gives it, or 3 for a count)
  std::vector<int> keyCol(wI, -1);
  std::vector<int> aggKind(wI, -1);
  for (size_t p = 0; p < wI; p++)
  {
    Node e = f[1][p];
    if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == x)
    {
      uint32_t c = datatypes::utils::indexOf(e.getOperator());
      if (Kset.count(c))
      {
        keyCol[p] = static_cast<int>(c);
      }
      continue;
    }
    Node own = datatypes::TupleUtils::nthElementOfTuple(a, p);
    std::set<uint32_t> accRead;
    if (!readPositions(e, a, accRead) || accRead.size() > 1
        || (accRead.size() == 1 && !accRead.count(p)))
    {
      continue;
    }
    Node arg;
    int k = isNullConstant(i0[p]) ? nullAwareStepKind(e, own, arg) : -1;
    if (k >= 0)
    {
      aggKind[p] = k;
    }
    else if (isCountStep(e, own, i0[p]))
    {
      aggKind[p] = 3;
    }
  }
  // the outer keys, as columns of X, and the inner seeds of their columns,
  // which seed them in the aggregates below: a group's first row replaces
  // them
  std::vector<uint32_t> Cp;
  std::vector<Node> keySeeds;
  for (uint32_t p : Ko)
  {
    if (p >= wI || keyCol[p] < 0)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Cp.push_back(static_cast<uint32_t>(keyCol[p]));
    keySeeds.push_back(i0[p]);
  }
  // the outer columns: a KEY (a copy of an outer group column), the
  // COUNTER, a MERGED inner aggregate, or an aggregate over the DISTINCT
  // values of the inner group column c (distinctCol, a column of X)
  enum Role
  {
    KEY,
    COUNTER,
    MERGED,
    DISTINCT
  };
  std::vector<Role> role(wO, KEY);
  std::vector<size_t> src(wO, 0);
  int distinctCol = -1;
  bool anyMerged = false;
  for (size_t q = 0; q < wO; q++)
  {
    Node e = g[1][q];
    if (q == static_cast<size_t>(co))
    {
      role[q] = COUNTER;
      continue;
    }
    if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == t)
    {
      uint32_t p = datatypes::utils::indexOf(e.getOperator());
      auto at = std::find(Ko.begin(), Ko.end(), p);
      if (at == Ko.end())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      role[q] = KEY;
      src[q] = at - Ko.begin();
      continue;
    }
    // a sum, minimum or maximum over one inner column, or a count of the
    // inner groups where one inner column is not null
    std::set<uint32_t> tRead, bRead;
    Node own = datatypes::TupleUtils::nthElementOfTuple(b, q);
    if (!readPositions(e, t, tRead) || tRead.size() != 1
        || !readPositions(e, b, bRead) || bRead.size() > 1
        || (bRead.size() == 1 && !bRead.count(q)))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node arg;
    int kg = isNullConstant(j[q]) ? nullAwareStepKind(e, own, arg) : -1;
    if (kg < 0 && isCountStep(e, own, j[q]))
    {
      kg = 3;
    }
    if (kg < 0)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    size_t p = *tRead.begin();
    if (kg == 3 && (p >= wI || keyCol[p] < 0))
    {
      // a count of inner aggregates is no merge
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    if (p < wI && aggKind[p] >= 0)
    {
      bool merges = (kg == 0 && (aggKind[p] == 0 || aggKind[p] == 3))
                    || (kg == 1 && aggKind[p] == 1)
                    || (kg == 2 && aggKind[p] == 2);
      if (!merges)
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      role[q] = MERGED;
      src[q] = p;
      anyMerged = true;
      continue;
    }
    if (p < wI && keyCol[p] >= 0
        && std::find(Ko.begin(), Ko.end(), p) == Ko.end())
    {
      if (distinctCol >= 0 && distinctCol != keyCol[p])
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      distinctCol = keyCol[p];
      role[q] = DISTINCT;
      src[q] = p;
      continue;
    }
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  if (distinctCol >= 0)
  {
    // the inner groups are the values of the outer keys and c
    std::set<uint32_t> want(Cp.begin(), Cp.end());
    want.insert(static_cast<uint32_t>(distinctCol));
    if (want != Kset)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  else if (!anyMerged)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode xType = X.getType().getBagElementType();
  std::vector<TypeNode> xTypes = xType.getTupleTypes();
  size_t nk = Cp.size();
  Node one = d_one;
  // the first part: an aggregate over X by Ko of the merged columns and a
  // counter, under the filter by the counter, or, when nothing is merged, the
  // set of the keys of the rows of X
  Node first;
  size_t wA;
  std::vector<size_t> mergedAt(wO, 0);
  if (anyMerged)
  {
    std::vector<TypeNode> types;
    for (uint32_t c : Cp)
    {
      types.push_back(xTypes[c]);
    }
    std::vector<size_t> mergedSrc;
    for (size_t q = 0; q < wO; q++)
    {
      if (role[q] == MERGED)
      {
        mergedAt[q] = nk + mergedSrc.size();
        mergedSrc.push_back(src[q]);
        types.push_back(f[1][src[q]].getType());
      }
    }
    types.push_back(d_nm->integerType());
    TypeNode accType = d_nm->mkTupleType(types);
    Node a2 = NodeManager::mkBoundVar("acc", accType);
    std::vector<Node> cells, seeds;
    for (size_t k = 0; k < nk; k++)
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(x, Cp[k]));
      seeds.push_back(keySeeds[k]);
    }
    for (size_t m = 0; m < mergedSrc.size(); m++)
    {
      size_t p = mergedSrc[m];
      Node own = datatypes::TupleUtils::nthElementOfTuple(a, p);
      Node own2 = datatypes::TupleUtils::nthElementOfTuple(a2, nk + m);
      cells.push_back(f[1][p].substitute(TNode(own), TNode(own2)));
      seeds.push_back(i0[p]);
    }
    Node cnt = datatypes::TupleUtils::nthElementOfTuple(a2, types.size() - 1);
    cells.push_back(d_nm->mkNode(Kind::ADD, cnt, one));
    seeds.push_back(d_zero);
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType, cells, 0, cells.size() - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType, seeds, 0, seeds.size() - 1);
    Node fA = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, a2), body);
    Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(Cp));
    std::vector<Node> children{op, fA, seed, X};
    Node A = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    Node r = rowVariable(accType);
    Node reached = d_nm->mkNode(
        Kind::GEQ,
        datatypes::TupleUtils::nthElementOfTuple(r, types.size() - 1),
        one);
    first = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, reached), A);
    wA = types.size();
  }
  else
  {
    std::vector<Node> cols;
    std::vector<TypeNode> types;
    Node xr = rowVariable(xType);
    for (uint32_t c : Cp)
    {
      cols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, c));
      types.push_back(xTypes[c]);
    }
    TypeNode kt = d_nm->mkTupleType(types);
    Node keys = mkLambda(
        xr,
        datatypes::TupleUtils::constructTupleFromElements(kt, cols, 0, nk - 1));
    first = d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, keys, X));
    wA = nk;
  }
  // the second part: the aggregate by Ko over the set S of the (Ko, c) of the
  // rows of X, under the filter by its counter, joined with the first on the
  // keys
  Node joined = first;
  std::vector<size_t> distinctAt(wO, 0);
  if (distinctCol >= 0)
  {
    std::vector<Node> cols;
    std::vector<TypeNode> stypes;
    Node xr = rowVariable(xType);
    for (uint32_t c : Cp)
    {
      cols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, c));
      stypes.push_back(xTypes[c]);
    }
    cols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, distinctCol));
    stypes.push_back(xTypes[distinctCol]);
    TypeNode sType = d_nm->mkTupleType(stypes);
    Node S = d_nm->mkNode(
        Kind::BAG_SETOF,
        d_nm->mkNode(Kind::BAG_MAP,
                     mkLambda(xr,
                              datatypes::TupleUtils::constructTupleFromElements(
                                  sType, cols, 0, cols.size() - 1)),
                     X));
    std::vector<TypeNode> types(stypes.begin(), stypes.begin() + nk);
    std::vector<size_t> qs;
    for (size_t q = 0; q < wO; q++)
    {
      if (role[q] == DISTINCT)
      {
        distinctAt[q] = nk + qs.size();
        qs.push_back(q);
        types.push_back(g[1][q].getType());
      }
    }
    types.push_back(d_nm->integerType());
    TypeNode accType = d_nm->mkTupleType(types);
    Node sv = NodeManager::mkBoundVar("s", sType);
    Node b2 = NodeManager::mkBoundVar("acc", accType);
    std::vector<Node> cells, seeds;
    for (size_t k = 0; k < nk; k++)
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(sv, k));
      seeds.push_back(keySeeds[k]);
    }
    for (size_t d = 0; d < qs.size(); d++)
    {
      size_t q = qs[d];
      Node col = datatypes::TupleUtils::nthElementOfTuple(t, src[q]);
      Node own = datatypes::TupleUtils::nthElementOfTuple(b, q);
      std::vector<Node> from{col, own};
      std::vector<Node> to{
          datatypes::TupleUtils::nthElementOfTuple(sv, nk),
          datatypes::TupleUtils::nthElementOfTuple(b2, nk + d)};
      cells.push_back(
          g[1][q].substitute(from.begin(), from.end(), to.begin(), to.end()));
      seeds.push_back(j[q]);
    }
    Node cnt = datatypes::TupleUtils::nthElementOfTuple(b2, types.size() - 1);
    cells.push_back(d_nm->mkNode(Kind::ADD, cnt, one));
    seeds.push_back(d_zero);
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType, cells, 0, cells.size() - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType, seeds, 0, seeds.size() - 1);
    Node fB = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, sv, b2), body);
    std::vector<uint32_t> idx;
    for (size_t k = 0; k < nk; k++)
    {
      idx.push_back(static_cast<uint32_t>(k));
    }
    Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(idx));
    std::vector<Node> children{op, fB, seed, S};
    Node B = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    Node r = rowVariable(accType);
    Node reached = d_nm->mkNode(
        Kind::GEQ,
        datatypes::TupleUtils::nthElementOfTuple(r, types.size() - 1),
        one);
    Node second = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, reached), B);
    Node product = d_nm->mkNode(Kind::TABLE_PRODUCT, first, second);
    TypeNode pType = product.getType().getBagElementType();
    Node pr = rowVariable(pType);
    std::vector<Node> equal;
    for (size_t k = 0; k < nk; k++)
    {
      equal.push_back(datatypes::TupleUtils::nthElementOfTuple(pr, k).eqNode(
          datatypes::TupleUtils::nthElementOfTuple(pr, wA + k)));
    }
    Node cond = equal.size() == 1 ? equal[0] : d_nm->mkNode(Kind::AND, equal);
    joined = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(pr, cond), product);
  }
  // the outer rows, rows in the example: the outer aggregate's columns read
  // off the joined rows, with 1 for the counter, which Q tests positive
  TypeNode oType = O.getType().getBagElementType();
  std::vector<TypeNode> oTypes = oType.getTupleTypes();
  TypeNode jType = joined.getType().getBagElementType();
  Node jr = rowVariable(jType);
  std::vector<Node> cells;
  for (size_t q = 0; q < wO; q++)
  {
    Node c;
    switch (role[q])
    {
      case KEY: c = datatypes::TupleUtils::nthElementOfTuple(jr, src[q]); break;
      case COUNTER: c = one; break;
      case MERGED:
        c = datatypes::TupleUtils::nthElementOfTuple(jr, mergedAt[q]);
        break;
      case DISTINCT:
        c = datatypes::TupleUtils::nthElementOfTuple(jr, wA + distinctAt[q]);
        break;
    }
    if (c.getType() != oTypes[q])
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    cells.push_back(c);
  }
  Node rows =
      d_nm->mkNode(Kind::BAG_MAP,
                   mkLambda(jr,
                            datatypes::TupleUtils::constructTupleFromElements(
                                oType, cells, 0, wO - 1)),
                   joined);
  Node ret = d_nm->mkNode(
      Kind::BAG_MAP, n[0], d_nm->mkNode(Kind::BAG_FILTER, n[1][0], rows));
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_ROLLUP);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateJoinMerge(
    const TNode& n) const
{
  // (bag.map h (bag.filter P (table.product C0 (table.product C1 ..)))) with
  // components that are aggregates (see rewrites.h):
  // * AGGREGATE_SETOF_IDEMPOTENT: an aggregate over (bag.setof Y) whose columns
  //   are copies of the columns of the row, minimums, maximums and a counter
  //   that h does not read and P reads only through (>= c 1) is the aggregate
  //   over Y, as a component: duplicate rows change none of those;
  // * AGGREGATE_JOIN_MERGE: two aggregates over one X by the same columns K,
  //   both copying every group column and seeding the copies alike, with P
  //   equating their copies, pair the rows of each group: they are one
  //   aggregate that computes the columns of both, the copies and the counter
  //   of the second read from those of the first. That is SQL's self-join of
  //   two GROUP BY queries over one table, which Calcite merges into one
  //   aggregate.
  Node h = asLambda(n[0]);
  if (n[1].getKind() != Kind::BAG_FILTER || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node P = asLambda(n[1][0]);
  Node T = n[1][1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the components and where their columns start
  std::vector<Node> comps;
  std::vector<size_t> starts;
  {
    Node rest = T;
    size_t at = 0;
    while (true)
    {
      Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
      if (!c.getType().getBagElementType().isTuple())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      comps.push_back(c);
      starts.push_back(at);
      at += c.getType().getBagElementType().getTupleLength();
      if (rest.getKind() != Kind::TABLE_PRODUCT)
      {
        break;
      }
      rest = rest[1];
    }
  }
  Node r = P[0][0];
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  std::set<uint32_t> hRead;
  if (!readPositions(h[1], h[0][0], hRead))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // positions P reads other than through (>= ((_ tuple.select k) r) 1)
  std::set<uint32_t> pRead;
  for (const Node& c : conjuncts)
  {
    if (c.getKind() == Kind::GEQ && c[1].isConst()
        && c[1].getConst<Rational>() == Rational(1)
        && c[0].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r)
    {
      continue;
    }
    if (!readPositions(c, r, pRead))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  auto rebuild = [&](const std::vector<Node>& cs) {
    Node prod = cs.back();
    for (size_t k = cs.size() - 1; k-- > 0;)
    {
      prod = d_nm->mkNode(Kind::TABLE_PRODUCT, cs[k], prod);
    }
    return prod;
  };
  // the counter of an aggregate: its column (+ ((_ tuple.select c) acc) 1)
  // from 0, or -1
  auto counterOf = [&](const Node& A) {
    Node f = asLambda(A[0]);
    if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
        || !isTupleTerm(f[1]))
    {
      return -1;
    }
    Node row = rowVariable(A.getType().getBagElementType());
    for (size_t c = 0; c < f[1].getNumChildren(); c++)
    {
      Node local = mkLambda(
          row,
          d_nm->mkNode(Kind::GEQ,
                       datatypes::TupleUtils::nthElementOfTuple(row, c),
                       d_one));
      if (counterColumn(local, f, A[1]) == static_cast<int>(c))
      {
        return static_cast<int>(c);
      }
    }
    return -1;
  };
  // 1. an idempotent aggregate over a bag.setof
  for (size_t i = 0; i < comps.size(); i++)
  {
    const Node& A = comps[i];
    if (A.getKind() != Kind::TABLE_AGGREGATE
        || A[2].getKind() != Kind::BAG_SETOF)
    {
      continue;
    }
    Node f = asLambda(A[0]);
    int cnt = counterOf(A);
    if (cnt < 0 || hRead.count(starts[i] + cnt) || pRead.count(starts[i] + cnt))
    {
      continue;
    }
    bool idempotent = true;
    for (size_t c = 0; c < f[1].getNumChildren() && idempotent; c++)
    {
      const Node& e = f[1][c];
      if (static_cast<int>(c) == cnt
          || (e.getKind() == Kind::APPLY_SELECTOR && e[0] == f[0][0]))
      {
        continue;
      }
      Node arg;
      int k = nullAwareStepKind(
          e, datatypes::TupleUtils::nthElementOfTuple(f[0][1], c), arg);
      idempotent = k == 1 || k == 2;
    }
    if (!idempotent)
    {
      continue;
    }
    std::vector<Node> children{A.getOperator(), A[0], A[1], A[2][0]};
    std::vector<Node> cs = comps;
    cs[i] = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    Node ret =
        d_nm->mkNode(Kind::BAG_MAP,
                     n[0],
                     d_nm->mkNode(Kind::BAG_FILTER, n[1][0], rebuild(cs)));
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_SETOF_IDEMPOTENT);
  }
  // 2. two aggregates over one X by the same columns
  for (size_t i = 0; i < comps.size(); i++)
  {
    for (size_t j = i + 1; j < comps.size(); j++)
    {
      const Node& A = comps[i];
      const Node& B = comps[j];
      if (A.getKind() != Kind::TABLE_AGGREGATE
          || B.getKind() != Kind::TABLE_AGGREGATE || A[2] != B[2])
      {
        continue;
      }
      Node opA = A.getOperator();
      Node opB = B.getOperator();
      if (opA != opB)
      {
        continue;
      }
      Node fa = asLambda(A[0]);
      Node fb = asLambda(B[0]);
      if (fa.getKind() != Kind::LAMBDA || fb.getKind() != Kind::LAMBDA
          || !isTupleTerm(fa[1]) || !isTupleTerm(fb[1]) || !isTupleTerm(A[1])
          || !isTupleTerm(B[1]))
      {
        continue;
      }
      const std::vector<uint32_t>& K =
          A.getOperator().getConst<ProjectOp>().getIndices();
      if (K.empty())
      {
        continue;
      }
      // where each copies each key column
      auto keyPositions = [&](const Node& f, std::map<uint32_t, size_t>& at) {
        for (size_t p = 0; p < f[1].getNumChildren(); p++)
        {
          const Node& e = f[1][p];
          if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == f[0][0])
          {
            uint32_t c = datatypes::utils::indexOf(e.getOperator());
            if (std::find(K.begin(), K.end(), c) != K.end() && !at.count(c))
            {
              at[c] = p;
            }
          }
        }
        return at.size() == std::set<uint32_t>(K.begin(), K.end()).size();
      };
      std::map<uint32_t, size_t> ka, kb;
      if (!keyPositions(fa, ka) || !keyPositions(fb, kb))
      {
        continue;
      }
      // the two seed the key copies alike: over an empty X the two rows of
      // initial values meet, and the merged row must read the same values
      // for B's key copies from A's
      bool sameSeeds = true;
      for (const std::pair<const uint32_t, size_t>& kv : ka)
      {
        sameSeeds = sameSeeds && A[1][kv.second] == B[1][kb[kv.first]];
      }
      if (!sameSeeds)
      {
        continue;
      }
      int ca = counterOf(A);
      int cb = counterOf(B);
      // P equates every pair of key columns
      std::vector<bool> used(conjuncts.size(), false);
      bool joined = true;
      for (const std::pair<const uint32_t, size_t>& kv : ka)
      {
        uint32_t pa = starts[i] + kv.second;
        uint32_t pb = starts[j] + kb[kv.first];
        bool found = false;
        for (size_t c = 0; c < conjuncts.size() && !found; c++)
        {
          const Node& e = conjuncts[c];
          if (e.getKind() != Kind::EQUAL
              || e[0].getKind() != Kind::APPLY_SELECTOR
              || e[1].getKind() != Kind::APPLY_SELECTOR || e[0][0] != r
              || e[1][0] != r)
          {
            continue;
          }
          uint32_t x0 = datatypes::utils::indexOf(e[0].getOperator());
          uint32_t x1 = datatypes::utils::indexOf(e[1].getOperator());
          if ((x0 == pa && x1 == pb) || (x0 == pb && x1 == pa))
          {
            used[c] = true;
            found = true;
          }
        }
        joined = joined && found;
      }
      if (!joined)
      {
        continue;
      }
      // the merged aggregate: A's columns, then B's others; bAt[p] is where
      // B's column p is in the merged rows
      size_t wa = fa[1].getNumChildren();
      size_t wb = fb[1].getNumChildren();
      std::vector<TypeNode> types =
          A.getType().getBagElementType().getTupleTypes();
      std::vector<TypeNode> btypes =
          B.getType().getBagElementType().getTupleTypes();
      std::vector<int> bAt(wb, -1);  // where B's column p is in the merged rows
      for (const std::pair<const uint32_t, size_t>& kv : kb)
      {
        bAt[kv.second] = static_cast<int>(ka[kv.first]);
      }
      if (cb >= 0 && ca >= 0)
      {
        bAt[cb] = ca;
      }
      std::vector<size_t> extra;
      for (size_t p = 0; p < wb; p++)
      {
        if (bAt[p] < 0)
        {
          bAt[p] = static_cast<int>(wa + extra.size());
          extra.push_back(p);
          types.push_back(btypes[p]);
        }
      }
      TypeNode accType = d_nm->mkTupleType(types);
      Node acc = NodeManager::mkBoundVar("acc", accType);
      Node x = fa[0][0];
      std::vector<Node> from, to;
      for (size_t p = 0; p < wa; p++)
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(fa[0][1], p));
        to.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, p));
      }
      std::vector<Node> fromB{fb[0][0]}, toB{x};
      for (size_t p = 0; p < wb; p++)
      {
        fromB.push_back(datatypes::TupleUtils::nthElementOfTuple(fb[0][1], p));
        toB.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, bAt[p]));
      }
      std::vector<Node> cells, seeds;
      for (size_t p = 0; p < wa; p++)
      {
        cells.push_back(fa[1][p].substitute(
            from.begin(), from.end(), to.begin(), to.end()));
        seeds.push_back(A[1][p]);
      }
      for (size_t p : extra)
      {
        cells.push_back(fb[1][p].substitute(
            fromB.begin(), fromB.end(), toB.begin(), toB.end()));
        seeds.push_back(B[1][p]);
      }
      Node body = datatypes::TupleUtils::constructTupleFromElements(
          accType, cells, 0, cells.size() - 1);
      Node seed = datatypes::TupleUtils::constructTupleFromElements(
          accType, seeds, 0, seeds.size() - 1);
      Node fm = d_nm->mkNode(
          Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc), body);
      std::vector<Node> children{A.getOperator(), fm, seed, A[2]};
      Node M = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      // the new components and where every old column went
      std::vector<Node> cs;
      std::vector<size_t> newStart(comps.size(), 0);
      size_t at = 0;
      for (size_t c = 0; c < comps.size(); c++)
      {
        if (c == j)
        {
          continue;
        }
        newStart[c] = at;
        cs.push_back(c == i ? M : comps[c]);
        at += (c == i ? M : comps[c])
                  .getType()
                  .getBagElementType()
                  .getTupleLength();
      }
      TypeNode newRow = rebuild(cs).getType().getBagElementType();
      Node r2 = rowVariable(newRow);
      std::vector<Node> oldSel, newSel;
      for (size_t c = 0; c < comps.size(); c++)
      {
        size_t w = comps[c].getType().getBagElementType().getTupleLength();
        for (size_t p = 0; p < w; p++)
        {
          size_t to2 = c == j ? newStart[i] + bAt[p] : newStart[c] + p;
          oldSel.push_back(
              datatypes::TupleUtils::nthElementOfTuple(r, starts[c] + p));
          newSel.push_back(datatypes::TupleUtils::nthElementOfTuple(r2, to2));
        }
      }
      std::vector<Node> kept;
      for (size_t c = 0; c < conjuncts.size(); c++)
      {
        if (!used[c])
        {
          kept.push_back(conjuncts[c].substitute(
              oldSel.begin(), oldSel.end(), newSel.begin(), newSel.end()));
        }
      }
      Node pBody =
          kept.empty()
              ? d_nm->mkConst(true)
              : (kept.size() == 1 ? kept[0] : d_nm->mkNode(Kind::AND, kept));
      std::vector<Node> oldH, newH;
      Node hv = h[0][0];
      for (size_t c = 0; c < oldSel.size(); c++)
      {
        oldH.push_back(datatypes::TupleUtils::nthElementOfTuple(hv, c));
        newH.push_back(newSel[c]);
      }
      Node hBody =
          h[1].substitute(oldH.begin(), oldH.end(), newH.begin(), newH.end());
      if (occursFree(pBody, r) || occursFree(hBody, hv))
      {
        continue;
      }
      Node ret = d_nm->mkNode(
          Kind::BAG_MAP,
          {mkLambda(r2, hBody),
           d_nm->mkNode(Kind::BAG_FILTER, {mkLambda(r2, pBody), rebuild(cs)})});
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_JOIN_MERGE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateCollapse(const TNode& n) const
{
  // AGGREGATE_COLLAPSE, for an aggregate over a union of aggregates, the
  // pattern of an aggregate pushed through a UNION ALL,
  //   (bag.map h (bag.filter Q ((_ table.aggr Ko) g j
  //                               (bag.union_disjoint P1 P2))))
  // where every Pi is (bag.map pi (bag.filter Qi ((_ table.aggr K) f i0 Xi)))
  // with one pi, Qi, K, f and i0, the inner aggregates grouped by exactly the
  // outer group columns, and g merging the columns of f: a sum of counts or of
  // sums, a minimum of minimums, a maximum of maximums. A group of the outer
  // aggregate has one row per part that its key reached, the fold of the part
  // over the rows of Xi with the key, so their merge is the fold of f over the
  // rows with the key of all the Xi (see rewrites.h). The result maps each
  // inner row r to h of (g r j), the outer row that the outer step from j gives
  // on r, through pi, and filters by the test of the inner counter with the
  // other conjuncts of Q on that row. Q and h must read the outer counter only
  // through (>= c 1): its value, the number of parts, is no column here. In
  // SQL,
  //   SELECT k, SUM(c) FROM (SELECT k, COUNT(*) AS c FROM X1 GROUP BY k
  //     UNION ALL SELECT k, COUNT(*) FROM X2 GROUP BY k) GROUP BY k
  // is SELECT k, COUNT(*) FROM (X1 UNION ALL X2) GROUP BY k.
  Node h = asLambda(n[0]);
  if (n[1].getKind() != Kind::BAG_FILTER || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node Q = asLambda(n[1][0]);
  Node outer = n[1][1];
  if (outer.getKind() != Kind::TABLE_AGGREGATE || Q.getKind() != Kind::LAMBDA
      || Q[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node g = outer[0];
  Node j = outer[1];
  int co = counterColumn(n[1][0], g, j);
  if (co < 0)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node y = g[0][0];
  Node b = g[0][1];
  // h and Q's other conjuncts never read the outer counter
  std::set<uint32_t> hRead;
  if (!readPositions(h[1], h[0][0], hRead) || hRead.count(co))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> qOthers;
  {
    std::vector<Node> conjuncts;
    if (Q[1].getKind() == Kind::AND)
    {
      conjuncts.insert(conjuncts.end(), Q[1].begin(), Q[1].end());
    }
    else
    {
      conjuncts.push_back(Q[1]);
    }
    for (const Node& c : conjuncts)
    {
      std::set<uint32_t> pos;
      if (!readPositions(c, Q[0][0], pos))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      if (pos.count(co))
      {
        if (pos.size() != 1 || c.getKind() != Kind::GEQ)
        {
          return BagsRewriteResponse(n, Rewrite::NONE);
        }
        continue;
      }
      qOthers.push_back(c);
    }
  }
  // the parts
  std::vector<Node> parts;
  std::vector<Node> todo{outer[2]};
  while (!todo.empty())
  {
    Node c = todo.back();
    todo.pop_back();
    if (c.getKind() == Kind::BAG_UNION_DISJOINT)
    {
      todo.push_back(c[1]);
      todo.push_back(c[0]);
    }
    else
    {
      parts.push_back(c);
    }
  }
  if (parts.size() < 2)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // a part is (bag.map pi (bag.filter Qi aggr)), or (bag.filter Qi aggr)
  // when the projection was absorbed above; belowMap gives the filter
  auto belowMap = [](const Node& p) {
    return p.getKind() == Kind::BAG_MAP ? p[1] : p;
  };
  Node first = parts[0];
  Node pi = first.getKind() == Kind::BAG_MAP ? first[0] : Node::null();
  if (belowMap(first).getKind() != Kind::BAG_FILTER
      || belowMap(first)[1].getKind() != Kind::TABLE_AGGREGATE)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node Qi = belowMap(first)[0];
  Node innerAggr = belowMap(first)[1];
  Node f = innerAggr[0];
  Node i0 = innerAggr[1];
  Node innerOp = innerAggr.getOperator();
  std::vector<Node> inputs;
  for (const Node& p : parts)
  {
    Node pPi = p.getKind() == Kind::BAG_MAP ? p[0] : Node::null();
    Node q = belowMap(p);
    if (pPi != pi || q.getKind() != Kind::BAG_FILTER || q[0] != Qi
        || q[1].getKind() != Kind::TABLE_AGGREGATE
        || q[1].getOperator() != innerOp || q[1][0] != f || q[1][1] != i0)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    inputs.push_back(q[1][2]);
  }
  int ci = counterColumn(Qi, f, i0);
  std::vector<uint32_t> J;
  if (pi.isNull())
  {
    for (uint32_t k = 0; k < f[1].getNumChildren(); k++)
    {
      J.push_back(k);
    }
  }
  else
  {
    J = projectionIndices(pi);
  }
  if (ci < 0 || J.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  {
    // Qi is only the counter's conjunct
    Node lambda = asLambda(Qi);
    if (lambda[1].getKind() == Kind::AND)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  // the outer keys are the inner keys
  const std::vector<uint32_t>& Ko =
      outer.getOperator().getConst<ProjectOp>().getIndices();
  const std::vector<uint32_t>& K =
      innerAggr.getOperator().getConst<ProjectOp>().getIndices();
  std::set<uint32_t> covered;
  for (uint32_t q : Ko)
  {
    if (q >= J.size())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node c = f[1][J[q]];
    if (c.getKind() != Kind::APPLY_SELECTOR || c[0] != x)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    covered.insert(datatypes::utils::indexOf(c.getOperator()));
  }
  if (covered != std::set<uint32_t>(K.begin(), K.end()))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // each outer column: a key, the counter, or a merge of a column of f
  for (size_t o = 0, m = g[1].getNumChildren(); o < m; o++)
  {
    if (static_cast<int>(o) == co)
    {
      continue;
    }
    Node c = g[1][o];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == y
        && std::find(
               Ko.begin(), Ko.end(), datatypes::utils::indexOf(c.getOperator()))
               != Ko.end())
    {
      continue;
    }
    Node arg;
    int outerKind = nullAwareStepKind(
        c, datatypes::TupleUtils::nthElementOfTuple(b, o), arg);
    if (outerKind < 0 || j[o].getKind() != Kind::APPLY_CONSTRUCTOR
        || j[o].getNumChildren() != 0)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    std::set<uint32_t> pos;
    if (!readPositions(arg, y, pos) || pos.size() != 1 || occursFree(arg, b))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    uint32_t q = *pos.begin();
    if (q >= J.size())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    uint32_t p = J[q];
    Node innerStep = f[1][p];
    Node innerAcc = datatypes::TupleUtils::nthElementOfTuple(acc, p);
    bool ok = false;
    if (outerKind == 0)
    {
      Node unused;
      ok = isCountStep(innerStep, innerAcc, i0[p])
           || (nullAwareStepKind(innerStep, innerAcc, unused) == 0
               && i0[p].getKind() == Kind::APPLY_CONSTRUCTOR
               && i0[p].getNumChildren() == 0);
    }
    else
    {
      Node unused;
      ok = nullAwareStepKind(innerStep, innerAcc, unused) == outerKind
           && i0[p].getKind() == Kind::APPLY_CONSTRUCTOR
           && i0[p].getNumChildren() == 0;
    }
    if (!ok)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // the collapsed aggregate over the union of the inputs,
  // ((_ table.aggr K) f i0 (bag.union_disjoint X1 X2))
  Node u = inputs[0];
  for (size_t k = 1; k < inputs.size(); k++)
  {
    u = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, u, inputs[k]);
  }
  std::vector<Node> children{innerAggr.getOperator(), f, i0, u};
  Node collapsed = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  TypeNode innerRow = collapsed.getType().getBagElementType();
  Node r = rowVariable(innerRow);
  Node view = pi.isNull() ? r : applyFunction(pi, r);
  if (view.isNull() || bindsVariable(g[1], y) || bindsVariable(g[1], b)
      || expr::hasSubterm(g[1], r))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> from{y, b};
  std::vector<Node> to{view, j};
  Node outerRow =
      g[1].substitute(from.begin(), from.end(), to.begin(), to.end());
  Node hBody = applyFunction(n[0], outerRow);
  if (hBody.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> keep{d_nm->mkNode(
      Kind::GEQ, datatypes::TupleUtils::nthElementOfTuple(r, ci), d_one)};
  for (const Node& c : qOthers)
  {
    Node moved = c.substitute(TNode(Q[0][0]), TNode(outerRow));
    keep.push_back(moved);
  }
  Node filterBody = keep.size() == 1 ? keep[0] : d_nm->mkNode(Kind::AND, keep);
  Node filtered =
      d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, filterBody), collapsed);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(r, hBody), filtered);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_COLLAPSE);
}

Node BagsRewriter::dropKnownMemberships(const Node& body,
                                        const Node& t,
                                        const Node& A) const
{
  // FILTER_KNOWN_MEMBERSHIP: the conjuncts of the body of a filter over rows t
  // of A that say what holds of every such row, or what another conjunct says,
  // go (see rewrites.h):
  // * (>= (bag.count (g c) (bag.map g X)) 1), where c is the part of t that a
  //   component X of A, or a filter over X, gives: c is a row of X;
  // * the same where the component is an aggregate over X, or a map of X, in a
  //   group some row of X reached, and g reads only its group columns: some row
  //   of X has those values;
  // * (>= (bag.count E' (bag.map g' X)) 1) beside
  //   (>= (bag.count E (bag.map g X)) 1), where g' and E' select columns of g
  //   and E: the second says it.
  // It is the membership that SQL's IN (SELECT a FROM X) leaves after a join
  // with X.
  if (d_rewriter == nullptr)
  {
    return body;
  }
  auto membership = [](const Node& c, Node& E, Node& g, Node& X) {
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::BAG_COUNT
        || c[0][1].getKind() != Kind::BAG_MAP)
    {
      return false;
    }
    E = c[0][0];
    g = c[0][1][0];
    X = c[0][1][1];
    return true;
  };
  // the components of A and where their columns start
  std::vector<Node> comps;
  std::vector<size_t> starts;
  {
    Node rest = A;
    size_t at = 0;
    while (true)
    {
      Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
      if (!c.getType().getBagElementType().isTuple())
      {
        return body;
      }
      comps.push_back(c);
      starts.push_back(at);
      at += c.getType().getBagElementType().getTupleLength();
      if (rest.getKind() != Kind::TABLE_PRODUCT)
      {
        break;
      }
      rest = rest[1];
    }
  }
  std::vector<Node> conjuncts;
  if (body.getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), body.begin(), body.end());
  }
  else
  {
    conjuncts.push_back(body);
  }
  std::vector<bool> drop(conjuncts.size(), false);
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    Node E, g, X;
    if (!membership(conjuncts[k], E, g, X))
    {
      continue;
    }
    // the group key of a component that is an aggregate over X, or a filter
    // over one, in a group some row of X reached
    for (size_t c = 0; c < comps.size() && !drop[k]; c++)
    {
      Node base = comps[c];
      bool reached = false;
      while (base.getKind() == Kind::BAG_FILTER)
      {
        if (base[1].getKind() == Kind::TABLE_AGGREGATE
            && counterColumn(base[0], asLambda(base[1][0]), base[1][1]) >= 0)
        {
          reached = true;
        }
        base = base[1];
      }
      if (base.getKind() != Kind::TABLE_AGGREGATE)
      {
        continue;
      }
      // the aggregate's input: X, or rows (bag.map g2 X) under a bag.setof
      Node input = base[2];
      if (input.getKind() == Kind::BAG_SETOF)
      {
        input = input[0];
      }
      Node g2;
      if (input != X && input.getKind() == Kind::BAG_MAP && input[1] == X)
      {
        g2 = asLambda(input[0]);
        if (g2.getKind() != Kind::LAMBDA || g2[0].getNumChildren() != 1
            || !isTupleTerm(g2[1]))
        {
          continue;
        }
      }
      else if (input != X || base[2].getKind() == Kind::BAG_SETOF)
      {
        continue;
      }
      Node fa = asLambda(base[0]);
      if (fa.getKind() != Kind::LAMBDA || fa[0].getNumChildren() != 2
          || !isTupleTerm(fa[1]))
      {
        continue;
      }
      if (!reached)
      {
        // or the body asks the component's counter to be positive
        Node r = rowVariable(base.getType().getBagElementType());
        for (const Node& d : conjuncts)
        {
          if (d.getKind() == Kind::GEQ && d[1].isConst()
              && d[1].getConst<Rational>() == Rational(1)
              && d[0].getKind() == Kind::APPLY_SELECTOR && d[0][0] == t)
          {
            size_t pos = datatypes::utils::indexOf(d[0].getOperator());
            size_t w = base.getType().getBagElementType().getTupleLength();
            if (pos >= starts[c] && pos < starts[c] + w)
            {
              Node local = mkLambda(
                  r,
                  d_nm->mkNode(Kind::GEQ,
                               datatypes::TupleUtils::nthElementOfTuple(
                                   r, pos - starts[c]),
                               d_one));
              reached = reached
                        || counterColumn(local, fa, base[1])
                               == static_cast<int>(pos - starts[c]);
            }
          }
        }
      }
      if (!reached)
      {
        continue;
      }
      // a row of X with the group's key columns, and placeholders (fresh
      // variables, holes) elsewhere: g must not read the holes
      TypeNode xt = X.getType().getBagElementType();
      size_t wx = xt.getTupleLength();
      std::vector<Node> cells(wx);
      std::vector<Node> holes;
      for (size_t p = 0; p < fa[1].getNumChildren(); p++)
      {
        const Node& e = fa[1][p];
        if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == fa[0][0])
        {
          size_t col = datatypes::utils::indexOf(e.getOperator());
          const std::vector<uint32_t>& K =
              base.getOperator().getConst<ProjectOp>().getIndices();
          if (std::find(K.begin(), K.end(), col) == K.end())
          {
            continue;
          }
          if (!g2.isNull())
          {
            // column col of the input is g2's column col of a row of X
            const Node& ge = g2[1][col];
            if (ge.getKind() != Kind::APPLY_SELECTOR || ge[0] != g2[0][0])
            {
              continue;
            }
            col = datatypes::utils::indexOf(ge.getOperator());
          }
          if (col < wx && cells[col].isNull())
          {
            cells[col] =
                datatypes::TupleUtils::nthElementOfTuple(t, starts[c] + p);
          }
        }
      }
      std::vector<TypeNode> xtypes = xt.getTupleTypes();
      for (size_t col = 0; col < wx; col++)
      {
        if (cells[col].isNull())
        {
          cells[col] = NodeManager::mkBoundVar("hole", xtypes[col]);
          holes.push_back(cells[col]);
        }
      }
      Node view = datatypes::TupleUtils::constructTupleFromElements(
          xt, cells, 0, wx - 1);
      Node applied = applyFunction(g, view);
      if (applied.isNull())
      {
        continue;
      }
      applied = d_rewriter->rewrite(applied);
      bool closed = true;
      for (const Node& h : holes)
      {
        closed = closed && !expr::hasSubterm(applied, h);
      }
      if (closed && applied == E)
      {
        drop[k] = true;
      }
    }
    // a row of a component that is X or a filter over X
    for (size_t c = 0; c < comps.size() && !drop[k]; c++)
    {
      Node base = comps[c];
      while (base.getKind() == Kind::BAG_FILTER)
      {
        base = base[1];
      }
      if (base != X)
      {
        continue;
      }
      size_t w = X.getType().getBagElementType().getTupleLength();
      std::vector<Node> cells;
      for (size_t i = 0; i < w; i++)
      {
        cells.push_back(
            datatypes::TupleUtils::nthElementOfTuple(t, starts[c] + i));
      }
      Node view = datatypes::TupleUtils::constructTupleFromElements(
          X.getType().getBagElementType(), cells, 0, w - 1);
      Node applied = applyFunction(g, view);
      if (!applied.isNull() && d_rewriter->rewrite(applied) == E)
      {
        drop[k] = true;
      }
    }
    if (drop[k])
    {
      continue;
    }
    // implied by another membership in a map of X with more columns
    std::vector<uint32_t> J = projectionIndices(asLambda(g));
    if (J.empty() || !isTupleTerm(E))
    {
      continue;
    }
    for (size_t o = 0; o < conjuncts.size() && !drop[k]; o++)
    {
      Node E2, g2, X2;
      if (o == k || drop[o] || !membership(conjuncts[o], E2, g2, X2) || X2 != X
          || !isTupleTerm(E2))
      {
        continue;
      }
      std::vector<uint32_t> J2 = projectionIndices(asLambda(g2));
      if (J2.empty() || J2.size() <= J.size())
      {
        continue;
      }
      bool implied = true;
      for (size_t q = 0; q < J.size() && implied; q++)
      {
        bool found = false;
        for (size_t q2 = 0; q2 < J2.size() && !found; q2++)
        {
          found = J2[q2] == J[q] && E2[q2] == E[q];
        }
        implied = found;
      }
      drop[k] = implied;
    }
  }
  std::vector<Node> kept;
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (!drop[k])
    {
      kept.push_back(conjuncts[k]);
    }
  }
  if (kept.size() == conjuncts.size())
  {
    return body;
  }
  if (kept.empty())
  {
    return d_nm->mkConst(true);
  }
  return kept.size() == 1 ? kept[0] : d_nm->mkNode(Kind::AND, kept);
}

bool BagsRewriter::isSet(const Node& X) const
{
  // whether no element of X occurs twice, syntactically: a bag.setof, a table
  // with a key, a filter over a set, a product of sets, or a map over one of
  // these that keeps, of every component, all its columns or a key. With the
  // key {0} of X and of Y, both of two columns, true for
  //   (bag.map
  //     (lambda ((t (Tuple Int Int Int Int)))
  //       (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
  //     (table.product X Y))
  if (X.getType().getBagElementType().isTuple() && !rowKeys(X).empty())
  {
    return true;
  }
  switch (X.getKind())
  {
    case Kind::BAG_SETOF: return true;
    case Kind::BAG_EMPTY: return true;
    case Kind::BAG_INTER_MIN: return isSet(X[0]) || isSet(X[1]);
    case Kind::BAG_FILTER: return isSet(X[1]);
    case Kind::TABLE_PRODUCT: return isSet(X[0]) && isSet(X[1]);
    case Kind::TABLE_AGGREGATE: return !rowKeys(X).empty();
    case Kind::BAG_MAP:
    {
      Node Y = X[1];
      if (!isSet(Y))
      {
        return false;
      }
      std::vector<uint32_t> J = projectionIndices(asLambda(X[0]));
      if (J.empty())
      {
        return false;
      }
      std::set<uint32_t> kept(J.begin(), J.end());
      // the components of Y, below the filters over it
      std::vector<Node> comps;
      Node rest = Y;
      while (rest.getKind() == Kind::BAG_FILTER)
      {
        rest = rest[1];
      }
      while (rest.getKind() == Kind::TABLE_PRODUCT)
      {
        comps.push_back(rest[0]);
        rest = rest[1];
      }
      comps.push_back(rest);
      size_t at = 0;
      for (const Node& c : comps)
      {
        TypeNode t = c.getType().getBagElementType();
        if (!t.isTuple())
        {
          return false;
        }
        size_t w = t.getTupleLength();
        bool all = true;
        for (size_t k = 0; k < w; k++)
        {
          all = all && kept.count(at + k) > 0;
        }
        bool key = false;
        for (const std::set<uint32_t>& K : keysOf(c))
        {
          bool covered = true;
          for (uint32_t k : K)
          {
            covered = covered && kept.count(at + k) > 0;
          }
          key = key || covered;
        }
        if (!all && !key)
        {
          return false;
        }
        at += w;
      }
      return true;
    }
    default: return X.isVar() && !keysOf(X).empty();
  }
}

BagsRewriteResponse BagsRewriter::rewriteSetofPushdown(const TNode& n) const
{
  // SETOF_PUSHDOWN: under duplicate removal only membership counts, so each
  // component of a product may be replaced by the set of the columns that g and
  // the rest of p read of it, after the conjuncts of p that read that component
  // alone (see rewrites.h):
  //   (bag.setof (bag.map g (bag.filter p (table.product C1 C2))))
  //   --->
  //   (bag.setof (bag.map g' (bag.filter p' (table.product
  //     (bag.setof (bag.map pi1 (bag.filter p1 C1)))
  //     (bag.setof (bag.map pi2 (bag.filter p2 C2)))))))
  // where pi1 projects C1 onto the columns read, p1 is the conjuncts of p on C1
  // alone, and g' and p' read the projected columns. A component that is a set
  // whose rows those columns tell apart, all of them or a key, stays, with its
  // conjuncts above. That is SQL's SELECT DISTINCT over a join, which Calcite
  // may write with the DISTINCT pushed into a side.
  Node inner = n[0];
  if (inner.getKind() != Kind::BAG_MAP)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node g = asLambda(inner[0]);
  Node F = inner[1];
  Node P;
  Node prod = F;
  if (F.getKind() == Kind::BAG_FILTER)
  {
    P = asLambda(F[0]);
    prod = F[1];
  }
  if (prod.getKind() != Kind::TABLE_PRODUCT || g.getKind() != Kind::LAMBDA
      || g[0].getNumChildren() != 1
      || (!P.isNull()
          && (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::set<uint32_t> gRead;
  if (!readPositions(g[1], g[0][0], gRead) || bindsVariable(g[1], g[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> comps;
  Node rest = prod;
  while (rest.getKind() == Kind::TABLE_PRODUCT)
  {
    comps.push_back(rest[0]);
    rest = rest[1];
  }
  comps.push_back(rest);
  std::vector<size_t> starts, widths;
  size_t total = 0;
  for (const Node& c : comps)
  {
    TypeNode t = c.getType().getBagElementType();
    if (!t.isTuple())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    starts.push_back(total);
    widths.push_back(t.getTupleLength());
    total += t.getTupleLength();
  }
  auto compOf = [&](uint32_t pos) {
    for (size_t k = 0; k < comps.size(); k++)
    {
      if (pos >= starts[k] && pos < starts[k] + widths[k])
      {
        return static_cast<int>(k);
      }
    }
    return -1;
  };
  // the conjuncts, and the one component each reads alone (-1 for several)
  std::vector<Node> conjuncts;
  std::vector<int> owner;
  std::vector<std::set<uint32_t>> creads;
  if (!P.isNull())
  {
    Node pt = P[0][0];
    if (bindsVariable(P[1], pt))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    if (P[1].getKind() == Kind::AND)
    {
      conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
    }
    else
    {
      conjuncts.push_back(P[1]);
    }
    for (const Node& c : conjuncts)
    {
      std::set<uint32_t> pos;
      if (!readPositions(c, pt, pos))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      int o = -2;
      for (uint32_t q : pos)
      {
        int k = compOf(q);
        o = o == -2 ? k : (o == k ? o : -1);
      }
      owner.push_back(o == -2 ? -1 : o);
      creads.push_back(pos);
    }
  }
  // global reads: g and the conjuncts reading several components
  std::set<uint32_t> global = gRead;
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (owner[k] < 0)
    {
      global.insert(creads[k].begin(), creads[k].end());
    }
  }
  std::vector<bool> keep(comps.size(), false);
  for (size_t c = 0; c < comps.size(); c++)
  {
    bool all = true;
    for (size_t k = 0; k < widths[c]; k++)
    {
      all = all && global.count(starts[c] + k) > 0;
    }
    bool keyRead = false;
    for (const std::set<uint32_t>& K : keysOf(comps[c]))
    {
      bool covered = true;
      for (uint32_t k : K)
      {
        covered = covered && global.count(starts[c] + k) > 0;
      }
      keyRead = keyRead || covered;
    }
    keep[c] = (all || keyRead) && isSet(comps[c]);
  }
  // a kept component's own conjuncts stay above, and so do the columns they
  // read
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (owner[k] >= 0 && keep[owner[k]])
    {
      global.insert(creads[k].begin(), creads[k].end());
    }
  }
  bool changed = false;
  std::vector<Node> newComps;
  std::map<uint32_t, uint32_t> moved;
  size_t newAt = 0;
  for (size_t c = 0; c < comps.size(); c++)
  {
    if (keep[c])
    {
      newComps.push_back(comps[c]);
      for (size_t k = 0; k < widths[c]; k++)
      {
        moved[starts[c] + k] = newAt + k;
      }
      newAt += widths[c];
      continue;
    }
    changed = true;
    TypeNode t = comps[c].getType().getBagElementType();
    Node v = rowVariable(t);
    // the component's own conjuncts, over its own rows
    std::vector<Node> local;
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      if (owner[k] != static_cast<int>(c))
      {
        continue;
      }
      std::vector<Node> from, to;
      for (size_t i = 0; i < widths[c]; i++)
      {
        from.push_back(
            datatypes::TupleUtils::nthElementOfTuple(P[0][0], starts[c] + i));
        to.push_back(datatypes::TupleUtils::nthElementOfTuple(v, i));
      }
      Node l = conjuncts[k].substitute(
          from.begin(), from.end(), to.begin(), to.end());
      if (occursFree(l, P[0][0]))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
      local.push_back(l);
    }
    Node source = comps[c];
    if (!local.empty())
    {
      Node body = local.size() == 1 ? local[0] : d_nm->mkNode(Kind::AND, local);
      source = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(v, body), source);
    }
    std::vector<uint32_t> cols;
    for (size_t k = 0; k < widths[c]; k++)
    {
      if (global.count(starts[c] + k))
      {
        cols.push_back(k);
      }
    }
    if (cols.empty())
    {
      // nothing reads it: whether it has a row that passes is all it says
      cols.push_back(0);
    }
    std::vector<Node> sel;
    std::vector<TypeNode> types;
    for (uint32_t k : cols)
    {
      sel.push_back(datatypes::TupleUtils::nthElementOfTuple(v, k));
      types.push_back(t.getTupleTypes()[k]);
    }
    TypeNode pt = d_nm->mkTupleType(types);
    Node pi = mkLambda(v,
                       datatypes::TupleUtils::constructTupleFromElements(
                           pt, sel, 0, sel.size() - 1));
    newComps.push_back(
        d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, pi, source)));
    for (size_t q = 0; q < cols.size(); q++)
    {
      moved[starts[c] + cols[q]] = newAt + q;
    }
    newAt += cols.size();
  }
  if (!changed)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node np = newComps.back();
  for (size_t k = newComps.size() - 1; k-- > 0;)
  {
    np = d_nm->mkNode(Kind::TABLE_PRODUCT, newComps[k], np);
  }
  TypeNode newRow = np.getType().getBagElementType();
  Node r = rowVariable(newRow);
  auto reread = [&](const Node& body, const Node& var) {
    std::vector<Node> from, to;
    for (const std::pair<const uint32_t, uint32_t>& m : moved)
    {
      from.push_back(datatypes::TupleUtils::nthElementOfTuple(var, m.first));
      to.push_back(datatypes::TupleUtils::nthElementOfTuple(r, m.second));
    }
    return body.substitute(from.begin(), from.end(), to.begin(), to.end());
  };
  if (expr::hasSubterm(g[1], r) || (!P.isNull() && expr::hasSubterm(P[1], r)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node gBody = reread(g[1], g[0][0]);
  if (occursFree(gBody, g[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> remaining;
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (owner[k] >= 0 && !keep[owner[k]])
    {
      continue;
    }
    Node c = reread(conjuncts[k], P[0][0]);
    if (occursFree(c, P[0][0]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    remaining.push_back(c);
  }
  Node below = np;
  if (!remaining.empty())
  {
    Node body = remaining.size() == 1 ? remaining[0]
                                      : d_nm->mkNode(Kind::AND, remaining);
    below = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r, body), np);
  }
  Node ret = d_nm->mkNode(
      Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, mkLambda(r, gBody), below));
  return BagsRewriteResponse(ret, Rewrite::SETOF_PUSHDOWN);
}

BagsRewriteResponse BagsRewriter::rewriteFilterIntoSetofComponent(
    const TNode& n) const
{
  // FILTER_INTO_SETOF: a conjunct c of the filter that reads only a component
  // that is a set moves into it, where the rule that lifts filters out of
  // products does not reach it (see rewrites.h). There c reads the rows v of
  // the component: column w + k of t is column k of v, for components before it
  // of w columns.
  Node P = asLambda(n[0]);
  Node A = n[1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || A.getKind() != Kind::TABLE_PRODUCT)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node t = P[0][0];
  if (bindsVariable(P[1], t))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> comps;
  Node rest = A;
  while (rest.getKind() == Kind::TABLE_PRODUCT)
  {
    comps.push_back(rest[0]);
    rest = rest[1];
  }
  comps.push_back(rest);
  std::vector<size_t> starts, widths;
  size_t total = 0;
  for (const Node& c : comps)
  {
    TypeNode ty = c.getType().getBagElementType();
    if (!ty.isTuple())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    starts.push_back(total);
    widths.push_back(ty.getTupleLength());
    total += ty.getTupleLength();
  }
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  for (size_t ci = 0; ci < conjuncts.size(); ci++)
  {
    std::set<uint32_t> pos;
    if (!readPositions(conjuncts[ci], t, pos) || pos.empty())
    {
      continue;
    }
    for (size_t k = 0; k < comps.size(); k++)
    {
      bool inside = true;
      for (uint32_t q : pos)
      {
        inside = inside && q >= starts[k] && q < starts[k] + widths[k];
      }
      if (!inside || comps[k].getKind() != Kind::BAG_SETOF)
      {
        continue;
      }
      // the conjunct over the component's own rows
      TypeNode cty = comps[k].getType().getBagElementType();
      Node v = rowVariable(cty);
      std::vector<Node> from, to;
      for (size_t i = 0; i < widths[k]; i++)
      {
        from.push_back(
            datatypes::TupleUtils::nthElementOfTuple(t, starts[k] + i));
        to.push_back(datatypes::TupleUtils::nthElementOfTuple(v, i));
      }
      Node local = conjuncts[ci].substitute(
          from.begin(), from.end(), to.begin(), to.end());
      if (occursFree(local, t) || expr::hasSubterm(conjuncts[ci], v))
      {
        continue;
      }
      Node filtered =
          d_nm->mkNode(Kind::BAG_FILTER, mkLambda(v, local), comps[k][0]);
      Node newComp = d_nm->mkNode(Kind::BAG_SETOF, filtered);
      std::vector<Node> nc = comps;
      nc[k] = newComp;
      Node np = nc.back();
      for (size_t j = nc.size() - 1; j-- > 0;)
      {
        np = d_nm->mkNode(Kind::TABLE_PRODUCT, nc[j], np);
      }
      std::vector<Node> restConj;
      for (size_t j = 0; j < conjuncts.size(); j++)
      {
        if (j != ci)
        {
          restConj.push_back(conjuncts[j]);
        }
      }
      Node ret = np;
      if (!restConj.empty())
      {
        Node body = restConj.size() == 1 ? restConj[0]
                                         : d_nm->mkNode(Kind::AND, restConj);
        ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), np);
      }
      return BagsRewriteResponse(ret, Rewrite::FILTER_INTO_SETOF);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateSemiJoin(const TNode& n) const
{
  // AGGREGATE_SEMI_JOIN, SEMI_JOIN under an aggregate: B is a set whose row the
  // equations of p fix, all its columns or a key, and f and K read of B only
  // columns that p equates to columns of the other components: read those
  // instead, and the product is a semi-join (see rewrites.h),
  //   ((_ table.aggr K) f i (bag.filter p (table.product A B)))
  //   --->
  //   ((_ table.aggr K') f' i (bag.filter pA' A))
  // with pA' the conjuncts pA that read no column of B, and the existence of a
  // row of B that passes pAB, the others (see rewriteSemiJoin); K' and f' read
  // the columns of A.
  Node f = n[0];
  Node i = n[1];
  if (n[2].getKind() != Kind::BAG_FILTER
      || n[2][1].getKind() != Kind::TABLE_PRODUCT || f.getKind() != Kind::LAMBDA
      || f[0].getNumChildren() != 2)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node p = asLambda(n[2][0]);
  Node prod = n[2][1];
  if (p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node pt = p[0][0];
  if (bindsVariable(f[1], x) || bindsVariable(p[1], pt))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> comps;
  Node rest = prod;
  while (rest.getKind() == Kind::TABLE_PRODUCT)
  {
    comps.push_back(rest[0]);
    rest = rest[1];
  }
  comps.push_back(rest);
  std::vector<size_t> starts, widths;
  size_t total = 0;
  for (const Node& c : comps)
  {
    TypeNode t = c.getType().getBagElementType();
    if (!t.isTuple())
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    starts.push_back(total);
    widths.push_back(t.getTupleLength());
    total += t.getTupleLength();
  }
  std::set<uint32_t> fRead;
  if (!readPositions(f[1], x, fRead))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<Node> conjuncts;
  if (p[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
  }
  else
  {
    conjuncts.push_back(p[1]);
  }
  std::vector<std::set<uint32_t>> reads(conjuncts.size());
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (!readPositions(conjuncts[k], pt, reads[k]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // the component to join away: of those that qualify, the one with the
  // smallest node, so that one join written in two orders is rewritten alike
  std::vector<size_t> order(comps.size());
  for (size_t k = 0; k < order.size(); k++)
  {
    order[k] = k;
  }
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return comps[a].getId() < comps[b].getId();
  });
  for (size_t j : order)
  {
    Node B = comps[j];
    std::vector<std::set<uint32_t>> keys = keysOf(B);
    if (B.getKind() != Kind::BAG_SETOF && keys.empty())
    {
      continue;
    }
    size_t bStart = starts[j], wb = widths[j];
    auto inB = [&](uint32_t pos) { return pos >= bStart && pos < bStart + wb; };
    std::vector<Node> onA, onAB;
    std::set<uint32_t> determined;
    // a column of B equal to a column of the others: B position -> that one
    std::map<uint32_t, uint32_t> aliases;
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      const Node& c = conjuncts[k];
      bool readsB = false;
      for (uint32_t pos : reads[k])
      {
        readsB = readsB || inB(pos);
      }
      (readsB ? onAB : onA).push_back(c);
      if (!readsB || c.getKind() != Kind::EQUAL)
      {
        continue;
      }
      for (size_t sd = 0; sd < 2; sd++)
      {
        Node col = c[sd];
        std::set<uint32_t> other;
        if (col.getKind() == Kind::APPLY_SELECTOR && col[0] == pt
            && readPositions(c[1 - sd], pt, other))
        {
          uint32_t pos = datatypes::utils::indexOf(col.getOperator());
          bool fromRest = inB(pos);
          for (uint32_t o : other)
          {
            fromRest = fromRest && !inB(o);
          }
          if (fromRest)
          {
            determined.insert(pos - bStart);
            Node e = c[1 - sd];
            if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == pt)
            {
              aliases[pos] = datatypes::utils::indexOf(e.getOperator());
            }
          }
        }
      }
    }
    bool fixesRow = determined.size() == wb;
    for (const std::set<uint32_t>& key : keys)
    {
      bool all = true;
      for (uint32_t c : key)
      {
        all = all && determined.count(c) > 0;
      }
      fixesRow = fixesRow || all;
    }
    if (onAB.empty() || !fixesRow)
    {
      continue;
    }
    // f and K read B only through aliased columns
    bool readable = true;
    for (uint32_t pos : fRead)
    {
      readable = readable && (!inB(pos) || aliases.count(pos));
    }
    for (uint32_t k : K)
    {
      readable = readable && (!inB(k) || aliases.count(k));
    }
    if (!readable)
    {
      continue;
    }
    // old position of a column of the others -> its position in A
    std::map<uint32_t, uint32_t> inA;
    size_t aPos = 0;
    std::vector<Node> others;
    for (size_t k = 0; k < comps.size(); k++)
    {
      if (k == j)
      {
        continue;
      }
      others.push_back(comps[k]);
      for (size_t c = 0; c < widths[k]; c++)
      {
        inA[starts[k] + c] = aPos++;
      }
    }
    auto toA = [&](uint32_t pos) { return inA[inB(pos) ? aliases[pos] : pos]; };
    Node A = others.back();
    for (size_t k = others.size() - 1; k-- > 0;)
    {
      A = d_nm->mkNode(Kind::TABLE_PRODUCT, others[k], A);
    }
    TypeNode aType = A.getType().getBagElementType();
    TypeNode bType = B.getType().getBagElementType();
    Node a = rowVariable(aType);
    Node b = aType == bType ? accumulatorVariable(bType) : rowVariable(bType);
    Node xa = rowVariable(aType);
    if (expr::hasSubterm(p[1], a) || expr::hasSubterm(p[1], b)
        || expr::hasSubterm(f[1], xa) || f[0][1] == xa)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    std::vector<Node> pFrom, pTo, fFrom, fTo;
    for (size_t k = 0; k < comps.size(); k++)
    {
      for (size_t c = 0; c < widths[k]; c++)
      {
        uint32_t pos = starts[k] + c;
        pFrom.push_back(datatypes::TupleUtils::nthElementOfTuple(pt, pos));
        pTo.push_back(
            k == j ? datatypes::TupleUtils::nthElementOfTuple(b, c)
                   : datatypes::TupleUtils::nthElementOfTuple(a, inA[pos]));
        if (k != j || aliases.count(pos))
        {
          fFrom.push_back(datatypes::TupleUtils::nthElementOfTuple(x, pos));
          fTo.push_back(datatypes::TupleUtils::nthElementOfTuple(xa, toA(pos)));
        }
      }
    }
    Node pA = onA.empty()
                  ? d_nm->mkConst(true)
                  : (onA.size() == 1 ? onA[0] : d_nm->mkNode(Kind::AND, onA));
    Node pAB = onAB.size() == 1 ? onAB[0] : d_nm->mkNode(Kind::AND, onAB);
    pA = pA.substitute(pFrom.begin(), pFrom.end(), pTo.begin(), pTo.end());
    pAB = pAB.substitute(pFrom.begin(), pFrom.end(), pTo.begin(), pTo.end());
    Node fBody =
        f[1].substitute(fFrom.begin(), fFrom.end(), fTo.begin(), fTo.end());
    if (occursFree(pA, pt) || occursFree(pAB, pt) || occursFree(fBody, x)
        || occursFree(pA, b))
    {
      continue;
    }
    std::vector<uint32_t> K2;
    for (uint32_t k : K)
    {
      K2.push_back(toA(k));
    }
    Node matches = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(b, pAB), B);
    Node empty = d_nm->mkConst(EmptyBag(B.getType()));
    Node exists = matches.eqNode(empty).notNode();
    Node filtered =
        d_nm->mkNode(Kind::BAG_FILTER, mkLambda(a, pA.andNode(exists)), A);
    Node f2 = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, xa, f[0][1]), fBody);
    Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(K2));
    std::vector<Node> children{op, f2, i, filtered};
    Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_SEMI_JOIN);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

Node BagsRewriter::semiJoinToIntersection(const Node& n, bool underSetof) const
{
  // SEMI_TO_INTERSECTION, for
  //   (bag.map g
  //            (bag.filter (lambda ((x ..))
  //                          (and (>= (bag.count (pi x) M) 1) q r))
  //                        X))
  // with pi a projection, as (pi x) =
  // (tuple ((_ tuple.select 0) x) ((_ tuple.select 1) x)); g a projection of
  // the columns of pi, h applied to the result of pi; q reading only the
  // columns of pi and r the others: the projected rows of the r-filtered X that
  // are in M and pass q. Under duplicate removal (underSetof), or when those
  // projected rows are a set, that is
  //   (bag.map h (bag.inter_min
  //                (bag.setof (bag.filter q' (bag.map pi (bag.filter r X))))
  //                (bag.setof (bag.filter q' M))))
  // with q' the conjuncts q over the rows of M, which reads the same whichever
  // side the join was written from: SQL's
  //   SELECT a, b FROM X WHERE (a, b) IN (SELECT .. FROM ..)
  // and the join of X with that subquery (see rewrites.h). Null when n is not
  // of that shape.
  Node g = asLambda(n[0]);
  Node P = asLambda(n[1][0]);
  Node X = n[1][1];
  if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
      || P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || d_rewriter == nullptr)
  {
    return Node::null();
  }
  std::vector<uint32_t> J = projectionIndices(g);
  if (J.empty())
  {
    return Node::null();
  }
  Node x = P[0][0];
  if (bindsVariable(P[1], x))
  {
    return Node::null();
  }
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  // the membership whose probe is a projection of x covering g's columns
  Node M;
  std::vector<uint32_t> Jp;
  size_t which = conjuncts.size();
  for (size_t k = 0; k < conjuncts.size() && M.isNull(); k++)
  {
    const Node& c = conjuncts[k];
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::BAG_COUNT || occursFree(c[0][1], x))
    {
      continue;
    }
    Node E = c[0][0];
    if (!isTupleTerm(E))
    {
      continue;
    }
    std::vector<uint32_t> cols;
    bool selectors = true;
    for (const Node& e : E)
    {
      if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == x)
      {
        cols.push_back(datatypes::utils::indexOf(e.getOperator()));
      }
      else
      {
        selectors = false;
      }
    }
    if (!selectors)
    {
      continue;
    }
    bool covers = true;
    for (uint32_t j : J)
    {
      covers = covers && std::find(cols.begin(), cols.end(), j) != cols.end();
    }
    if (covers)
    {
      M = c[0][1];
      Jp = cols;
      which = k;
    }
  }
  if (M.isNull())
  {
    return Node::null();
  }
  std::set<uint32_t> probed(Jp.begin(), Jp.end());
  std::vector<Node> qs, rs;
  for (size_t k = 0; k < conjuncts.size(); k++)
  {
    if (k == which)
    {
      continue;
    }
    std::set<uint32_t> pos;
    if (!readPositions(conjuncts[k], x, pos))
    {
      return Node::null();
    }
    bool onProbe = true;
    for (uint32_t q : pos)
    {
      onProbe = onProbe && probed.count(q) > 0;
    }
    (onProbe ? qs : rs).push_back(conjuncts[k]);
  }
  TypeNode rowType = X.getType().getBagElementType();
  TypeNode wType = M.getType().getBagElementType();
  Node xr = rowVariable(rowType);
  // pi over the rows of X
  std::vector<Node> piCols;
  for (uint32_t j : Jp)
  {
    piCols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, j));
  }
  Node pi = mkLambda(xr,
                     datatypes::TupleUtils::constructTupleFromElements(
                         wType, piCols, 0, piCols.size() - 1));
  Node source = X;
  if (!rs.empty())
  {
    Node r = rs.size() == 1 ? rs[0] : d_nm->mkNode(Kind::AND, rs);
    source = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(x, r), X);
  }
  Node projected = d_nm->mkNode(Kind::BAG_MAP, pi, source);
  if (!underSetof && !isSet(projected))
  {
    return Node::null();
  }
  Node w = rowVariable(wType);
  std::vector<Node> from, to;
  for (size_t k = 0; k < Jp.size(); k++)
  {
    Node col = datatypes::TupleUtils::nthElementOfTuple(x, Jp[k]);
    if (std::find(from.begin(), from.end(), col) == from.end())
    {
      from.push_back(col);
      to.push_back(datatypes::TupleUtils::nthElementOfTuple(w, k));
    }
  }
  Node left = projected;
  Node right = M;
  if (!qs.empty())
  {
    Node q = qs.size() == 1 ? qs[0] : d_nm->mkNode(Kind::AND, qs);
    Node qw = q.substitute(from.begin(), from.end(), to.begin(), to.end());
    if (occursFree(qw, x))
    {
      return Node::null();
    }
    Node lambda = mkLambda(w, qw);
    left = d_nm->mkNode(Kind::BAG_FILTER, lambda, left);
    right = d_nm->mkNode(Kind::BAG_FILTER, lambda, right);
  }
  Node inter = d_nm->mkNode(Kind::BAG_INTER_MIN,
                            {d_nm->mkNode(Kind::BAG_SETOF, left),
                             d_nm->mkNode(Kind::BAG_SETOF, right)});
  // h: g's columns read from the probe row
  std::vector<Node> hCols;
  for (uint32_t j : J)
  {
    size_t at = std::find(Jp.begin(), Jp.end(), j) - Jp.begin();
    hCols.push_back(datatypes::TupleUtils::nthElementOfTuple(w, at));
  }
  Node hBody = datatypes::TupleUtils::constructTupleFromElements(
      g[1].getType(), hCols, 0, hCols.size() - 1);
  if (J == Jp)
  {
    return inter;
  }
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(w, hBody), inter);
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

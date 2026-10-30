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
 */
struct BagsNotNullAttributeId
{
};
typedef expr::Attribute<BagsNotNullAttributeId, Node> BagsNotNullAttribute;

namespace {
/**
 * Whether n is the null of a nullable sort, e.g.
 * (as nullable.null (Nullable Int)), the constructor of no argument.
 */
bool isNullConstant(const Node& n)
{
  return n.getKind() == Kind::APPLY_CONSTRUCTOR && n.getNumChildren() == 0
         && n.getType().isNullable();
}

/**
 * The bound variable of type tn that the rewriter uses for role and key n,
 * one per (role, n, tn): the variable of id BAGS_FIRST_INDEX cached on
 * (SEXPR role n), role a string constant. The reductions of bags, the other
 * users of that id, cache on the bag terms they reduce, never on an SEXPR.
 */
Node mkRewriterVar(NodeManager* nm, const char* role, Node n, TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, tn);
}

/** The same, named name. */
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
      case Kind::TABLE_PROJECT: response = postRewriteProject(n); break;
      case Kind::TABLE_AGGREGATE: response = postRewriteAggregate(n); break;
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
  // a table constant whose rows have the sort of the probe
  bool rowProbe = false;
  if (n[1].getKind() == Kind::VARIABLE)
  {
    TypeNode rowType = n[1].getType().getBagElementType();
    TypeNode probeType = n[0].getType();
    rowProbe = rowType.isTuple() && rowType == probeType;
  }
  if ((n[1].getKind() == Kind::BAG_MAP || rowProbe)
      && n[0].getKind() == Kind::APPLY_CONSTRUCTOR && n[0].getNumChildren() > 1)
  {
    // COUNT_MAP_CONST_PROBE: column k of the probe is a constant c and the
    // map copies column j of its row there, so only the rows of X whose
    // column j is c can give the probe; column k leaves the probe and the map:
    //   (bag.count (tuple 5 b)
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)
    //                                              ((_ tuple.select 0) t)))
    //                       X))
    //   --->
    //   (bag.count (tuple b)
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
    //                       (bag.filter (lambda ((t T))
    //                                     (= ((_ tuple.select 1) t) 5))
    //                                   X)))
    // A table constant X that the input declares (Kind::VARIABLE) counts as
    // its own identity map
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
    //                                   ((_ tuple.select 1) t)))
    //            X)
    // but a skolem the solver introduced by purification does not: rewriting
    // the counts of those makes the solver introduce more of them.
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
        // g2 is (lambda ((t T)) (tuple ((_ tuple.select 0) t))), e2 is
        // (tuple b)
        Node g2 = mkLambda(sv,
                           datatypes::TupleUtils::constructTupleFromElements(
                               t, cols, 0, cols.size() - 1));
        Node e2 = datatypes::TupleUtils::constructTupleFromElements(
            t, probe, 0, probe.size() - 1);
        // (bag.filter (lambda ((t T)) (= ((_ tuple.select 1) t) 5)) X)
        Node fixed =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(sv, col.eqNode(c)), n1[1]);
        Node ret = d_nm->mkNode(
            Kind::BAG_COUNT, e2, d_nm->mkNode(Kind::BAG_MAP, g2, fixed));
        return BagsRewriteResponse(ret, Rewrite::COUNT_MAP_CONST_PROBE);
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

BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // the bag.setof of a key assertion, see BagsKeyTermAttribute
    return BagsRewriteResponse(n, Rewrite::NONE);
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
    // (bag.setof (bag x n)) = (bag x (ite (>= n 1) 1 0))
    Node count = d_nm->mkNode(
        Kind::ITE, d_nm->mkNode(Kind::GEQ, n[0][1], d_one), d_one, d_zero);
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], count);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
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

void BagsRewriter::recordFacts(TNode assertion) const
{
  // the conjuncts of a top-level assertion are top-level assertions too
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
      recordKey(a);
      recordNotNull(a);
    }
  }
}

void BagsRewriter::recordKey(const TNode& n) const
{
  // n is (= (bag.setof M) M), either way round, with M a projection of a table
  // constant X onto columns K, as the input states it,
  // ((_ table.project 0 2) X), or as the rewriter leaves it, a map by
  // (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 0 2) t)): no two rows
  // of X agree on K, a key of X
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() != Kind::BAG_SETOF || n[i][0] != n[1 - i])
    {
      continue;
    }
    Node M = n[1 - i];
    std::vector<uint32_t> K;
    Node T;
    if (M.getKind() == Kind::TABLE_PROJECT && M[0].isVar())
    {
      K = M.getOperator().getConst<ProjectOp>().getIndices();
      T = M[0];
    }
    else if (M.getKind() == Kind::BAG_MAP && M[1].isVar())
    {
      K = projectionIndices(asLambda(M[0]));
      T = M[1];
    }
    if (K.empty())
    {
      continue;
    }
    std::sort(K.begin(), K.end());
    K.erase(std::unique(K.begin(), K.end()), K.end());
    std::vector<Node> cols;
    for (uint32_t k : K)
    {
      cols.push_back(d_nm->mkConstInt(Rational(k)));
    }
    // (SEXPR 0 2), added to the keys (SEXPR (SEXPR 1) ..) X has already
    Node key = d_nm->mkNode(Kind::SEXPR, cols);
    // the bag.setof of the assertion, and the one that rewriting its argument
    // builds (over the map that PROJECT_TO_MAP makes of the projection), are
    // not rewritten
    Node keyTerm = n[i];
    keyTerm.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal = d_nm->mkNode(Kind::BAG_SETOF, d_rewriter->rewrite(M));
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
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

void BagsRewriter::recordNotNull(const TNode& n) const
{
  // n is the assertion that column k of the table constant X has no null,
  // (= (bag.filter (lambda ((t (Tuple Int (Nullable Int)))) (= ((_ tuple.select
  // k) t) (as nullable.null (Nullable Int)))) X) (as bag.empty ..)), either way
  // round, see recordNotNull in the header
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
    if (!T.isVar() || p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1
        || p[1].getKind() != Kind::EQUAL)
    {
      continue;
    }
    Node v = p[0][0];
    Node col;
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
    // the filter of the assertion, and the one the rewriting of its predicate
    // will build, are not rewritten
    F.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal =
          d_nm->mkNode(Kind::BAG_FILTER, d_rewriter->rewrite(F[0]), T);
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
    // the column k, added to the never-null columns (SEXPR ..) of X
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
      d_nonNull.clear();
    }
  }
}

bool BagsRewriter::nonNullTerm(const Node& t,
                               const Node& x,
                               const std::set<uint32_t>& nx,
                               const Node& acc,
                               const std::set<uint32_t>& nacc) const
{
  // whether t is never null, with the columns nx of x and nacc of acc never
  // null; a term of a sort that is not nullable is never null
  if (!t.getType().isNullable())
  {
    return true;
  }
  if (t.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // (nullable.some a), but not (as nullable.null (Nullable Int))
    return t.getNumChildren() == 1;
  }
  if (t.getKind() == Kind::APPLY_SELECTOR && t[0].getType().isTuple())
  {
    uint32_t k = datatypes::utils::indexOf(t.getOperator());
    return (!x.isNull() && t[0] == x && nx.count(k) > 0)
           || (!acc.isNull() && t[0] == acc && nacc.count(k) > 0);
  }
  if (t.getKind() == Kind::BAG_FOLD)
  {
    // a fold from a value that is not null, whose step is not null or keeps the
    // accumulator, as
    //   (bag.fold (lambda ((t (Tuple Int Int)) (acc (Nullable Int)))
    //               (ite p (nullable.some ((_ tuple.select 0) t)) acc))
    //             (nullable.some 0)
    //             X)
    Node l = asLambda(t[0]);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2
        && t[1].getKind() == Kind::APPLY_CONSTRUCTOR
        && t[1].getNumChildren() == 1)
    {
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
    return false;
  }
  if (t.getKind() == Kind::ITE)
  {
    // (ite (= (as nullable.null (Nullable Int)) a) b c) with a never null
    // is c; any other ite is never null when both branches are not
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
  return false;
}

std::set<uint32_t> BagsRewriter::aggregateNonNull(const Node& B,
                                                  bool reached) const
{
  // the columns of ((_ table.aggr K) f i X) that are never null: those whose
  // initial value is not and whose step keeps them so; in a group a row
  // reached, also those the step makes not null from these. With
  //   f = (lambda ((t (Tuple Int Int))
  //                (acc (Tuple (Nullable Int) (Nullable Int))))
  //         (tuple ((_ tuple.select 0) acc) (nullable.some 1)))
  //   i = (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
  // column 0 is never null (its initial value is not, and its step keeps it),
  // and column 1 is not null in the groups a row reached (reached is true),
  // since the first step makes it (nullable.some 1)
  std::set<uint32_t> out;
  Node f = asLambda(B[0]);
  Node init = B[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || init.getKind() != Kind::APPLY_CONSTRUCTOR
      || init.getNumChildren() != f[1].getNumChildren())
  {
    return out;
  }
  std::set<uint32_t> nx = nonNullColumns(B[2]);
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  // the invariant: the columns non-null in the seed, then the greatest
  // subset of them that every step keeps non-null
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

std::set<uint32_t> BagsRewriter::nonNullColumns(const Node& B) const
{
  // the columns of B's rows that are never null, read off its structure: the
  // NOT NULL columns of a table constant (BagsNotNullAttribute), and what the
  // operators above keep or establish. For instance, with column 0 of
  // X : (Bag (Tuple (Nullable Int) (Nullable Int))) never null, both columns of
  //   (bag.filter
  //     (lambda ((t (Tuple (Nullable Int) (Nullable Int))))
  //       (nullable.is_some ((_ tuple.select 1) t)))
  //     X)
  // are never null
  auto it = d_nonNull.find(B);
  if (it != d_nonNull.end())
  {
    return it->second;
  }
  std::set<uint32_t> out;
  TypeNode et = B.getType().getBagElementType();
  if (et.isTuple())
  {
    switch (B.getKind())
    {
      case Kind::BAG_FILTER:
      {
        out = nonNullColumns(B[1]);
        Node p = asLambda(B[0]);
        if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1)
        {
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
            // (nullable.is_some ((_ tuple.select k) x)), or
            // (= ((_ tuple.select k) x) a) with a never null
            Node a;
            int ci = datatypes::utils::isTester(c, a);
            if (ci >= 0 && a.getKind() == Kind::APPLY_SELECTOR && a[0] == x
                && a.getType().isNullable()
                && a.getType().getDType()[ci].getNumArgs() == 1)
            {
              out.insert(datatypes::utils::indexOf(a.getOperator()));
            }
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
          // a filter that tests an aggregate's counter column positive keeps
          // only the groups a row reached, see counterColumn
          std::set<uint32_t> more = aggregateNonNull(B[1], true);
          out.insert(more.begin(), more.end());
        }
        if (B[1].getKind() == Kind::TABLE_PRODUCT && p.getKind() == Kind::LAMBDA
            && p[0].getNumChildren() == 1)
        {
          // a component aggregate whose groups the filter keeps reached ones
          // of: its counter tested positive, or joined to such a one, see
          // reachedComponents; the components of
          // (table.product X (table.product Y Z)) are X, Y and Z, starting at
          // the columns starts2
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
      case Kind::BAG_SETOF:
      case Kind::BAG_DIFFERENCE_SUBTRACT:
      case Kind::BAG_DIFFERENCE_REMOVE: out = nonNullColumns(B[0]); break;
      case Kind::BAG_INTER_MIN:
      {
        out = nonNullColumns(B[0]);
        std::set<uint32_t> more = nonNullColumns(B[1]);
        out.insert(more.begin(), more.end());
        break;
      }
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      {
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
        // column j of a map by (lambda ((t ..)) (tuple a0 .. am)) is never null
        // when aj is not, given the never-null columns of its argument
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
      case Kind::TABLE_AGGREGATE: out = aggregateNonNull(B, false); break;
      default:
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

Node BagsRewriter::assumeNonNull(const Node& body,
                                 const Node& x,
                                 const std::set<uint32_t>& cols) const
{
  // body with the null tests of the columns cols of x decided: they are
  // never null. With cols = {1},
  //   (and (nullable.is_some ((_ tuple.select 1) x))
  //        (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
  //        p)
  //   is
  //   (and true false p)
  // which the rewriter then simplifies
  if (cols.empty())
  {
    return body;
  }
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

std::vector<std::set<uint32_t>> BagsRewriter::keysOf(const Node& B) const
{
  // the keys of B: those of a table constant, of a filter over one; for X
  // with the attribute (SEXPR (SEXPR 0 2) (SEXPR 1)), {{0, 2}, {1}}
  std::vector<std::set<uint32_t>> keys;
  Node T = B;
  while (T.getKind() == Kind::BAG_FILTER)
  {
    T = T[1];
  }
  if (!T.isVar() || !T.hasAttribute(BagsKeysAttribute()))
  {
    return keys;
  }
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

std::vector<std::set<uint32_t>> BagsRewriter::rowKeys(const Node& B) const
{
  // the keys of B read off its structure: a table's declared keys, kept by
  // filters, intersections and differences, by maps that keep their columns,
  // and combined by products; all the columns of a bag.setof; the group columns
  // that an aggregate's rows keep. Every key found makes B a set. With X and Y
  // of two columns, each with the key {0}:
  //   (table.product X Y) has the key {0, 2}, Y's column 0 being column 2
  //     of the product;
  //   (bag.map (lambda ((t (Tuple Int Int)))
  //              (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
  //            X) has the key {1};
  //   ((_ table.aggr 0) f i X) has the key {k} when column k of f's result
  //     is ((_ tuple.select 0) t), the group column.
  std::vector<std::set<uint32_t>> keys;
  TypeNode et = B.getType().getBagElementType();
  if (!et.isTuple())
  {
    return keys;
  }
  size_t width = et.getTupleLength();
  switch (B.getKind())
  {
    case Kind::BAG_FILTER:
    {
      // a column that the filter fixes to a constant decides nothing, and one
      // it sets equal to another is that one. For X : (Bag (Tuple Int Int Int))
      // with the key {0, 1},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 1) t) 5))
      //               X)
      // has the key {0}; and with the key {1, 2},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
      //               X)
      // has the key {0, 1}, column 2 being column 0
      keys = rowKeys(B[1]);
      std::map<uint32_t, Node> fixed = fixedColumns(B[0]);
      Node P = asLambda(B[0]);
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
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE: return rowKeys(B[0]);
    case Kind::BAG_INTER_MIN:
    {
      keys = rowKeys(B[0]);
      std::vector<std::set<uint32_t>> more = rowKeys(B[1]);
      keys.insert(keys.end(), more.begin(), more.end());
      return keys;
    }
    case Kind::BAG_SETOF:
    {
      keys = rowKeys(B[0]);
      // all the columns of the rows of a bag.setof of a map, counting a
      // constant column, or one that repeats another, only once
      std::set<uint32_t> all;
      Node g =
          B[0].getKind() == Kind::BAG_MAP ? asLambda(B[0][0]) : Node::null();
      std::set<Node> seen;
      for (size_t k = 0; k < width; k++)
      {
        if (!g.isNull() && g.getKind() == Kind::LAMBDA
            && g[1].getKind() == Kind::APPLY_CONSTRUCTOR
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
      Node g = asLambda(B[0]);
      if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
          || g[1].getKind() != Kind::APPLY_CONSTRUCTOR
          || g[1].getNumChildren() != width)
      {
        return keys;
      }
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
      Node f = asLambda(B[0]);
      if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
          || f[1].getKind() != Kind::APPLY_CONSTRUCTOR)
      {
        return keys;
      }
      Node x = f[0][0];
      std::set<uint32_t> out;
      for (uint32_t c : B.getOperator().getConst<ProjectOp>().getIndices())
      {
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
  if (B.isVar())
  {
    return keysOf(B);
  }
  return keys;
}

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

BagsRewriteResponse BagsRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAP);
  TypeNode mapType = n.getType();
  TypeNode argType = n[1].getType();
  if (mapType == argType && argType.getBagElementType().isTuple())
  {
    // MAP_IDENTITY: a map that copies every column in order is its argument
    // (see rewrites.h)
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
    // NOT_NULL_COLUMNS: the null tests of the columns that the rows of X never
    // have null in are decided, see assumeNonNull and rewrites.h
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
      // MAP_MAP, see rewriteMapOfMap
      BagsRewriteResponse r = rewriteMapOfMap(n);
      if (r.d_node != n)
      {
        return r;
      }
      break;
    }
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
  // the rules for maps of aggregates and of products of aggregates, each
  // documented at its function
  {
    // AGGREGATE_DEAD_COLUMNS, see rewriteAggregateDeadColumns
    BagsRewriteResponse r = rewriteAggregateDeadColumns(n);
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
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // MAP_EQUAL_COLUMNS: a row that passes the filter has the columns it
    // equates equal, and the map reads the first of them (see rewrites.h); rep
    // is a union-find over the columns, each pointing to the smallest it equals
    Node h = asLambda(n[0]);
    Node P = asLambda(n[1][0]);
    if (h.getKind() == Kind::LAMBDA && h[0].getNumChildren() == 1
        && P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1
        && n[1][1].getType().getBagElementType().isTuple())
    {
      Node r = P[0][0];
      size_t w = n[1][1].getType().getBagElementType().getTupleLength();
      std::vector<uint32_t> rep(w);
      for (uint32_t col = 0; col < w; col++)
      {
        rep[col] = col;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t col) {
        return rep[col] == col ? col : (rep[col] = find(rep[col]));
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
  if (n[1].getKind() == Kind::BAG_FILTER && n[0].getKind() == Kind::LAMBDA
      && n[0][0].getNumChildren() == 1)
  {
    // MAP_FIXED_COLUMNS: a row that passes the filter has the constants it
    // fixes its columns to, and the map reads those instead, see readFixed and
    // rewrites.h
    std::map<uint32_t, Node> fixed = fixedColumns(n[1][0]);
    if (n[1][1].getKind() == Kind::TABLE_AGGREGATE)
    {
      // and, when the filter keeps only groups some row reached, the
      // constants every group computes, see reachedGroupConstants
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
    // CANONICAL_VARIABLE: the lambda over its canonical variable, see
    // canonicalLambda and rewrites.h
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, canonical, n[1]);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  Node P = n[0];
  Node A = n[1];
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // the filter of a not-null assertion, see BagsKeyTermAttribute
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode t = A.getType();
  {
    // NOT_NULL_COLUMNS: the null tests of the columns that the rows of A never
    // have null in are decided, see assumeNonNull and rewrites.h
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
      // FILTER_TRUE and FILTER_FALSE, for a constant predicate
      // (see rewrites.h); the rewriter keeps a lambda with a constant body as a
      // function array constant, see asLambda
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
    // FILTER_NULLABLE_TRUTH: the two ways to say that a three-valued
    // predicate holds become one, see normalizeTruth
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
      // FILTER_TRUE and FILTER_FALSE, as above, for a lambda node
      if (body.getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
    {
      std::vector<Node> cs;
      if (body.getKind() == Kind::AND)
      {
        cs.insert(cs.end(), body.begin(), body.end());
      }
      else
      {
        cs.push_back(body);
      }
      std::vector<Node> flat = cs;
      // FILTER_CONFLICTING_CONSTANTS: a conjunction that fixes one term to two
      // distinct constants holds of no row (see rewrites.h); fixed maps each
      // term a conjunct fixes to its constant
      std::map<Node, Node> fixed;
      for (const Node& c : flat)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        bool leftConst = c[0].isConst();
        bool rightConst = c[1].isConst();
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
      // a value e that a membership (>= (bag.count (tuple a e) X) 1) puts in
      // a column of X that is never null is not null either
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
      // FILTER_CONFLICTING_CONSTANTS also drops the conjuncts that others
      // imply:
      //   (nullable.is_some a) next to (= a (nullable.some 5));
      //   (nullable.is_some e), or (not (= (as nullable.null (Nullable Int))
      //   e)), next to a membership that puts e in a never-null column;
      //   (>= (* a b) 1) of integers next to (>= a 1) and (>= b 1), the test
      //   that a product of two groups' counters is positive
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
        Node a;
        int ci = datatypes::utils::isTester(c, a);
        auto it = ci >= 0 ? fixed.find(a) : fixed.end();
        if (it != fixed.end() && it->second.getKind() == Kind::APPLY_CONSTRUCTOR
            && datatypes::utils::indexOf(it->second.getOperator())
                   == static_cast<size_t>(ci))
        {
          continue;
        }
        if (ci >= 0 && nonNull.count(a) && a.getType().isNullable()
            && a.getType().getDType()[ci].getNumArgs() == 1)
        {
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
      // FILTER_FALSE: no row passes a conjunct and its negation
      // (see rewrites.h)
      std::unordered_set<Node> present(body.begin(), body.end());
      for (const Node& c : body)
      {
        if (c.getKind() == Kind::NOT && present.count(c[0]))
        {
          return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                     Rewrite::FILTER_FALSE);
        }
      }
      // FILTER_SORT_CONJUNCTS: the conjuncts in one order, without
      // duplicates, so that two filters by the same conjunction, merged in
      // different orders, are one lambda,
      //   (bag.filter (lambda ((t T)) (and q p q)) X)
      //   ---> (bag.filter (lambda ((t T)) (and p q)) X)
      // when the alpha key of p is smaller than that of q. The order is by
      // alphaKey, which does not depend on the name of the row variable: the
      // name is chosen after the order (canonicalLambda), so an order by
      // node id would change with it
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
    // CANONICAL_VARIABLE, see canonicalLambda
    Node canonical = canonicalLambda(P);
    if (canonical != P)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, canonical, A);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
    if (body.getKind() == Kind::OR)
    {
      // FILTER_SPLIT_CLOSED: a disjunct c that does not read the row, such as
      // EXISTS (subquery), splits the filter in two:
      //   (bag.filter (lambda ((t T)) (or c q)) A)
      //   --->
      //   (bag.union_disjoint (bag.filter (lambda ((t T)) c) A)
      //                       (bag.filter (lambda ((t T)) (and (not c) q)) A))
      // each row passes one of the two exactly when it passes the
      // disjunction, and never both
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
      // FILTER_BAG_MAKE, a bag of x again rather than an ite over bags, so
      // that a product or a map over it keeps its shape:
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
    // FILTER_MAP, see rewriteFilterOfMap
    case Kind::BAG_MAP: return rewriteFilterOfMap(n);
    case Kind::TABLE_AGGREGATE:
    {
      if (rejectsInitialRow(n[0], A[1]))
      {
        // AGGREGATE_KEYED, under a filter that drops the row of initial values
        // (see rejectsInitialRow): the rows of the groups, see
        // keyedAggregateRows and rewrites.h
        Node rows = keyedAggregateRows(A);
        if (!rows.isNull())
        {
          Node ret = d_nm->mkNode(Kind::BAG_FILTER, n[0], rows);
          return BagsRewriteResponse(ret, Rewrite::AGGREGATE_KEYED);
        }
      }
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    case Kind::BAG_SETOF:
    {
      // FILTER_SETOF:
      //   (bag.filter p (bag.setof A)) ---> (bag.setof (bag.filter p A))
      Node inner = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_SETOF, inner);
      return BagsRewriteResponse(ret, Rewrite::FILTER_SETOF);
    }
    case Kind::TABLE_PRODUCT:
    {
      {
        // AGGREGATE_KEYED, for the components of the product whose groups the
        // filter keeps only reached ones of (see reachedComponents): the row of
        // initial values of such a component, which it has when its input is
        // empty, is in no row that passes, so the component is the rows of its
        // groups (see keyedAggregateRows)
        std::vector<Node> comps;
        std::vector<size_t> starts;
        Node rest = A;
        size_t at = 0;
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
          std::vector<int> test;
          std::vector<int> reached =
              reachedComponents(n[0], comps, starts, test);
          bool changed = false;
          for (size_t c = 0; c < comps.size(); c++)
          {
            if (reached[c] && comps[c].getKind() == Kind::TABLE_AGGREGATE)
            {
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
        // FILTER_JOIN_TRANSITIVE, see rewriteJoinTransitiveConditions
        BagsRewriteResponse r = rewriteJoinTransitiveConditions(n);
        if (r.d_node != n)
        {
          return r;
        }
      }
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
}

BagsRewriteResponse BagsRewriter::rewriteJoinTransitiveConditions(
    const TNode& n) const
{
  // FILTER_JOIN_TRANSITIVE: (bag.filter P (table.product C0 C1 ..)) where P
  // equates columns of different components: a condition on one column of
  // an equated class that the rows of its component satisfy (read off the
  // component and P's conjuncts on it alone, see elementConditions) holds of
  // the class's first column too, and joins P when it is not there, so that
  // a condition written on either side of a join is on both. With X and Y
  // of two columns,
  //   (bag.filter (lambda ((t V)) (= ((_ tuple.select 0) t)
  //                                  ((_ tuple.select 2) t)))
  //               (table.product X
  //                              (bag.filter (lambda ((s U))
  //                                            (> ((_ tuple.select 0) s) 3))
  //                                          Y)))
  //   --->
  //   (bag.filter (lambda ((t V)) (and (= ((_ tuple.select 0) t)
  //                                       ((_ tuple.select 2) t))
  //                                    (> ((_ tuple.select 0) t) 3)))
  //               (table.product X
  //                              (bag.filter (lambda ((s U))
  //                                            (> ((_ tuple.select 0) s) 3))
  //                                          Y)))
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
    // the component under those conjuncts,
    // (bag.filter (lambda ((v U)) (> ((_ tuple.select 0) v) 3)) Y), whose
    // element conditions are read off
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

std::vector<int> BagsRewriter::reachedComponents(
    const Node& P,
    const std::vector<Node>& comps,
    const std::vector<size_t>& starts,
    std::vector<int>& test) const
{
  // for a filter P over the product of comps: per component, the conjunct of P
  // that tests its count of rows positive (-1 when none), in test; and whether
  // its groups are reached: 1 when tested, 2 when joined on all its keys with a
  // reached aggregate whose input has the same key values, 0 otherwise. For
  // X : (Bag (Tuple Int Int)), G1 = ((_ table.aggr 0) f i X) and G2 =
  // ((_ table.aggr 0) g j X), each with rows of three columns, copying its
  // group column 0 and counting rows in column 2,
  //   P = (lambda ((t (Tuple Int Int Int Int Int Int)))
  //         (and (>= ((_ tuple.select 2) t) 1)
  //              (= ((_ tuple.select 0) t) ((_ tuple.select 3) t))))
  // over (table.product G1 G2) gives test = {0, -1} and reached = {1, 2}: G1's
  // count is tested, and every group of G2 that a reached group of G1 meets has
  // a row of X, the same key values as that group
  std::vector<int> reached(comps.size(), 0);
  test.assign(comps.size(), -1);
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || d_rewriter == nullptr)
  {
    return reached;
  }
  Node r = lambda[0][0];
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
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
        || f[1].getKind() != Kind::APPLY_CONSTRUCTOR)
    {
      continue;
    }
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
    // keyAt[c] maps each group column k to the column of the aggregate's
    // rows that copies it, ((_ tuple.select k) t) in f's result; keyed when
    // every group column is copied
    keyed[c] =
        !K.empty()
        && keyAt[c].size() == std::set<uint32_t>(K.begin(), K.end()).size();
    if (!keyed[c])
    {
      continue;
    }
    // a conjunct (>= ((_ tuple.select pos) t) 1) of P tests the count of rows
    // when the same test of column pos - start of the component's own rows does
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
        test[c] = static_cast<int>(k);
        reached[c] = 1;
      }
    }
  }
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
  // the key values of a component's input as a set, rewritten: for the group
  // column 0 of X : (Bag (Tuple Int Int)),
  //   (bag.setof
  //     (bag.map (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 0) s)))
  //              X))
  // two components whose sets are one term have the same key values
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
  // reached through a join with a reached group, to a fixpoint
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

void BagsRewriter::elementConditions(const Node& A,
                                     const Node& w,
                                     std::set<Node>& out) const
{
  // conditions every element w of A satisfies, read off A's filters, through
  // projections onto distinct columns, and through the key columns of the
  // groups an aggregate's rows reached. For
  //   A = (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
  //                (bag.filter (lambda ((s T))
  //                              (and (> ((_ tuple.select 1) s) 3)
  //                                   (< ((_ tuple.select 0) s) 7)))
  //                            X))
  // out gets (> ((_ tuple.select 0) w) 3): the map keeps column 1 of the
  // rows, as column 0 of w, and drops column 0, of which nothing is said
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
            && f[1].getKind() == Kind::APPLY_CONSTRUCTOR)
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
    Node l = asLambda(f);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2)
    {
      if (bag.getType().getBagElementType().isTuple())
      {
        // NOT_NULL_COLUMNS: the null tests of columns the rows of X never
        // have null are decided, see assumeNonNull
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
        // FOLD_MAP: the fold visits (g y) once per occurrence of y in Y,
        //   (bag.fold (lambda ((t U) (acc S)) b) i
        //             (bag.map (lambda ((s T)) e) Y))
        //   --->
        //   (bag.fold (lambda ((s T) (acc S)) b[t := e]) i Y)
        // when e does not read acc
        Node y = g[0][0];
        Node body = l[1].substitute(TNode(l[0][0]), TNode(g[1]));
        if (!occursFree(g[1], l[0][1]))
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
    // FOLD_TUPLE, see rewriteFoldOfTuple
    BagsRewriteResponse r = rewriteFoldOfTuple(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // FOLD_CONSTANT_STEP: a step c that reads neither the row nor the
    // accumulator gives c after any row, and the initial value for no row
    // (see rewrites.h)
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
    // CANONICAL_VARIABLE, see canonicalLambda
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

BagsRewriteResponse BagsRewriter::rewriteAggregateUnionDisjointKeys(
    const TNode& top) const
{
  // AGGREGATE_UNION_DISJOINT_KEYS: an aggregate over a union of parts no two
  // of which share a key value, with Q keeping only groups some row reached
  // (see counterColumn): every reached group is one part's, so the groups
  // are the union of the parts' groups,
  //   (bag.map h (bag.filter Q ((_ table.aggr 0) f i
  //                               (bag.union_disjoint U1 U2))))
  //   --->
  //   (bag.map h (bag.filter Q (bag.union_disjoint ((_ table.aggr 0) f i U1)
  //                                                ((_ table.aggr 0) f i U2))))
  // e.g. for
  //   U1 = (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s) 1)) X)
  //   U2 = (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s) 2)) Y)
  // Two parts are disjoint when a key column one part's rows have equal to a
  // constant makes a condition of the other's rows false (as 1 does to
  // (= ((_ tuple.select 0) w) 2)), or when one part's key columns are
  // constants or ites of constants and each of their combinations makes
  // such a condition false, or is null in a column the other part never has
  // null in
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
    if (U.getKind() == Kind::BAG_MAKE
        && U[0].getKind() == Kind::APPLY_CONSTRUCTOR)
    {
      for (uint32_t k : K)
      {
        cols.push_back(U[0][k]);
      }
    }
    else if (U.getKind() == Kind::BAG_MAP)
    {
      Node g = asLambda(U[0]);
      if (g.getKind() != Kind::LAMBDA
          || g[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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

BagsRewriteResponse BagsRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);

  {
    // NOT_NULL_COLUMNS: the null tests of the columns that the rows of X never
    // have null in are decided, see assumeNonNull and rewrites.h
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
  if (n.getOperator().getConst<ProjectOp>().getIndices().empty())
  {
    // AGGREGATE_NO_KEYS: grouping by no column makes one part, all of X, even
    // when X is empty (table.group of an empty table is one empty part):
    //   ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, n[0], n[1], n[2]);
    Node ret = d_nm->mkNode(Kind::BAG_MAKE, fold, d_one);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_NO_KEYS);
  }
  {
    // AGGREGATE_SORT_OUTPUT, see rewriteAggregateSortOutput
    BagsRewriteResponse r = rewriteAggregateSortOutput(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE, see canonicalLambda
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
    // AGGREGATE_MAP, see rewriteAggregateOfMap
    BagsRewriteResponse r = rewriteAggregateOfMap(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
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

BagsRewriteResponse BagsRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyBag(tableType));
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // PRODUCT_EMPTY: a product with the empty table is empty
    return BagsRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  // the normal form keeps the maps and filters above the products, see
  // rewriteProductOfMap and rewriteProductOfFilter, so that a query becomes
  // (bag.map h (bag.filter P (table.product X1 (table.product X2 ..)))), the
  // shape of SELECT h FROM X1, X2, .. WHERE P
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
  // filter of the product, over the factor's columns of its rows. With A and
  // B of two columns,
  //   (table.product (bag.filter (lambda ((s T)) (> ((_ tuple.select 1) s) 3))
  //                              A)
  //                  B)
  //   --->
  //   (bag.filter (lambda ((t V)) (> ((_ tuple.select 1) t) 3))
  //               (table.product A B))
  //   (table.product A (bag.filter (lambda ((s U)) (> ((_ tuple.select 1) s)
  //                                                  3))
  //                                B))
  //   --->
  //   (bag.filter (lambda ((t V)) (> ((_ tuple.select 3) t) 3))
  //               (table.product A B))
  // p is applied to the factor's part of t, (tuple ((_ tuple.select 2) t)
  // ((_ tuple.select 3) t)) for B, and beta-reduced (see applyFunction)
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
  // with B < A,
  //   (table.product A (table.product B C))
  //   ---> (bag.map perm (table.product B (table.product A C)))
  //   (table.product A B) ---> (bag.map perm (table.product B A))
  // where perm puts the columns back in the order A, B, C; with A, B and C of
  // one column,
  //   perm = (lambda ((t V)) (tuple ((_ tuple.select 1) t)
  //                                 ((_ tuple.select 0) t)
  //                                 ((_ tuple.select 2) t)))
  // so that two joins that list their tables in different orders become one
  // product
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

Node BagsRewriter::rowVariable(TypeNode tupleType) const
{
  // one bound variable per row type, so that two lambdas built here for the
  // same operation are one node, and purification gives them one symbol; the
  // variable of (Tuple Int Int) is named row_N, N the id of the key
  // (as bag.empty (Bag (Tuple Int Int)))
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(tupleType)));
  return mkRewriterVar(
      d_nm, "row", key, "row_" + std::to_string(key.getId()), tupleType);
}

bool BagsRewriter::bindsVariable(const Node& body, const Node& var) const
{
  // whether a closure in body binds var: true for var t and the body
  //   (>= (bag.count ((_ tuple.project 0) t)
  //                  (bag.map (lambda ((t (Tuple Int Int)))
  //                             ((_ tuple.project 1) t))
  //                           X))
  //       1)
  // whose inner lambda binds t again
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

bool BagsRewriter::occursFree(const Node& n, const Node& v) const
{
  // whether v occurs free in n: false for t in a lambda that binds t, true in
  // ((_ tuple.select 0) t)
  if (!expr::hasSubterm(n, v))
  {
    return false;
  }
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(n, fvs);
  return fvs.find(v) != fvs.end();
}

Node BagsRewriter::asLambda(const Node& f) const
{
  // a lambda whose body is a constant, or an ite over constants, is kept by the
  // rewriter as a function array constant: read it as the lambda it is, e.g.
  // (lambda ((t (Tuple Int Int))) true) for the constant of the filter that
  // keeps every row
  if (f.getKind() == Kind::FUNCTION_ARRAY_CONST)
  {
    Node lambda = uf::FunctionConst::toLambda(f);
    if (!lambda.isNull())
    {
      return lambda;
    }
  }
  return f;
}

Node BagsRewriter::applyFunction(const Node& fn, const Node& x) const
{
  // (f x) beta-reduced: for f =
  // (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3)) and x =
  // (tuple a b), (> ((_ tuple.select 1) (tuple a b)) 3), which the rewriter
  // simplifies to (> b 3); null when the substitution would capture a variable;
  // (f x) as an APPLY_UF when f is not a lambda
  Node f = asLambda(fn);
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    TNode var = f[0][0];
    if (var == x)
    {
      return f[1];
    }
    if (bindsVariable(f[1], var) || bindsVariable(x, var))
    {
      // substituting under a binder of the same variable would capture
      return Node::null();
    }
    // a binder in f's body must not capture a variable free in x
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
  return d_nm->mkNode(Kind::APPLY_UF, fn, x);
}

std::pair<Node, Node> BagsRewriter::lambdaOf(const Node& f) const
{
  // (t, b) for a lambda f of the variable t and the body b; for a function f
  // that is not a lambda, (t, (f t)) with t the row variable of its argument
  // sort
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    return std::make_pair(f[0][0], f[1]);
  }
  TypeNode domain = f.getType().getArgTypes()[0];
  Node t = rowVariable(domain);
  return std::make_pair(t, d_nm->mkNode(Kind::APPLY_UF, f, t));
}

bool BagsRewriter::readPositions(const Node& body,
                                 const Node& var,
                                 std::set<uint32_t>& positions) const
{
  // the columns body reads of var: {0, 2} for
  // (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)) and var t; false for
  // (= t (tuple a b)), which reads the whole row
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
      // the row itself, not through a selector: the whole row is read
      return false;
    }
    if (cur.getKind() == Kind::APPLY_SELECTOR && cur[0] == var)
    {
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

bool BagsRewriter::composable(const Node& f) const
{
  // f is a lambda of one variable, or a function array constant of one: the
  // rules that compose functions build lambdas of their bodies. A declared
  // function symbol f stays one, as upstream: (lambda ((t ..)) (f t)) would be
  // a lambda around a function the model interprets, a lambda the input did not
  // have
  Node l = asLambda(f);
  return l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 1;
}

Node BagsRewriter::mkLambda(const Node& var, const Node& body) const
{
  // the lambda of the variable var with the body body
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
}

BagsRewriteResponse BagsRewriter::rewriteFilterOfFilter(const TNode& n) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // FILTER_FILTER: two filters are one, by the conjunction,
  //   (bag.filter (lambda ((s T)) p) (bag.filter (lambda ((t T)) q) A))
  //   ---> (bag.filter (lambda ((t T)) (and p[s := t] q)) A)
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

BagsRewriteResponse BagsRewriter::rewriteFilterOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // FILTER_MAP: a filter of a map is the map of a filter by the predicate of
  // the image, p[s := e] for the filter (lambda ((s ..)) p) and the map
  // (lambda ((t ..)) e) (see rewrites.h)
  Node p = n[0];
  Node f = n[1][0];
  Node A = n[1][1];
  if (!composable(p) || !composable(f))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::pair<Node, Node> lf = lambdaOf(f);
  Node t = lf.first;
  Node body = applyFunction(p, lf.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node filtered = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), A);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, f, filtered);
  return BagsRewriteResponse(ret, Rewrite::FILTER_MAP);
}

BagsRewriteResponse BagsRewriter::rewriteMapOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // MAP_MAP: two maps are one, by the composition: e[s := g] for the outer map
  // (lambda ((s ..)) e) and the inner one (lambda ((t ..)) g) (see rewrites.h)
  Node f = n[0];
  Node g = n[1][0];
  Node A = n[1][1];
  if (!composable(f) || !composable(g))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::pair<Node, Node> lg = lambdaOf(g);
  Node t = lg.first;
  Node body = applyFunction(f, lg.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
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
  // product, which keeps the other factor's columns. With A and B of two
  // columns,
  //   (table.product (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
  //                           A)
  //                  B)
  //   --->
  //   (bag.map (lambda ((t V)) (tuple ((_ tuple.select 1) t)
  //                                   ((_ tuple.select 2) t)
  //                                   ((_ tuple.select 3) t)))
  //            (table.product A B))
  // and the same on the right, the image after A's columns; f is applied to
  // the factor's part of t, (tuple ((_ tuple.select 0) t)
  // ((_ tuple.select 1) t)) for A
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

BagsRewriteResponse BagsRewriter::postRewriteProject(const TNode& n) const
{
  if (!d_higherOrder)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // PROJECT_TO_MAP: a projection is a map by tuple.project (see rewrites.h)
  Assert(n.getKind() == Kind::TABLE_PROJECT);
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = d_nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  Node t = rowVariable(elementType);
  Node projection = d_nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, projection), A);
  return BagsRewriteResponse(ret, Rewrite::PROJECT_TO_MAP);
}

std::vector<uint32_t> BagsRewriter::projectionIndices(const Node& f) const
{
  // f = (lambda ((t ..)) (tuple ((_ tuple.select j0) t) .. ((_ tuple.select jm)
  // t))), or (lambda ((t ..)) ((_ tuple.project j0 .. jm) t)): the columns j0,
  // .., jm; empty for any other f
  std::vector<uint32_t> out;
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return out;
  }
  Node x = f[0][0];
  Node body = f[1];
  if (body.getKind() == Kind::TUPLE_PROJECT && body[0] == x)
  {
    return body.getOperator().getConst<ProjectOp>().getIndices();
  }
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple())
  {
    return out;
  }
  for (const Node& c : body)
  {
    if (c.getKind() != Kind::APPLY_SELECTOR || c[0] != x)
    {
      return std::vector<uint32_t>();
    }
    out.push_back(datatypes::utils::indexOf(c.getOperator()));
  }
  return out;
}

BagsRewriteResponse BagsRewriter::rewriteAggregateOfMap(const TNode& n) const
{
  // AGGREGATE_MAP: the fold reads each row through the map's function g, and
  // grouping by column k of the mapped row is grouping by the column of X's row
  // that g copies there (see rewrites.h). g may compute its other columns any
  // way: each group column of g's row must be a column of X's row; a constant,
  // which every row of a group shares and so drops out of the grouping; or a
  // term of group columns only (deptno + 42 beside deptno), which splits no
  // group the others do not
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
  Node gv = g[0][0];
  std::vector<uint32_t> K = n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<uint32_t> JK;
  std::vector<Node> computed;
  for (uint32_t k : K)
  {
    if (k >= g[1].getNumChildren())
    {
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
    // a key computed from columns that are keys themselves (deptno + 42
    // beside deptno) splits no group the others do not
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
  std::sort(JK.begin(), JK.end());
  JK.erase(std::unique(JK.begin(), JK.end()), JK.end());
  TypeNode rowType = X.getType().getBagElementType();
  if (!rowType.isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = rowVariable(rowType);
  Node y = f[0][1];
  Node gx = applyFunction(n[2][0], x);
  if (gx.isNull() || bindsVariable(f[1], x) || x == y)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node body = f[1].substitute(TNode(f[0][0]), TNode(gx));
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, y), body);
  Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(JK));
  std::vector<Node> children{op, lambda, i, X};
  Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_MAP);
}

bool BagsRewriter::rewritesToFalse(const Node& n) const
{
  Node r = d_rewriter->rewrite(n);
  return r.isConst() && !r.getConst<bool>();
}

bool BagsRewriter::rejectsInitialRow(const Node& P, const Node& i) const
{
  // whether P is false on the row of initial values i, the one row of the
  // aggregate of an empty table: (P i) rewrites to false. True for a test of a
  // count of rows, which starts at 0,
  //   P = (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int)))
  //         (>= ((_ tuple.select 2) r) 1))
  //   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
  if (d_rewriter == nullptr)
  {
    return false;
  }
  Node applied = applyFunction(P, i);
  return !applied.isNull() && rewritesToFalse(applied);
}

Node BagsRewriter::keyedAggregateRows(const Node& A) const
{
  // A = ((_ table.aggr K) f i X) whose group columns K contain a key of X
  // (see rowKeys): every group is one row t of X, once, folded once from i, so
  // the groups some row reached are the map of X by (lambda ((t ..)) (f t i)),
  // with (f t i) beta-reduced; null for any other A. Only the reached groups:
  // an empty X is one empty group, folded to the row of initial values,
  // (bag i 1), which the map does not have
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  Node f = asLambda(A[0]);
  if (K.empty() || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2)
  {
    return Node::null();
  }
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
  Node body = f[1].substitute(TNode(f[0][1]), TNode(A[1]));
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(f[0][0], body), A[2]);
}

Node BagsRewriter::accumulatorVariable(TypeNode type) const
{
  // the second variable of an aggregate's function, one per accumulator sort,
  // named accrow_N after the id N of the key (as bag.empty (Bag S)) of its sort
  // S
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(type)));
  return mkRewriterVar(
      d_nm, "accumulator", key, "accrow_" + std::to_string(key.getId()), type);
}

Node BagsRewriter::alphaKey(const Node& f) const
{
  // f with every variable it binds, at any depth, replaced by a placeholder for
  // its binding depth, and every variable free in it by one placeholder per
  // sort: equal for lambdas that differ only in the names of their variables,
  // and unchanged when a lambda inside f or around f renames its variables. The
  // keys of
  //   (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
  //   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
  // are one node, (lambda ((b0 (Tuple Int Int))) (> ((_ tuple.select 0) b0) 3))
  // with b0 the placeholder for depth 0; a free variable r of an enclosing
  // lambda becomes the placeholder of its sort, so the key of
  //   (lambda ((t (Tuple Int Int)))
  //     (= ((_ tuple.select 0) t) ((_ tuple.select 0) r)))
  // does not depend on r's name either. Cached in d_alphaKeys.
  std::unordered_map<Node, Node>::iterator it = d_alphaKeys.find(f);
  if (it != d_alphaKeys.end())
  {
    return it->second;
  }
  std::unordered_map<TNode, Node> bound;
  Node key = alphaKeyScope(f, bound, 0);
  d_alphaKeys[f] = key;
  return key;
}

Node BagsRewriter::alphaKeyScope(TNode root,
                                 std::unordered_map<TNode, Node>& bound,
                                 size_t depth) const
{
  // the alpha key of root, with bound mapping the variables of the enclosing
  // binders of root to their placeholders and depth the number of those
  // binders
  // the terms of one scope, converted once each: lambda bodies share subterms
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{root};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      std::unordered_map<TNode, Node>::iterator b = bound.find(n);
      if (b != bound.end())
      {
        cache[n] = b->second;
      }
      else
      {
        Node zero = d_nm->mkConstInt(Rational(0));
        cache[n] = mkRewriterVar(d_nm, "alpha-free", zero, n.getType());
      }
      todo.pop_back();
      continue;
    }
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    if (n.isClosure())
    {
      // a lambda of the variables s and acc at depth d becomes the lambda of
      // the placeholders b_d and b_d+1, its body converted in the scope of
      // those placeholders
      todo.pop_back();
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> vars;
      std::vector<std::pair<TNode, Node>> saved;
      for (size_t i = 0; i < nvars; i++)
      {
        TNode v = n[0][i];
        Node index = d_nm->mkConstInt(Rational(depth + i));
        Node p = mkRewriterVar(d_nm, "alpha-bound", index, v.getType());
        std::unordered_map<TNode, Node>::iterator b = bound.find(v);
        saved.push_back({v, b != bound.end() ? b->second : Node::null()});
        bound[v] = p;
        vars.push_back(p);
      }
      std::vector<Node> children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      children.push_back(d_nm->mkNode(Kind::BOUND_VAR_LIST, vars));
      for (size_t i = 1, nc = n.getNumChildren(); i < nc; i++)
      {
        children.push_back(alphaKeyScope(n[i], bound, depth + nvars));
      }
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
    size_t first = children.size();
    for (const Node& c : n)
    {
      Node cc = cache[c];
      changed = changed || cc != c;
      children.push_back(cc);
    }
    switch (n.getKind())
    {
      // the rewriter orders the arguments of these by node, which depends
      // on the names of the variables they read: the key must not
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
      // an arithmetic atom oriented by the order of its variables: as the
      // arithmetic rewriter orients it over the placeholders, so that
      // (>= (- a b) 0) and (not (>= (- b a) 1)) have one key; and its negation
      // too, which the atom's own orientation may have negated again
      built = d_rewriter->rewrite(built);
    }
    if (k == Kind::ITE && built.getKind() == Kind::ITE
        && built[0].getKind() == Kind::NOT)
    {
      // (ite (not c) a b) is (ite c b a), one key for both
      built = d_nm->mkNode(Kind::ITE, built[0][0], built[2], built[1]);
    }
    cache[n] = built;
  }
  return cache[root];
}

Node BagsRewriter::simplifyIteSame(const Node& body) const
{
  // (ite (= a b) b a) is a, and (ite (= a b) a b) is b, anywhere in body:
  // the translator's null-aware steps leave them once an accumulator is
  // known, e.g. the minimum step
  //   (ite (= (as nullable.null (Nullable Int)) acc) a (ite .. ..))
  // with acc a's own column
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
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
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
    Node m = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
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

Node BagsRewriter::canonicalLambda(const Node& f) const
{
  // f with its variables named after f's alpha key: lambdas that differ only in
  // the names of their variables become one node, so the solver purifies them
  // into one function symbol (see rewrites.h). Two lambdas one inside the other
  // have different keys, so canonical names never shadow each other, and the
  // key does not change when a lambda inside or around f is renamed, so
  // renaming terminates. With N the node id of f's alpha key, the variables of
  // a lambda of one variable are renamed to t_N, of two to t_N and acc_N; and
  // first (ite (= a b) b a) in the body is a, see simplifyIteSame
  Assert(f.getKind() == Kind::LAMBDA);
  {
    Node simpler = simplifyIteSame(f[1]);
    if (simpler != f[1])
    {
      return canonicalLambda(d_nm->mkNode(Kind::LAMBDA, f[0], simpler));
    }
  }
  size_t arity = f[0].getNumChildren();
  std::vector<Node> vars(f[0].begin(), f[0].end());
  Node key = alphaKey(f);
  std::vector<Node> canonical;
  for (size_t k = 0; k < arity; k++)
  {
    Node cache = d_nm->mkNode(Kind::SEXPR, key, d_nm->mkConstInt(Rational(k)));
    // named apart: a printed problem binds by name, and a canonical name
    // shared by a lambda and a variable free in it would capture it
    std::string name = (k == 0 ? "t_" : "acc_") + std::to_string(key.getId());
    canonical.push_back(
        mkRewriterVar(d_nm, "canonical", cache, name, vars[k].getType()));
  }
  if (canonical == vars)
  {
    return f;
  }
  Node body = f[1];
  for (size_t k = 0; k < arity; k++)
  {
    if (canonical[k] != vars[k] && expr::hasSubterm(body, canonical[k]))
    {
      return f;
    }
  }
  Node newBody = body.substitute(
      vars.begin(), vars.end(), canonical.begin(), canonical.end());
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, canonical), newBody);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateSortOutput(
    const TNode& n) const
{
  // AGGREGATE_SORT_OUTPUT: ((_ table.aggr K) f i X) where f builds a tuple: the
  // positions that copy a group column of the row come first, sorted by column,
  // then the others, sorted by what they compute
  // (the alpha key of their step and their initial value). Two aggregates that
  // output the same columns in different orders then differ only in the map
  // above them (see rewrites.h). The new step reads the sorted accumulator, so
  // the new fold computes the sorted rows of the old one
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
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
  Node x = f[0][0];
  Node y = f[0][1];
  size_t m = f[1].getNumChildren();
  // (class, rank) per position: class 0 for key copies ranked by column,
  // class 1 for the others ranked by what they compute (the alpha key of the
  // step and seed) when every one reads only its own accumulator column, by
  // position otherwise
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
      order.push_back({{0, datatypes::utils::indexOf(c.getOperator())}, q});
    }
    else if (independent)
    {
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
      order.push_back({{1, q}, q});
    }
  }
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
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<uint32_t> inverse(m);  // old position -> new position
  for (uint32_t q = 0; q < m; q++)
  {
    inverse[sigma[q]] = q;
  }
  TypeNode oldType = f[1].getType();
  std::vector<TypeNode> types;
  for (uint32_t q = 0; q < m; q++)
  {
    types.push_back(oldType.getTupleTypes()[sigma[q]]);
  }
  TypeNode newType = d_nm->mkTupleType(types);
  Node acc = accumulatorVariable(newType);
  if (acc == x || (acc != y && expr::hasSubterm(f[1], acc)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the old accumulator over the new one, whose position p is position
  // inverse[p] of acc: (tuple ((_ tuple.select 1) acc) ((_ tuple.select 0)
  // acc)) in the example
  std::vector<Node> oldAcc;
  for (uint32_t p = 0; p < m; p++)
  {
    oldAcc.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, inverse[p]));
  }
  Node unsortedAcc = datatypes::TupleUtils::constructTupleFromElements(
      oldType, oldAcc, 0, m - 1);
  Node body = f[1].substitute(TNode(y), TNode(unsortedAcc));
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
  std::vector<Node> children{n.getOperator(), lambda, newI, X};
  Node sortedAggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
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

BagsRewriteResponse BagsRewriter::rewriteFoldOfTuple(const TNode& n) const
{
  // FOLD_TUPLE: a fold of tuples whose component k reads the accumulator only
  // at position k is the tuple of the folds of the components, each with its
  // own step, ((_ tuple.select k) acc) read as its accumulator
  // (see rewrites.h). The folds over X read its elements in one order, so each
  // component is the fold of its own step.
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
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
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> components;
  for (size_t k = 0; k < m; k++)
  {
    std::set<uint32_t> positions;
    if (!readPositions(body[k], acc, positions) || bindsVariable(body[k], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    for (uint32_t pos : positions)
    {
      if (pos != k)
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
    TypeNode type = body[k].getType();
    Node a = accumulatorVariable(type);
    if (a == x || expr::hasSubterm(body[k], a))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node selected = datatypes::TupleUtils::nthElementOfTuple(acc, k);
    Node step = body[k].substitute(TNode(selected), TNode(a));
    if (expr::hasSubterm(step, acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node lambda = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, a), step);
    Node seed = datatypes::TupleUtils::nthElementOfTuple(i, k);
    components.push_back(d_nm->mkNode(Kind::BAG_FOLD, lambda, seed, X));
  }
  Node ret = datatypes::TupleUtils::constructTupleFromElements(
      n.getType(), components, 0, m - 1);
  return BagsRewriteResponse(ret, Rewrite::FOLD_TUPLE);
}

BagsRewriteResponse BagsRewriter::rewriteSetofOfMap(const TNode& n) const
{
  // SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, the set of a map:
  // * f a constant c:
  //     (bag.setof (bag.map (lambda ((t T)) c) Y))
  //     ---> (bag c (ite (= Y (as bag.empty (Bag T))) 0 1))
  // * f a projection onto columns in another order than theirs: the set of
  //   the projection onto the sorted columns, mapped back by the
  //   permutation, which is injective and so commutes with duplicate removal,
  //     (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
  //                                                ((_ tuple.select 0) t)))
  //                         Y))
  //     --->
  //     (bag.map (lambda ((r U)) (tuple ((_ tuple.select 1) r)
  //                                     ((_ tuple.select 0) r)))
  //              (bag.setof (bag.map (lambda ((t T))
  //                                    (tuple ((_ tuple.select 0) t)
  //                                           ((_ tuple.select 2) t)))
  //                                  Y)))
  // * f a tuple some of whose components are constants: the constants are
  //   put back by an injective map over the set of the other components,
  //     (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t) 5))
  //                         Y))
  //     --->
  //     (bag.map (lambda ((r U)) (tuple ((_ tuple.select 0) r) 5))
  //              (bag.setof (bag.map (lambda ((t T))
  //                                    (tuple ((_ tuple.select 1) t)))
  //                                  Y)))
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
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  {
    // a projection onto columns in another order than theirs: the set of the
    // projection onto the sorted columns, mapped back by the permutation,
    // which is injective and so commutes with duplicate removal
    std::vector<uint32_t> J = projectionIndices(f);
    if (!J.empty())
    {
      std::vector<uint32_t> sorted = J;
      std::sort(sorted.begin(), sorted.end());
      sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
      if (sorted != J)
      {
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
  // SEMI_JOIN: (bag.map f (bag.filter p (table.product X0 (table.product X1
  // ..)))) with a component B = Xj that is a set (a bag.setof, or a table
  // with a key, whose rows are distinct), f reading none of B's columns
  // (or only columns that p equates to columns of the others), and p having,
  // for every column of B or for every column of a key of B, a conjunct
  // (= ((_ tuple.select c) t) e) with e reading no column of B: a row of the
  // other components meets at most one row of B that passes, so the product
  // passes each of their rows once when one does. With Y of two columns and
  // the key {0} of B = Z,
  //   (bag.map (lambda ((t V)) (tuple ((_ tuple.select 1) t)))
  //            (bag.filter (lambda ((t V)) (= ((_ tuple.select 0) t)
  //                                           ((_ tuple.select 2) t)))
  //                        (table.product Y Z)))
  //   --->
  //   (bag.map (lambda ((a U)) (tuple ((_ tuple.select 1) a)))
  //            (bag.filter (lambda ((a U))
  //                          (not (= (bag.filter (lambda ((b W))
  //                                                (= ((_ tuple.select 0) a)
  //                                                   ((_ tuple.select 0) b)))
  //                                              Z)
  //                                  (as bag.empty (Bag W)))))
  //                        Y))
  // the product of the other components A (Y here) filtered by pA, the
  // conjuncts reading no column of B, and the existence of a row of B that
  // passes pAB, the others: the shape of SQL's EXISTS and IN, which other
  // rules decorrelate (see rewriteEmptyFilter). Called with side 0 only;
  // every component is tried, the one with the smallest node first, so that
  // one join written in two orders is rewritten alike.
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
    // (not (= (bag.filter (lambda ((b W)) pAB) B) (as bag.empty (Bag W))))
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

Node BagsRewriter::rewriteEmptyFilter(const Node& F) const
{
  // EQ_EMPTY_FILTER_DECORRELATE, for the emptiness of a filter F in the body
  // of an enclosing lambda over a row r:
  //   (= (as bag.empty (Bag T)) (bag.filter (lambda ((s T)) (and c q e)) X))
  // where c reads no s (only r, or nothing), q reads only s, and each
  // equation e ties a column of s to a term E that reads no s, such as
  // (= ((_ tuple.select 1) s) ((_ tuple.select 0) r)): no row of X passes
  // when c fails, or when the tuple of the E is not among the columns of the
  // rows that pass q,
  //   --->
  //   (or (not c)
  //       (not (>= (bag.count (tuple ((_ tuple.select 0) r))
  //                           (bag.map (lambda ((s T))
  //                                      (tuple ((_ tuple.select 1) s)))
  //                                    (bag.filter (lambda ((s T)) q) X)))
  //                1)))
  // The bag no longer depends on the enclosing row, so a filter over this
  // predicate is not a new bag per row the solver reads. Returns that
  // formula, or null when F is not of that shape.
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
      // an equation between a column and a constant is a key as well:
      //   (= (as bag.empty (Bag T))
      //      (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 10)) X))
      // says 10 is not among the column's values
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

Node BagsRewriter::truthOf(const Node& X) const
{
  // the formula X = (nullable.some true) for a nullable Boolean X built of
  // ites over (nullable.some b) and null, or null when X is not: for
  //   X = (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
  // the formula (ite c b false)
  if (X.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    return X.getNumChildren() == 1 ? X[0] : d_nm->mkConst(false);
  }
  if (X.getKind() == Kind::ITE)
  {
    Node a = truthOf(X[1]);
    Node b = truthOf(X[2]);
    if (a.isNull() || b.isNull())
    {
      return Node::null();
    }
    return d_nm->mkNode(Kind::ITE, X[0], a, b);
  }
  return Node::null();
}

Node BagsRewriter::normalizeTruth(const Node& body) const
{
  // FILTER_NULLABLE_TRUTH: the conjuncts (nullable.is_some X) and
  // (nullable.val X) of body, for X a nullable Boolean of ites over
  // constants and (nullable.some b), replaced by the formula
  // X = (nullable.some true) they say, see truthOf:
  //   (and (nullable.is_some X) (nullable.val X) q)
  //   ---> (and (ite c b false) q)
  // for X = (ite c (nullable.some b) (as nullable.null (Nullable Bool))), so
  // that SQL's WHERE over a three-valued condition, written either way, is
  // one formula
  std::vector<Node> conjuncts;
  if (body.getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), body.begin(), body.end());
  }
  else
  {
    conjuncts.push_back(body);
  }
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
  std::vector<Node> out;
  bool changed = false;
  std::set<Node> done;
  for (const Node& c : conjuncts)
  {
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
        // both conjuncts become the one formula
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

BagsRewriteResponse BagsRewriter::rewriteAggregateDeadColumns(
    const TNode& n) const
{
  // AGGREGATE_DEAD_COLUMNS: in
  // (bag.map h (bag.filter P ((_ table.aggr K) f i X))), or the same without
  // the filter, where h and P read no column q of the aggregate's rows and f
  // computes column q from the row and from column q of the accumulator only,
  // which no other column reads, column q changes nothing that anything reads,
  // and goes (see rewrites.h). Grouping is by K, columns of X, so no output
  // column decides a group.
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
  // which accumulator columns each component reads
  std::vector<std::set<uint32_t>> reads(m);
  for (size_t q = 0; q < m; q++)
  {
    if (!readPositions(f[1][q], acc, reads[q]) || bindsVariable(f[1][q], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
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
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode newType = d_nm->mkTupleType(types);
  Node acc2 = accumulatorVariable(newType);
  Node r2 = rowVariable(newType);
  if (acc2 == x || expr::hasSubterm(f[1], acc2) || expr::hasSubterm(h[1], r2)
      || (!P.isNull() && expr::hasSubterm(P[1], r2)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // a kept column of the old row, read from the new one
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
  Node f2 = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
  Node i2 = datatypes::TupleUtils::constructTupleFromElements(
      newType, init, 0, init.size() - 1);
  std::vector<Node> children{Y.getOperator(), f2, i2, X};
  Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  Node h2body = reindex(h[1], h[0][0], r2);
  if (occursFree(h2body, h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node below = aggr;
  if (!P.isNull())
  {
    Node p2body = reindex(P[1], P[0][0], r2);
    if (occursFree(p2body, P[0][0]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    below = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r2, p2body), aggr);
  }
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(r2, h2body), below);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_DEAD_COLUMNS);
}

std::map<uint32_t, Node> BagsRewriter::fixedColumns(const Node& p) const
{
  // the columns a filter's predicate fixes to a constant, by conjuncts
  // (= ((_ tuple.select k) t) c) with c a constant: {1 -> 5} for
  //   (lambda ((t (Tuple Int Int)))
  //     (and (= ((_ tuple.select 1) t) 5) (> ((_ tuple.select 0) t) 3)))
  std::map<uint32_t, Node> fixed;
  Node lambda = asLambda(p);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1)
  {
    return fixed;
  }
  Node t = lambda[0][0];
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

Node BagsRewriter::readFixed(const Node& body,
                             const Node& var,
                             const std::map<uint32_t, Node>& fixed) const
{
  // body with each column of var that fixed names replaced by its constant:
  // with {1 -> 5}, ((_ tuple.select 1) var) is read as 5
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

std::map<uint32_t, Node> BagsRewriter::reachedGroupConstants(
    const Node& F) const
{
  // F = (bag.filter P ((_ table.aggr K) f i X)) where P has a conjunct
  // (>= ((_ tuple.select c) r) 1) and f counts in column c from 0,
  // (+ ((_ tuple.select c) acc) 1): P keeps the groups some row reached,
  // never the row of initial values an empty X gives, so a column that f
  // sets to a constant is that constant in every row P keeps, and a column
  // that f keeps as it is, ((_ tuple.select q) acc), is its seed; for f's
  // result (tuple ((_ tuple.select 0) t) 7 ((_ tuple.select 2) acc) (+ ..))
  // and seed (tuple .. .. 4 0), the map {1 -> 7, 2 -> 4}
  std::map<uint32_t, Node> constants;
  Node P = asLambda(F[0]);
  Node aggr = F[1];
  Node f = aggr[0];
  Node i = aggr[1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return constants;
  }
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
  bool reached = false;
  for (const Node& c : conjuncts)
  {
    // (>= ((_ tuple.select c) r) 1)
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
      constants[q] = c;
    }
    else if (c == datatypes::TupleUtils::nthElementOfTuple(acc, q)
             && i[q].isConst())
    {
      // a column the step keeps as it is: its seed
      constants[q] = i[q];
    }
  }
  return constants;
}

int BagsRewriter::counterColumn(const Node& P,
                                const Node& f,
                                const Node& i) const
{
  // the column c of a (bag.filter P ((_ table.aggr K) f i X)) that counts the
  // rows of each group, (+ ((_ tuple.select c) acc) 1) from 0, if P has the
  // conjunct (>= ((_ tuple.select c) r) 1); -1 otherwise. The translator adds
  // such a counter to every aggregate with group columns: SQL's GROUP BY
  // makes no group of an empty table, while table.aggr folds it to one row
  // of initial values, the row the test drops
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return -1;
  }
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

Node BagsRewriter::dropKnownMemberships(const Node& body,
                                        const Node& t,
                                        const Node& A) const
{
  // FILTER_KNOWN_MEMBERSHIP: the conjuncts of a filter's body over rows t of
  // A that say what holds of every such row, or what another conjunct says,
  // go:
  // * (>= (bag.count (g c) (bag.map g X)) 1) where c is the part of t a
  //   component X of A (or a filter over X) gives: c is a row of X;
  // * the same where the component is an aggregate over X (or a map of X)
  //   in a group some row of X reached, and g reads only its group columns:
  //   some row of X has those values;
  // * (>= (bag.count E' (bag.map g' X)) 1) beside (>= (bag.count E (bag.map
  //   g X)) 1) where g' and E' select columns of g and E: the second says it.
  // With A = (table.product X Y),
  //   (and (>= (bag.count (tuple ((_ tuple.select 0) t))
  //                       (bag.map (lambda ((s T))
  //                                  (tuple ((_ tuple.select 0) s)))
  //                                X))
  //            1)
  //        q)
  //   ---> q
  // the membership SQL's IN (SELECT a FROM X) leaves after a join with X
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
            || g2[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
          || fa[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
    if (J.empty() || E.getKind() != Kind::APPLY_CONSTRUCTOR)
    {
      continue;
    }
    for (size_t o = 0; o < conjuncts.size() && !drop[k]; o++)
    {
      Node E2, g2, X2;
      if (o == k || drop[o] || !membership(conjuncts[o], E2, g2, X2) || X2 != X
          || E2.getKind() != Kind::APPLY_CONSTRUCTOR)
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
  // these that keeps, of every component, all its columns or a key; with
  // the key {0} of X and of Y, true for
  //   (bag.map (lambda ((t V)) (tuple ((_ tuple.select 0) t)
  //                                   ((_ tuple.select 2) t)))
  //            (table.product X Y))
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

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

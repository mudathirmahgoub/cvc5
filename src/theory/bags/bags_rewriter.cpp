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
 * Notation. The comments of this file write terms in SMT-LIB syntax, with
 * cvc5's operators for tuples, nullables, bags and tables:
 *
 *   (tuple a b)                     a row of sort (Tuple Int Int)
 *   ((_ tuple.select 1) t)          column 1 of the row t
 *   ((_ tuple.project 0 2) t)       the row (tuple ((_ tuple.select 0) t)
 *                                   ((_ tuple.select 2) t))
 *   (nullable.some 5)               a value of sort (Nullable Int)
 *   (as nullable.null (Nullable Int))
 *   (nullable.is_some x), (nullable.val x)
 *   (bag e 2)                       the bag with e twice (Kind::BAG_MAKE)
 *   (as bag.empty (Bag T))
 *   (bag.count e X)                 the multiplicity of e in X
 *   (bag.union_disjoint X Y)        multiplicities added
 *   (bag.inter_min X Y)             the smaller multiplicity of the two
 *   (bag.difference_subtract X Y)   multiplicities subtracted, down to 0
 *   (bag.setof X)                   X with every multiplicity cut to 1
 *   (bag.map (lambda ((t T)) b) X)  b for every row t of X, multiplicities
 *                                   of equal images added
 *   (bag.filter (lambda ((t T)) p) X)
 *   (bag.fold (lambda ((t T) (acc S)) b) i X)
 *                                   b folded over the rows of X, from i
 *   (table.product X Y)             the rows of X followed by those of Y
 *   ((_ table.project 0 2) X)       (bag.map of tuple.project 0 2 over X)
 *   ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X)
 *                                   X split into the groups of its rows with
 *                                   the same column 0, each group folded as
 *                                   by bag.fold from i, the results a bag
 *
 * Unless said otherwise, X, Y and Z are tables (bags of tuples) with rows of
 * sort T and U, t and s are rows bound by a lambda, acc is an accumulator, and
 * a, b, c are terms. The rewriter makes its own bound variables, named row_N,
 * t_N and acc_N; the examples write them t and acc. SQL's three-valued
 * logic is encoded with (Nullable Bool): a predicate p holds of a row when p
 * is (nullable.some true), written (= p (nullable.some true)), see truthOf.
 */

/**
 * The keys of a table constant X: an SEXPR of SEXPRs of column indices, one
 * per key, recorded by recordKey when the rewriter meets the key's assertion.
 * The translator states that columns 0 and 2 of X are a key as
 *   (= (bag.setof (bag.map (lambda ((t T)) ((_ tuple.project 0 2) t)) X))
 *      (bag.map (lambda ((t T)) ((_ tuple.project 0 2) t)) X))
 * and X then gets the attribute (SEXPR (SEXPR 0 2)).
 */
struct BagsKeysAttributeId
{
};
typedef expr::Attribute<BagsKeysAttributeId, Node> BagsKeysAttribute;
/**
 * A term of an assertion the rewriter reads a fact from: the
 * (bag.setof (bag.map (lambda ((t T)) ((_ tuple.project 0 2) t)) X)) of a key
 * assertion, or the (bag.filter ..) of a not-null assertion. Such a term is
 * never rewritten: the fact it states would justify rewriting it away (the
 * bag.setof of a projection onto a key is the projection itself), and the
 * assertion would become true and the fact lost.
 */
struct BagsKeyTermAttributeId
{
};
typedef expr::Attribute<BagsKeyTermAttributeId, bool> BagsKeyTermAttribute;
/**
 * The columns of a table constant X that hold no null: an SEXPR of column
 * indices, recorded by recordNotNull when the rewriter meets the assertion
 *   (= (bag.filter (lambda ((t T))
 *                    (= (as nullable.null (Nullable Int))
 *                       ((_ tuple.select 1) t)))
 *        X)
 *      (as bag.empty (Bag T)))
 * that column 1 of X is NOT NULL; X then gets the attribute (SEXPR 1).
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
    // COUNT_MAP_DUPLICATE_COLUMNS: every row the map makes has equal columns
    // i < j (the same term u), so a probe occurs only when its columns i and
    // j are equal too, and column j can be dropped from the probe and the map:
    //   (bag.count (tuple a b c) (bag.map (lambda ((t T)) (tuple u v u)) X))
    //   --->
    //   (ite (= a c)
    //        (bag.count (tuple a b) (bag.map (lambda ((t T)) (tuple u v)) X))
    //        0)
    // A probe e that is not a tuple term has the columns
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
          // g2 is (lambda ((t T)) (tuple u v)), e2 is (tuple a b)
          Node g2 = mkLambda(g[0][0],
                             datatypes::TupleUtils::constructTupleFromElements(
                                 t, cols, 0, cols.size() - 1));
          Node e2 = datatypes::TupleUtils::constructTupleFromElements(
              t, probe, 0, probe.size() - 1);
          // (bag.count (tuple a b) (bag.map (lambda ((t T)) (tuple u v)) X))
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
    // COUNT_MAP_CONST_COLUMN: column j of every row the map makes is the
    // constant c, so a probe occurs only when its column j is c, and the
    // column can be dropped from the probe and the map:
    //   (bag.count (tuple a b)
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
    //                       X))
    //   --->
    //   (ite (= b 5)
    //        (bag.count (tuple a)
    //                   (bag.map (lambda ((t T))
    //                              (tuple ((_ tuple.select 0) t)))
    //                            X))
    //        0)
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
        // g2 is (lambda ((t T)) (tuple ((_ tuple.select 0) t))), e2 is
        // (tuple a)
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
  if ((n[1].getKind() == Kind::BAG_MAP
       || (n[1].getKind() == Kind::VARIABLE
           && n[1].getType().getBagElementType().isTuple()
           && n[1].getType().getBagElementType() == n[0].getType()))
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
                       d_nm->mkNode(Kind::BOUND_VAR_LIST, v),
                       datatypes::TupleUtils::constructTupleFromElements(
                           et, cols, 0, cols.size() - 1)),
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
  if (n[1].getKind() == Kind::BAG_MAP && n[1][1].getKind() == Kind::BAG_FILTER)
  {
    // COUNT_MAP_FILTER_KEYS: g projects the rows of X onto columns J, and a
    // conjunct of the filter reads only those columns (or no row at all):
    // every row g maps to the probe agrees with the probe on them, so the
    // conjunct holds of all those rows or of none, and is decided on the
    // probe instead, with ((_ tuple.select J[k]) t) read as column k of it:
    //   (bag.count (tuple a)
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
    //                       (bag.filter (lambda ((t T))
    //                                     (and (> ((_ tuple.select 0) t) 3)
    //                                          (< ((_ tuple.select 1) t) 7)))
    //                                   X)))
    //   --->
    //   (ite (> a 3)
    //        (bag.count (tuple a)
    //                   (bag.map (lambda ((t T))
    //                              (tuple ((_ tuple.select 0) t)))
    //                            (bag.filter (lambda ((t T))
    //                                          (< ((_ tuple.select 1) t) 7))
    //                                        X)))
    //        0)
    // COUNT_MAP_FILTER_CORRELATED: a conjunct that equates another column of
    // the row with a term E that is not a constant and does not read the row
    // (a column of an enclosing row r, in a correlated subquery) becomes one
    // more column of the map and of the probe:
    //   (bag.count (tuple a)
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
    //                       (bag.filter (lambda ((t T))
    //                                     (and (= ((_ tuple.select 1) t)
    //                                             ((_ tuple.select 0) r))
    //                                          (> ((_ tuple.select 0) t) 3)))
    //                                   X)))
    //   --->
    //   (bag.count (tuple a ((_ tuple.select 0) r))
    //              (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
    //                                              ((_ tuple.select 1) t)))
    //                       (bag.filter (lambda ((t T))
    //                                     (> ((_ tuple.select 0) t) 3))
    //                                   X)))
    // which leaves the filter free of r, so that the counts for two
    // enclosing rows are counts in one bag.
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
        if (gBody.getKind() == Kind::APPLY_CONSTRUCTOR
            && !bindsVariable(g0[1], g0[0][0]))
        {
          TypeNode t = d_nm->mkTupleType(types);
          // g2 is (lambda ((t T)) (tuple ((_ tuple.select 0) t)
          //                              ((_ tuple.select 1) t)))
          // e2 is (tuple a ((_ tuple.select 0) r))
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
          // (bag.filter (lambda ((t T)) (> ((_ tuple.select 0) t) 3)) X)
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

BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // the bag.setof of a key assertion, see BagsKeyTermAttribute
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
    // AGGREGATE_GROUP_KEYS: the group columns of the groups a row reached,
    // as a set, are those of the rows, see keysOfReachedGroups; with f
    // copying the group column 0 of X to its column 0 and counting rows in
    // its column 2,
    //   (bag.setof (bag.map (lambda ((r V)) (tuple ((_ tuple.select 0) r)))
    //                       (bag.filter (lambda ((r V))
    //                                     (>= ((_ tuple.select 2) r) 1))
    //                                   ((_ table.aggr 0) f i X))))
    //   --->
    //   (bag.setof (bag.map (lambda ((s T)) (tuple ((_ tuple.select 0) s)))
    //                       X))
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
    // (bag.setof (bag x n)) = (bag x (ite (>= n 1) 1 0))
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
    // conjunct, p in one and (not p) in the other, keep together the rows of
    // X the other conjuncts keep: every row of X passes one of the two or
    // neither, never both,
    //   (bag.union_disjoint
    //     (bag.filter (lambda ((t T)) (and p q)) X)
    //     (bag.filter (lambda ((t T)) (and (not p) q)) X))
    //   --->
    //   (bag.filter (lambda ((t T)) q) X)
    // also under one map g of both, (bag.union_disjoint (bag.map g F1)
    // (bag.map g F2)) ---> (bag.map g F), and for two parts of a longer union,
    // the other parts unioned to the result. The two filters' variables
    // may differ, the second is renamed to the first.
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
    // a part (bag.map g (bag.filter (lambda ((x T)) (and c1 c2)) X)) seen as
    // g, X, x and the conjuncts c1, c2; g is null for a part without a map
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
        // (bag.filter (lambda ((t T)) q) X), under (bag.map g ..) if any
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
    // conditions qA read off A's filters (elementConditions), so an element of
    // B that is also in A does too, and the other way round; each side gets
    // the conditions of the other it lacks,
    //   (bag.inter_min (bag.filter (lambda ((t T)) qA) X)
    //                  (bag.filter (lambda ((t T)) qB) Y))
    //   --->
    //   (bag.inter_min (bag.filter (lambda ((t T)) qB)
    //                              (bag.filter (lambda ((t T)) qA) X))
    //                  (bag.filter (lambda ((t T)) qA)
    //                              (bag.filter (lambda ((t T)) qB) Y)))
    // which the filter rules merge, so that both sides have the same
    // filters; each new filter is rewritten here, to see whether anything
    // changed
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
  // n is (= (bag.setof M) M), either way round, with M a projection of a
  // table constant X onto columns K, as the input states it,
  //   M = ((_ table.project 0 2) X)
  // or as the rewriter leaves it,
  //   M = (bag.map (lambda ((t T)) ((_ tuple.project 0 2) t)) X):
  // no two rows of X agree on K, a key of X
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
    // the bag.setof of the assertion, and the one the rewriting of its
    // argument will build, (bag.setof (bag.map (lambda ((t T)) (tuple
    // ((_ tuple.select 0) t) ((_ tuple.select 2) t))) X)), are not rewritten
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
  // n is
  //   (= (bag.filter (lambda ((t T))
  //                    (= (as nullable.null (Nullable Int))
  //                       ((_ tuple.select k) t)))
  //                  X)
  //      (as bag.empty (Bag T)))
  // either way round: no row of the table constant X has a null in column k
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
    // seeded non-null, every step non-null or the accumulator:
    //   (bag.fold (lambda ((t T) (acc (Nullable Int)))
    //               (ite p (nullable.some ..) acc))
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
  // the columns of ((_ table.aggr K) f i X) never null: those whose seed is
  // not and whose step keeps them so; in a group a row reached, also those the
  // step makes non-null from these. With
  //   f = (lambda ((t T) (acc (Tuple (Nullable Int) (Nullable Int))))
  //         (tuple ((_ tuple.select 0) acc) (nullable.some 1)))
  //   i = (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
  // column 0 is never null (its seed is not and its step keeps it), and
  // column 1 is not null in the groups a row reached (reached is true): the
  // first step makes it (nullable.some 1)
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
  // columns asserted NOT NULL of a table constant (BagsNotNullAttribute), and
  // what the operators above keep or establish, e.g. with column 0 of X
  // never null,
  //   (bag.filter (lambda ((t T)) (nullable.is_some ((_ tuple.select 1) t)))
  //               X)
  // has the columns 0 and 1 never null
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
        // column j of (bag.map (lambda ((t T)) (tuple a0 .. am)) X) is never
        // null when aj is not, given the never-null columns of X
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
  // keys of B read off its structure: a table's declared keys, kept by
  // filters, intersections and differences, by maps that keep their columns,
  // and combined by products; all the columns of a bag.setof; the group
  // columns an aggregate's rows keep. Every key found makes B a set. E.g.
  // with the key {0} of X and {0} of Y,
  //   (table.product X Y) has the key {0, 2} (Y's column 0 is column 2 of
  //   the product, for X of two columns);
  //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)
  //                                   ((_ tuple.select 0) t)))
  //            X) has the key {1};
  //   ((_ table.aggr 0) f i X) has the key {k} when column k of f's result
  //   is ((_ tuple.select 0) t), the group column.
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
      // a column the filter fixes to a constant decides nothing, and one it
      // sets equal to another is that one: with the key {0, 1} of X,
      //   (bag.filter (lambda ((t T)) (= ((_ tuple.select 1) t) 5)) X)
      // has the key {0}, and with the key {1, 2},
      //   (bag.filter (lambda ((t T)) (= ((_ tuple.select 0) t)
      //                                  ((_ tuple.select 2) t)))
      //               X)
      // has the key {0, 1} (column 2 is column 0)
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
      // all the columns, but a constant column or one that repeats another
      // one of (bag.setof (bag.map (lambda ((t T)) (tuple ..)) X)) only once
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
  if (n.getType() == n[1].getType()
      && n[1].getType().getBagElementType().isTuple())
  {
    // MAP_IDENTITY: the map that copies every column in order,
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
    //                                   ((_ tuple.select 1) t)))
    //            X)
    //   ---> X
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
    // NOT_NULL_COLUMNS: the null tests of columns the rows of X never have
    // null are decided, see assumeNonNull; with column 1 of X never null,
    //   (bag.map (lambda ((t T))
    //              (ite (nullable.is_some ((_ tuple.select 1) t)) a b))
    //            X)
    //   --->
    //   (bag.map (lambda ((t T)) (ite true a b)) X)
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
  // documented at its function: MAP_SPLIT_CLOSED, AGGREGATE_DEAD_COLUMNS,
  // AGGREGATE_COLLAPSE, AGGREGATE_ROLLUP, AGGREGATE_JOIN_MERGE,
  // PRODUCT_AGGREGATE_DEAD_COLUMN, AGGREGATE_UNION_DISJOINT_KEYS and
  // AGGREGATE_UNION_SPLIT
  {
    BagsRewriteResponse r = rewriteMapSplitClosed(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateDeadColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateCollapse(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateRollup(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateJoinMerge(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteProductAggregateColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateUnionDisjointKeys(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    BagsRewriteResponse r = rewriteAggregateUnionSplit(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // MAP_EQUAL_COLUMNS: a row that passes has the columns the filter equates
    // equal, and the map reads the first of them (the smallest column):
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)))
    //            (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
    //                                           ((_ tuple.select 2) s)))
    //                        X))
    //   --->
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
    //            (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
    //                                           ((_ tuple.select 2) s)))
    //                        X))
    // so that two queries that read either column become one term; rep is a
    // union-find over the columns, each pointing to the smallest it equals
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
    // MAP_FIXED_COLUMNS: a row that passes has the constants the filter fixes
    // its columns to, and the map reads those instead, see readFixed:
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
    //                                   ((_ tuple.select 1) t)))
    //            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X))
    //   --->
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
    //            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X))
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
    // MAP_IDENTITY_ON_FILTER: the identity on the rows that pass, every
    // column is the row's own or the constant the filter fixes it to:
    //   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
    //            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X))
    //   --->
    //   (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X)
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
    // CANONICAL_VARIABLE: the lambda over the canonical variable of its
    // body, see canonicalLambda,
    //   (bag.map (lambda ((s T)) ((_ tuple.select 0) s)) X)
    //   ---> (bag.map (lambda ((t_N T)) ((_ tuple.select 0) t_N)) X)
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
    // FILTER_COUNT_AS_COUNTER: an aggregate with a counter column c, whose
    // step is (+ ((_ tuple.select c) acc) 1) from 0, has on every row a
    // COUNT(*) column q (one whose step counts rows from (nullable.some 0),
    // see isCountStep) equal to (nullable.some ((_ tuple.select c) t)); the
    // filter reads column q so, which makes a test of COUNT(*) a test of the
    // counter that the solver relates to the group's rows. With c = 2, q = 1,
    //   (bag.filter (lambda ((t T))
    //                 (= ((_ tuple.select 1) t) (nullable.some 3)))
    //               ((_ table.aggr 0) f i X))
    //   --->
    //   (bag.filter (lambda ((t T))
    //                 (= (nullable.some ((_ tuple.select 2) t))
    //                    (nullable.some 3)))
    //               ((_ table.aggr 0) f i X))
    // also for the aggregates among the components of a product; the
    // components of (table.product G (table.product Y Z)) are G, Y and Z,
    // whose columns start at starts[i] in the product's rows
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
            || f[0].getNumChildren() != 2
            || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
            || G[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
    // NOT_NULL_COLUMNS: the null tests of columns the rows of A never have
    // null are decided, see assumeNonNull; with column 1 of X never null,
    //   (bag.filter (lambda ((t T))
    //                 (and (nullable.is_some ((_ tuple.select 1) t)) p))
    //               X)
    //   --->
    //   (bag.filter (lambda ((t T)) (and true p)) X)
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
      // FILTER_TRUE and FILTER_FALSE:
      //   (bag.filter (lambda ((t T)) true) A) ---> A
      //   (bag.filter (lambda ((t T)) false) A) ---> (as bag.empty (Bag T))
      // (the rewriter keeps a constant lambda as a function array constant,
      // see asLambda)
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
      // FILTER_DE_MORGAN: (not (or a b)) among the conjuncts is (not a) and
      // (not b), conjuncts the rules below read one at a time:
      //   (bag.filter (lambda ((t T)) (and p (not (or a b)))) X)
      //   ---> (bag.filter (lambda ((t T)) (and p (not a) (not b))) X)
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
      // FILTER_CONFLICTING_CONSTANTS: a conjunction that fixes one term to two
      // distinct constants holds for no row,
      //   (bag.filter (lambda ((t T)) (and (= ((_ tuple.select 0) t) 1)
      //                                    (= ((_ tuple.select 0) t) 2)))
      //               X)
      //   ---> (as bag.empty (Bag T))
      // fixed maps each term a conjunct fixes to its constant
      std::map<Node, Node> fixed;
      for (const Node& c : flat)
      {
        if (c.getKind() != Kind::EQUAL || c[0].isConst() == c[1].isConst())
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
      // FILTER_KNOWN_NONEMPTY: a bag that a membership conjunct finds a row
      // in, or a bag it reaches that row through maps, filters and bag.setof,
      // is not empty:
      //   (bag.filter (lambda ((t T))
      //                 (and (>= (bag.count ((_ tuple.project 0) t)
      //                                     (bag.map g Y))
      //                          1)
      //                      (not (= Y (as bag.empty (Bag U))))))
      //               X)
      //   --->
      //   (bag.filter (lambda ((t T))
      //                 (>= (bag.count ((_ tuple.project 0) t) (bag.map g Y))
      //                     1))
      //               X)
      // and the filter is empty when the conjunct says that the bag is
      // empty
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
      // FILTER_FALSE: a conjunct and its negation, no row passes,
      //   (bag.filter (lambda ((t T)) (and p (not p))) X)
      //   ---> (as bag.empty (Bag T))
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

    // FILTER_FILTER and FILTER_MAP, see rewriteFilterOfFilter and
    // rewriteFilterOfMap
    case Kind::BAG_FILTER: return rewriteFilterOfFilter(n);
    case Kind::BAG_MAP: return rewriteFilterOfMap(n);
    case Kind::TABLE_AGGREGATE:
    {
      if (rejectsInitialRow(n[0], A[1]))
      {
        // AGGREGATE_KEYED, under a filter that drops the row of initial
        // values (see rejectsInitialRow), see keyedAggregateRows:
        //   (bag.filter Q ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X))
        //   ---> (bag.filter Q (bag.map (lambda ((t T)) b[acc := i]) X))
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
        // AGGREGATE_KEYED, for the components of the product whose groups
        // the filter keeps reached ones of (see reachedComponents): the row
        // of initial values of such a component, there when its input is
        // empty, is in no row that passes. With G = ((_ table.aggr 0) f i X)
        // tested by P,
        //   (bag.filter P (table.product G Y))
        //   ---> (bag.filter P (table.product (bag.map (lambda ((t T))
        //                                                b[acc := i])
        //                                              X)
        //                                     Y))
        // see keyedAggregateRows
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
      // FILTER_IMPLIED_COUNTER, FILTER_JOIN_TRANSITIVE and
      // FILTER_EQUI_JOIN_SETS, see dropImpliedCounters,
      // rewriteJoinTransitiveConditions and rewriteEquiJoinOfSets
      BagsRewriteResponse r = dropImpliedCounters(n);
      if (r.d_node != n)
      {
        return r;
      }
      r = rewriteJoinTransitiveConditions(n);
      if (r.d_node != n)
      {
        return r;
      }
      return rewriteEquiJoinOfSets(n);
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
      Node c2 = d_rewriter->rewrite(c.substitute(
          TNode(datatypes::TupleUtils::nthElementOfTuple(u, k)),
          TNode(datatypes::TupleUtils::nthElementOfTuple(r, first))));
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
  // for a filter P over the product of comps: per component, the conjunct of
  // P that tests its counter positive (-1 when none), in test; and whether
  // its groups are reached: 1 when tested, 2 when joined on all its keys with
  // a reached aggregate whose input has the same key values, 0 otherwise.
  // With G1 = ((_ table.aggr 0) f i X) and G2 = ((_ table.aggr 0) g j X),
  // each copying its group column 0 and with its counter in column 2,
  //   P = (lambda ((t V)) (and (>= ((_ tuple.select 2) t) 1)
  //                            (= ((_ tuple.select 0) t)
  //                               ((_ tuple.select 3) t))))
  // over (table.product G1 G2) gives test = {0, -1} and reached = {1, 2}:
  // G1's counter is tested, and every group of G2 that a reached group of
  // G1 meets has a row of X, the same key values as that group
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
    // a conjunct (>= ((_ tuple.select pos) t) 1) of P tests the counter when
    // (lambda ((row U)) (>= ((_ tuple.select pos-start) row) 1)) does, for
    // the component alone
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
  // the key values of a component's input as a set, rewritten,
  //   (bag.setof (bag.map (lambda ((s T)) (tuple ((_ tuple.select 0) s))) X))
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
        if (joined && keySet(i) == keySet(j))
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
  // copy all their group columns, joined on them, over inputs with the same
  // key values (see reachedComponents): the group of the second that a
  // reached group of the first meets is reached too, and the test of its
  // counter goes. With G1 = ((_ table.aggr 0) f i X) and
  // G2 = ((_ table.aggr 0) g j X), counters in their columns 2,
  //   (bag.filter (lambda ((t V)) (and (>= ((_ tuple.select 2) t) 1)
  //                                    (>= ((_ tuple.select 5) t) 1)
  //                                    (= ((_ tuple.select 0) t)
  //                                       ((_ tuple.select 3) t))))
  //               (table.product G1 G2))
  //   --->
  //   (bag.filter (lambda ((t V)) (and (>= ((_ tuple.select 2) t) 1)
  //                                    (= ((_ tuple.select 0) t)
  //                                       ((_ tuple.select 3) t))))
  //               (table.product G1 G2))
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
  // FILTER_EQUI_JOIN_SETS: a join of two sets X and Y of rows of one sort T,
  // on all their columns, pairs each row of X with the one equal row of Y,
  // if any: the rows of the intersection, twice. With T of two columns,
  //   (bag.filter (lambda ((t V)) (and (= ((_ tuple.select 0) t)
  //                                       ((_ tuple.select 2) t))
  //                                    (= ((_ tuple.select 1) t)
  //                                       ((_ tuple.select 3) t))
  //                                    q))
  //               (table.product X Y))
  //   --->
  //   (bag.filter (lambda ((t V)) q)
  //               (bag.map (lambda ((w T)) (tuple ((_ tuple.select 0) w)
  //                                               ((_ tuple.select 1) w)
  //                                               ((_ tuple.select 0) w)
  //                                               ((_ tuple.select 1) w)))
  //                        (bag.inter_min X Y)))
  // the shape of SQL's INTERSECT, which the translator writes as
  // bag.inter_min; X and Y are sets, see isSet
  Node P = asLambda(n[0]);
  Node X = n[1][0];
  Node Y = n[1][1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || X.getType() != Y.getType()
      || !X.getType().getBagElementType().isTuple() || !isSet(X) || !isSet(Y))
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
  // dup is (lambda ((w T)) (tuple ((_ tuple.select 0) w) ((_ tuple.select 1)
  // w) ((_ tuple.select 0) w) ((_ tuple.select 1) w)))
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
  {
    Node l = asLambda(f);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2)
    {
      if (l[1] == l[0][1])
      {
        // FOLD_IDENTITY_STEP: a step that keeps the accumulator,
        //   (bag.fold (lambda ((t T) (acc S)) acc) i X) ---> i
        return BagsRewriteResponse(t, Rewrite::FOLD_IDENTITY_STEP);
      }
      if (bag.getKind() == Kind::BAG_FILTER
          && bag[1].getKind() == Kind::TABLE_PRODUCT
          && !l[1].getType().isTuple())
      {
        // FOLD_OVER_JOIN: a fold over a join, as the fold of the one-column
        // aggregate of eagerAggregation over the join of the pre-aggregated
        // sides:
        //   (bag.fold f i (bag.filter P (table.product X Y)))
        //   --->
        //   (bag.fold f' i J')
        // where (f1, i1) is f as a one-column tuple fold,
        //   f1 = (lambda ((t V) (acc (Tuple S))) (tuple b[acc := a0]))
        //   i1 = (tuple i)
        // with a0 = ((_ tuple.select 0) acc), eagerAggregation gives
        // (f3, i3, J') for it, and f' is f3 back on S
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
          // f3 = (lambda ((s W) (acc3 (Tuple S))) (tuple b3)), and the step
          // of f' is b3 with ((_ tuple.select 0) acc3) := a3
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
        // does not read the accumulator is 0 over no row, and otherwise the
        // sum that skips nulls from null: one fold S then stands for both
        // SUM (from null) and COALESCE(SUM, 0) (from 0),
        //   (bag.fold (lambda ((t T) (acc (Nullable Int)))
        //               (nullable.some (+ (nullable.val acc) e)))
        //             (nullable.some 0)
        //             X)
        //   --->
        //   (ite (= (as nullable.null (Nullable Int)) S) (nullable.some 0) S)
        // where
        //   S = (bag.fold (lambda ((t T) (acc (Nullable Int)))
        //                   (ite (= (as nullable.null (Nullable Int)) acc)
        //                        (nullable.some e)
        //                        (nullable.some (+ (nullable.val acc) e))))
        //                 (as nullable.null (Nullable Int))
        //                 X)
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
                           null.eqNode(a),
                           some,
                           d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                        dt[si].getConstructor(),
                                        d_nm->mkNode(Kind::ADD, val, e)));
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
                           null.eqNode(a),
                           b,
                           d_nm->mkNode(Kind::ITE, null.eqNode(b), a, both));
          return BagsRewriteResponse(ret, Rewrite::FOLD_UNION_COMBINE);
        }
      }
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
    // accumulator gives c after any row,
    //   (bag.fold (lambda ((t T) (acc S)) c) i X)
    //   ---> (ite (= X (as bag.empty (Bag T))) i c)
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
  if (bag.isConst())
  {
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  Kind k = bag.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      if (bag[1].isConst() && bag[1].getConst<Rational>() > Rational(0))
      {
        // (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, n > 0
        Node value = BagsUtils::evaluateBagFold(n);
        return BagsRewriteResponse(value, Rewrite::FOLD_BAG);
      }
      break;
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.fold f t (bag.union_disjoint A B)) =
      //       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
      Node A = bag[0] < bag[1] ? bag[0] : bag[1];
      Node B = bag[0] < bag[1] ? bag[1] : bag[0];
      Node foldA = d_nm->mkNode(Kind::BAG_FOLD, f, t, A);
      Node fold = d_nm->mkNode(Kind::BAG_FOLD, f, foldA, B);
      return BagsRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
    }
    default: return BagsRewriteResponse(n, Rewrite::NONE);
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
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || init.getKind() != Kind::APPLY_CONSTRUCTOR
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
  // AGGREGATE_UNION_SPLIT:
  //   (bag.map h (bag.filter Q ((_ table.aggr K) f i
  //                               (bag.union_disjoint U1 .. Um))))
  // where every column of f other than the copies of the group columns and
  // the counter folds an argument column, skipping its nulls, that is null
  // on every row of all parts but one, and every part has the same group
  // keys: each group folds each column over one part's rows, so the rows
  // are those of the aggregates of the parts, one per part, joined on the
  // keys. Q reads the counter only through (>= c 1) and h not at all: with
  // the same keys in every part, the first part's counter is positive
  // exactly when theirs are, and stands for it. This is SQL's
  //   SELECT k, SUM(a), SUM(b) FROM (SELECT k, a, NULL AS b FROM X
  //     UNION ALL SELECT k, NULL, b FROM Y) GROUP BY k
  // with the rows of f (tuple k sum-of-a sum-of-b counter), and
  //   U1 = (bag.map (lambda ((s T)) (tuple ((_ tuple.select 0) s)
  //                                        ((_ tuple.select 1) s)
  //                                        (as nullable.null (Nullable Int))))
  //                 X)
  // and U2 the same with the null in column 1:
  //   --->
  //   (bag.map h
  //     (bag.filter Q
  //       (bag.map (lambda ((p W)) (tuple ((_ tuple.select 0) p)
  //                                       ((_ tuple.select 1) p)
  //                                       ((_ tuple.select 4) p)
  //                                       ((_ tuple.select 2) p)))
  //                (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
  //                                               ((_ tuple.select 3) p)))
  //                            (table.product ((_ table.aggr 0) f1 i1 U1)
  //                                           ((_ table.aggr 0) f2 i2 U2))))))
  // where the rows of f1 are (tuple k sum-of-a counter), and those of f2
  // (tuple k sum-of-b counter)
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
      || f[0].getNumChildren() != 2 || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || init.getKind() != Kind::APPLY_CONSTRUCTOR || d_rewriter == nullptr)
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
    if (!g.isNull() && g.getKind() == Kind::LAMBDA
        && g[1].getKind() == Kind::APPLY_CONSTRUCTOR)
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
  // the parts own columns, and have the same keys: the sets
  //   (bag.setof (bag.map (lambda ((u T)) (tuple ((_ tuple.select 0) u))) Um))
  // of the parts are one term after rewriting
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
      // the parts' values combined, skipping nulls, as FOLD_UNION_COMBINE
      // combines two folds
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
          case 3: both = some(d_nm->mkNode(Kind::ADD, val(c), val(v))); break;
          case 1:
            both = d_nm->mkNode(
                Kind::ITE, d_nm->mkNode(Kind::LEQ, val(c), val(v)), c, v);
            break;
          default:
            both = d_nm->mkNode(
                Kind::ITE, d_nm->mkNode(Kind::GEQ, val(c), val(v)), c, v);
            break;
        }
        c = kind[q] == 3
                ? both
                : d_nm->mkNode(
                      Kind::ITE,
                      null.eqNode(c),
                      v,
                      d_nm->mkNode(Kind::ITE, null.eqNode(v), c, both));
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
  // F = (bag.filter (lambda ((r V)) (>= ((_ tuple.select c) r) 1))
  //                 ((_ table.aggr K) f i X))
  // with c the counter (see counterColumn), and h reading only columns where
  // f copies a group column ((_ tuple.select k) t): the rows h makes of the
  // groups are those it makes of the rows of X, without repeats,
  //   (bag.map h' X)
  // to put under a bag.setof, null otherwise; h' is h with column p of r read
  // as ((_ tuple.select k) s) of the rows s of X. With covering, h must read
  // all of K, so that distinct groups give distinct rows. With f copying
  // column 0 of X to its column 0,
  //   h = (lambda ((r V)) (tuple ((_ tuple.select 0) r)))
  //   h' = (lambda ((s T)) (tuple ((_ tuple.select 0) s)))
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
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || counterColumn(F[0], f, A[1]) < 0)
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
            if (e != d && !occursFree(e, w)
                && d_rewriter->rewrite(e) == d_nm->mkConst(false))
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
        if (!occursFree(v, w) && d_rewriter->rewrite(v) == d_nm->mkConst(false))
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
  // Eager aggregation, the SQL rewrite that pushes an aggregate through a
  // join. f folds the rows of J = (bag.filter P (table.product X Y)),
  // grouped by the columns K of J's rows (none for a fold), with P equating
  // columns of X with columns of Y besides conditions on X alone and on Y
  // alone, and every column of f a key copy, the counter, or a sum, minimum,
  // maximum or count over a column of one side: the groups of the join are
  // made of the groups of X and of Y by their join and key columns, X's sum
  // over a pair of groups is X's sum times Y's rows, a minimum is X's
  // minimum, a count X's count times Y's rows. Returns
  //   (SEXPR f3 J' (SEXPR k0 ..))
  // where f3 folds J', the join of those two aggregates, the same way (from
  // the same initial value), and k0 .. are the columns of J' rows that hold
  // the group columns K; null when J is not of that shape. For SQL's
  //   SELECT x.k, SUM(y.b) FROM X x JOIN Y y ON x.a = y.a GROUP BY x.k
  // with X rows (tuple k a) and Y rows (tuple a b),
  //   J = (bag.filter (lambda ((t V)) (= ((_ tuple.select 1) t)
  //                                      ((_ tuple.select 2) t)))
  //                   (table.product X Y))
  // and f's rows (tuple k sum-of-b counter), K = {0}:
  //   AX = ((_ table.aggr 1 0) fx ix X), rows (tuple a k rows-x counter-x)
  //   AY = ((_ table.aggr 0) fy iy Y), rows (tuple a sum-of-b rows-y
  //                                              counter-y)
  //   J' = (bag.filter (lambda ((p W)) (and (= ((_ tuple.select 0) p)
  //                                            ((_ tuple.select 4) p))
  //                                         (>= ((_ tuple.select 3) p) 1)
  //                                         (>= ((_ tuple.select 7) p) 1)))
  //                    (table.product AX AY))
  //   f3 = (lambda ((p W) (acc S))
  //          (tuple ((_ tuple.select 1) p)
  //                 [the step of f's sum, with argument
  //                  (ite (= (as nullable.null (Nullable Int))
  //                          ((_ tuple.select 5) p))
  //                       (as nullable.null (Nullable Int))
  //                       (nullable.some
  //                         (* (nullable.val ((_ tuple.select 5) p))
  //                            (nullable.val ((_ tuple.select 2) p)))))]
  //                 (+ ((_ tuple.select 2) acc)
  //                    (* ((_ tuple.select 3) p) ((_ tuple.select 7) p)))))
  // and the group columns (SEXPR 1), where AX has k. rows-x and rows-y are
  // COUNT(*) columns, (nullable.some 0) plus one per row.
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
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(bv, g[k]));
      const DType& dt = btypes[g[k]].getDType();
      seeds.push_back(
          d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                       dt[dt[0].getNumArgs() == 0 ? 0 : 1].getConstructor()));
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
  Node pairs = d_nm->mkNode(Kind::MULT, rowsOf(false), rowsOf(true));
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
                         null.eqNode(v),
                         null,
                         d_nm->mkNode(Kind::APPLY_CONSTRUCTOR,
                                      dt[si].getConstructor(),
                                      d_nm->mkNode(Kind::MULT, val, times)));
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
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || n[1].getKind() != Kind::APPLY_CONSTRUCTOR || K.empty())
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
  // PRODUCT_AGGREGATE_DEAD_COLUMN: in
  //   (bag.map h (bag.filter P (table.product C0 C1 ..)))
  // or the same without the filter, a column of a component aggregate that
  // neither h nor P reads, nor another step of its aggregate, goes (for an
  // aggregate alone, AGGREGATE_DEAD_COLUMNS does it). With
  //   G = ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
  //                         (tuple i0 i1 i2) X)
  // and nothing reading column 1 of G's rows (column 1 of the product),
  //   (bag.map h (table.product G Y))
  //   --->
  //   (bag.map h' (table.product ((_ table.aggr 0)
  //                                (lambda ((t T) (acc S')) (tuple a0' a2'))
  //                                (tuple i0 i2)
  //                                X)
  //                              Y))
  // where h' reads column k of the product as column k - 1 for k > 1, and
  // a0', a2' are a0, a2 over the narrower accumulator; the columns removed
  // can only merge rows that h maps to one image anyway
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
        || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
        || A[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
  // AGGREGATE_DUPLICATE_COLUMN: columns p < q of f fold alike, the same step
  // of their own accumulator from the same seed, as for SELECT SUM(a),
  // SUM(a): one fold, read twice,
  //   ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 s1 s2))
  //                     (tuple i0 i1 i1) X)
  //   --->
  //   (bag.map (lambda ((r U)) (tuple ((_ tuple.select 0) r)
  //                                   ((_ tuple.select 1) r)
  //                                   ((_ tuple.select 1) r)))
  //            ((_ table.aggr 0) (lambda ((t T) (acc U)) (tuple a0 s1))
  //                              (tuple i0 i1) X))
  // where s2 is s1 with ((_ tuple.select 1) acc) read as
  // ((_ tuple.select 2) acc), and no other step reads column 2
  Node f = asLambda(n[0]);
  Node init = n[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || init.getKind() != Kind::APPLY_CONSTRUCTOR)
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
      if (init[p] != init[q] || f[1][p].getType() != f[1][q].getType()
          || f[1][q].substitute(TNode(oq), TNode(op)) != f[1][p])
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
    // NOT_NULL_COLUMNS: the null tests of columns the rows of X never have
    // null are decided in the steps of f, see assumeNonNull
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
    // AGGREGATE_FIXED_COLUMNS: the rows of every group pass the filter, they
    // have the constants it fixes (see fixedColumns, readFixed), and a group
    // column it fixes splits no group:
    //   ((_ table.aggr 0 1) (lambda ((t T) (acc S)) b)
    //                       i
    //                       (bag.filter (lambda ((s T))
    //                                     (= ((_ tuple.select 1) s) 5))
    //                                   X))
    //   --->
    //   ((_ table.aggr 0) (lambda ((t T) (acc S)) b[((_ tuple.select 1) t)
    //                                               := 5])
    //                     i
    //                     (bag.filter (lambda ((s T))
    //                                   (= ((_ tuple.select 1) s) 5))
    //                                 X))
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
    // AGGREGATE_NO_KEYS: grouping by no column makes one part, all of X, even
    // when X is empty (table.group of an empty table is one empty part):
    //   ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
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
    // PRODUCT_EMPTY:
    //   (table.product X (as bag.empty (Bag U))) ---> (as bag.empty (Bag V))
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
  // whether a closure in body binds var: true for body
  //   (>= (bag.count ((_ tuple.project 0) t)
  //                  (bag.map (lambda ((t T)) ((_ tuple.project 1) t)) X))
  //       1)
  // and var t, whose inner lambda binds t again
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
  // whether v occurs free in n: false for t in (lambda ((t T)) b), true in
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
  // a lambda whose body is a constant, or an ite over constants, is kept by
  // the rewriter as a function array constant: read it as the lambda it is,
  // e.g. (lambda ((t T)) true) for the constant of the filter that keeps
  // every row
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
  // (f x) beta-reduced: for f = (lambda ((s T)) (> ((_ tuple.select 1) s) 3))
  // and x = (tuple a b), (> ((_ tuple.select 1) (tuple a b)) 3), which the
  // rewriter simplifies to (> b 3); null when the substitution would capture
  // a variable; (f x) as an APPLY_UF when f is not a lambda
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
  // (t, b) for f = (lambda ((t T)) b); for a function f that is not a lambda,
  // (t, (f t)) with t the row variable of T
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
  // f is (lambda ((t T)) b), or a function array constant of one: the rules
  // that compose functions build lambdas of their bodies. A declared function
  // symbol f stays one, as upstream: (lambda ((t T)) (f t)) would be a lambda
  // around a function the model interprets, a lambda the input did not have
  Node l = asLambda(f);
  return l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 1;
}

Node BagsRewriter::mkLambda(const Node& var, const Node& body) const
{
  // (lambda ((var T)) body)
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
  // FILTER_MAP: a filter of a map is the map of a filter, by the predicate
  // of the image,
  //   (bag.filter (lambda ((s U)) p) (bag.map (lambda ((t T)) e) A))
  //   ---> (bag.map (lambda ((t T)) e) (bag.filter (lambda ((t T)) p[s := e])
  //                                                A))
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
  // MAP_MAP: two maps are one, by the composition,
  //   (bag.map (lambda ((s U)) e) (bag.map (lambda ((t T)) g) A))
  //   ---> (bag.map (lambda ((t T)) e[s := g]) A)
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
  // PROJECT_TO_MAP:
  //   ((_ table.project 1 0) X)
  //   ---> (bag.map (lambda ((t T)) ((_ tuple.project 1 0) t)) X)
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
  // f = (lambda ((t T)) (tuple ((_ tuple.select j0) t) ..
  // ((_ tuple.select jm) t))), or (lambda ((t T)) ((_ tuple.project j0 .. jm)
  // t)): the columns j0, .., jm; empty for any other f
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
  // AGGREGATE_MAP: the fold reads each row through g, and grouping by
  // column k of the mapped row is grouping by the column of X's row that g
  // copies there:
  //   ((_ table.aggr 0) (lambda ((s U) (acc S)) b) i
  //                     (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
  //                                                     ((_ tuple.select 0)
  //                                                      t)))
  //                              X))
  //   --->
  //   ((_ table.aggr 2) (lambda ((t T) (acc S))
  //                       b[s := (tuple ((_ tuple.select 2) t)
  //                                     ((_ tuple.select 0) t))])
  //                     i X)
  // g may compute its other columns any way: each group column of g's row
  // must be a column of X's row, a constant, which every row of a group
  // shares and so drops out of the grouping, or a term of group columns
  // only (deptno + 42 beside deptno), which splits no group the others do
  // not
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

bool BagsRewriter::rejectsInitialRow(const Node& P, const Node& i) const
{
  // whether P is false on the row of initial values i, the one row of the
  // aggregate of an empty table: (P i) rewrites to false. True for
  //   P = (lambda ((r V)) (>= ((_ tuple.select 2) r) 1))
  //   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
  // the test of a counter, which starts at 0
  if (d_rewriter == nullptr)
  {
    return false;
  }
  Node applied = applyFunction(P, i);
  return !applied.isNull()
         && d_rewriter->rewrite(applied) == d_nm->mkConst(false);
}

Node BagsRewriter::keyedAggregateRows(const Node& A) const
{
  // A = ((_ table.aggr K) f i X) whose group columns K contain a key of X
  // (see rowKeys): every group is one row of X, once, folded once from i, so
  // the groups some row reached give the rows
  //   (bag.map (lambda ((t T)) b[acc := i]) X)
  // for f = (lambda ((t T) (acc S)) b); null for any other A. Only the
  // reached groups: an empty X is one empty group, folded to the row of
  // initial values, (bag i 1), which the map does not have
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

BagsRewriteResponse BagsRewriter::rewriteFilterOfAggregate(const TNode& n) const
{
  // FILTER_AGGREGATE: a conjunct of p that reads only positions of the
  // result where f copies a group column of the row filters the groups by
  // their keys, which is filtering the rows of X by the same columns before
  // grouping: every group is kept or dropped whole. With f copying column 0
  // of X to column 0 of its rows and counting them in column 2,
  //   (bag.filter (lambda ((r V)) (and (> ((_ tuple.select 0) r) 3)
  //                                    (>= ((_ tuple.select 2) r) 1)))
  //               ((_ table.aggr 0) f i X))
  //   --->
  //   (bag.filter (lambda ((r V)) (>= ((_ tuple.select 2) r) 1))
  //               ((_ table.aggr 0) f i (bag.filter (lambda ((t T))
  //                                                   (> ((_ tuple.select 0)
  //                                                         t)
  //                                                      3))
  //                                                 X)))
  // The conjuncts that stay must reject the row of initial values i, as the
  // counter test does (see rejectsInitialRow): when no row of X passes the
  // moved conjuncts, the aggregate of the empty bag still has that row,
  // (bag i 1), which the moved conjuncts would have dropped
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

Node BagsRewriter::accumulatorVariable(TypeNode type) const
{
  // the second variable of an aggregate's function, one per accumulator type,
  // named accrow_N after the id N of the key (as bag.empty (Bag S)) of its
  // type S
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(type)));
  return mkRewriterVar(
      d_nm, "accumulator", key, "accrow_" + std::to_string(key.getId()), type);
}

Node BagsRewriter::alphaKey(const Node& f) const
{
  // f with every variable it binds, at any depth, replaced by a placeholder
  // for its binding depth, and every variable free in it by one placeholder
  // per type: equal for alpha-equivalent lambdas, and unchanged when a lambda
  // inside f or around f renames its variables. The keys of
  //   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
  //   (lambda ((t T)) (> ((_ tuple.select 0) t) 3))
  // are one node, (lambda ((b0 T)) (> ((_ tuple.select 0) b0) 3)) with b0
  // the placeholder for depth 0; a free variable r of an enclosing lambda
  // becomes the placeholder of its type, so
  //   (lambda ((t T)) (= ((_ tuple.select 0) t) ((_ tuple.select 0) r)))
  // has a key that does not depend on r's name either. Cached in
  // d_alphaKeys.
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
      cache[n] = b != bound.end() ? b->second
                                  : mkRewriterVar(d_nm,
                                                  "alpha-free",
                                                  d_nm->mkConstInt(Rational(0)),
                                                  n.getType());
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
      // (lambda ((s T) (acc S)) b) at depth d is
      // (lambda ((b_d T) (b_d+1 S)) key-of-b), the body converted in the
      // scope of the new placeholders
      todo.pop_back();
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> vars;
      std::vector<std::pair<TNode, Node>> saved;
      for (size_t i = 0; i < nvars; i++)
      {
        TNode v = n[0][i];
        Node p = mkRewriterVar(d_nm,
                               "alpha-bound",
                               d_nm->mkConstInt(Rational(depth + i)),
                               v.getType());
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
  // f with its variables named after f's alpha key: lambdas that differ only
  // in the names of their variables become one node, so the solver purifies
  // them into one function symbol. Two lambdas one inside the other have
  // different keys, so canonical names never shadow each other, and the key
  // does not change when a lambda inside or around f is renamed, so renaming
  // terminates. With K the alpha key of f and N its node id,
  //   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
  //   ---> (lambda ((t_N T)) (> ((_ tuple.select 0) t_N) 3))
  //   (lambda ((x T) (y S)) b) ---> (lambda ((t_N T) (acc_N S)) b')
  // and first (ite (= a b) b a) in the body is a, see simplifyIteSame
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
  // AGGREGATE_SORT_OUTPUT: ((_ table.aggr K) f i X) where f builds a tuple:
  // the positions that copy a key column of the row come first, sorted by
  // column, then the others, sorted by what they compute (the alpha key of
  // their step and their seed). Two aggregates that output the same columns
  // in different orders then differ only in the map above them:
  //   ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a1 ((_ tuple.select 0)
  //                                                      t)))
  //                     (tuple i1 i0) X)
  //   --->
  //   (bag.map (lambda ((r S')) (tuple ((_ tuple.select 1) r)
  //                                    ((_ tuple.select 0) r)))
  //            ((_ table.aggr 0) (lambda ((t T) (acc S'))
  //                                (tuple ((_ tuple.select 0) t) a1'))
  //                              (tuple i0 i1) X))
  // where a1' is a1 over the sorted accumulator, ((_ tuple.select 1) acc)
  // read as ((_ tuple.select 0) acc): the new fold computes the sorted rows
  // of the old one
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
                               d_nm->mkNode(Kind::BOUND_VAR_LIST, x, v),
                               c.substitute(TNode(own), TNode(v)));
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
  // FOLD_TUPLE: a fold of tuples whose component k reads the accumulator
  // only at position k is the tuple of the folds of the components,
  //   (bag.fold (lambda ((t T) (acc (Tuple Int Int))) (tuple b0 b1))
  //             (tuple i0 i1) X)
  //   --->
  //   (tuple (bag.fold (lambda ((t T) (a Int)) b0[((_ tuple.select 0) acc)
  //                                               := a])
  //                    i0 X)
  //          (bag.fold (lambda ((t T) (a Int)) b1[((_ tuple.select 1) acc)
  //                                               := a])
  //                    i1 X))
  // The folds over X read its elements in one order, so each component is
  // the fold of its own step.
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

BagsRewriteResponse BagsRewriter::rewriteProductOfBagMake(const TNode& n,
                                                          size_t side) const
{
  // PRODUCT_BAG_MAKE: a product with a single row e, present once or when
  // b holds, is a map of the other side that appends e, under the filter b
  // when there is one; b and e do not read the rows of A. With A of two
  // columns and e = (tuple 7),
  //   (table.product A (bag (tuple 7) (ite b 1 0)))
  //   --->
  //   (bag.filter (lambda ((r V)) b)
  //               (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
  //                                               ((_ tuple.select 1) t)
  //                                               7))
  //                        A))
  // the map is injective, and each row of A meets the one row e, once if b;
  // with side 0 the bag is the left factor and e comes first
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

BagsRewriteResponse BagsRewriter::rewriteMapSplitClosed(const TNode& n) const
{
  // MAP_SPLIT_CLOSED: a map whose body has a Boolean subterm c that asks
  // about a bag and reads no variable but the row, such as EXISTS (subquery)
  // or IN (subquery) as a column, splits on c:
  //   (bag.map (lambda ((t T)) b) X)
  //   --->
  //   (bag.union_disjoint (bag.map (lambda ((t T)) b[c := true])
  //                                (bag.filter (lambda ((t T)) c) X))
  //                       (bag.map (lambda ((t T)) b[c := false])
  //                                (bag.filter (lambda ((t T)) (not c)) X)))
  // so that the question becomes a filter, which the filter rules
  // decorrelate
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
  Node a = d_nm->mkNode(Kind::BAG_MAP,
                        mkLambda(t, yes),
                        d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, c), X));
  Node b =
      d_nm->mkNode(Kind::BAG_MAP,
                   mkLambda(t, no),
                   d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, c.notNode()), X));
  Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
  return BagsRewriteResponse(ret, Rewrite::MAP_SPLIT_CLOSED);
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
      return datatypes::utils::indexOf(keysS[a].getOperator())
             < datatypes::utils::indexOf(keysS[b].getOperator());
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
                          d_nm->mkNode(Kind::GEQ, x, d_one),
                          d_nm->mkNode(Kind::GEQ, y, d_one));
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
  // AGGREGATE_DEAD_COLUMNS: in (bag.map h (bag.filter P ((_ table.aggr K) f i
  // X))), or the same without the filter, where h and P read no column q of
  // the aggregate's rows, and f computes column q from the row and column q
  // of the accumulator only, which no other column reads: column q changes
  // nothing anything reads, and goes. Grouping is by K, columns of X, so no
  // output column decides a group. With column 1 read by nothing,
  //   (bag.map h ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
  //                                (tuple i0 i1 i2) X))
  //   --->
  //   (bag.map h' ((_ table.aggr 0) (lambda ((t T) (acc S')) (tuple a0 a2'))
  //                                 (tuple i0 i2) X))
  // where h' and a2' read column 2 as column 1
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
  // the columns a filter's predicate fixes to a constant: conjuncts
  // (= ((_ tuple.select k) t) c) with c a constant; for
  //   (lambda ((t T)) (and (= ((_ tuple.select 1) t) 5) (> ((_ tuple.select 0)
  //                                                        t)
  //                                                     3)))
  // the map {1 -> 5}
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
  if (!accIsNull || A.getType() != acc.getType() || !A.getType().isDatatype())
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
  // AGGREGATE_ROLLUP, an aggregate of an aggregate:
  //   (bag.map h (bag.filter Q ((_ table.aggr Ko) g j
  //                               (bag.filter P ((_ table.aggr K) f i X)))))
  // the outer aggregate grouping the inner groups by some of their group
  // columns, Ko. Every outer column is a group column, the outer counter
  // (read by Q through (>= c 1) only, and not by h), a merge of an inner
  // aggregate (a sum of sums or counts, a minimum of minimums, a maximum of
  // maximums), or an aggregate over an inner group column c outside Ko when
  // K is Ko and c: over the inner groups of a key, c takes each of its values
  // once, so that is the aggregate over the distinct values of c. So the
  // outer rows are those of an aggregate over X by Ko of the merged columns,
  // joined on the keys with an aggregate by Ko over the distinct (Ko, c) of
  // X of the others. That is how Calcite writes a query with DISTINCT and
  // plain aggregates; for
  //   SELECT k, SUM(a), COUNT(DISTINCT c) FROM X GROUP BY k
  // as SELECT k, SUM(s), COUNT(c) FROM (SELECT k, c, SUM(a) AS s FROM X
  // GROUP BY k, c) GROUP BY k,
  //   --->
  //   (bag.map h (bag.filter Q (bag.map rows
  //     (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
  //                                    ((_ tuple.select 3) p)))
  //       (table.product
  //         (bag.filter (lambda ((r U)) (>= ((_ tuple.select 2) r) 1))
  //                     ((_ table.aggr 0) fA iA X))
  //         (bag.filter (lambda ((r U')) (>= ((_ tuple.select 2) r) 1))
  //                     ((_ table.aggr 0) fB iB
  //                                       (bag.setof (bag.map (lambda ((t T))
  //                                         (tuple ((_ tuple.select 0) t)
  //                                                ((_ tuple.select 2) t)))
  //                                         X)))))))))
  // where fA sums a over X by k (tuple k sum-of-a counter), fB counts the
  // distinct c by k (tuple k count-of-c counter), and rows puts the columns
  // in the outer aggregate's order, with 1 for its counter
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
      || g[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || j.getKind() != Kind::APPLY_CONSTRUCTOR
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
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR
      || i0.getKind() != Kind::APPLY_CONSTRUCTOR)
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
  // the outer keys, as columns of X
  std::vector<uint32_t> Cp;
  for (uint32_t p : Ko)
  {
    if (p >= wI || keyCol[p] < 0)
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Cp.push_back(static_cast<uint32_t>(keyCol[p]));
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
  // the first part: the merged columns over X, by Ko, with a counter,
  //   (bag.filter (lambda ((r U)) (>= ((_ tuple.select c) r) 1))
  //               ((_ table.aggr Ko) fA iA X))
  // or, when nothing is merged, the distinct keys,
  //   (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select k) t)))
  //                       X))
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
    for (uint32_t c : Cp)
    {
      cells.push_back(datatypes::TupleUtils::nthElementOfTuple(x, c));
      seeds.push_back(d_nm->mkNode(
          Kind::APPLY_CONSTRUCTOR,
          xTypes[c]
              .getDType()[xTypes[c].getDType()[0].getNumArgs() == 0 ? 0 : 1]
              .getConstructor()));
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
  // the second part: the aggregates over the distinct (Ko, c),
  //   (bag.filter (lambda ((r U')) (>= ((_ tuple.select c') r) 1))
  //               ((_ table.aggr 0 .. nk-1) fB iB S))
  // with S = (bag.setof (bag.map (lambda ((t T)) (tuple k.. c)) X)),
  // joined with the first on the keys
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
      seeds.push_back(d_nm->mkNode(
          Kind::APPLY_CONSTRUCTOR,
          stypes[k]
              .getDType()[stypes[k].getDType()[0].getNumArgs() == 0 ? 0 : 1]
              .getConstructor()));
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
  // components that are aggregates:
  // * AGGREGATE_SETOF_IDEMPOTENT: an aggregate over (bag.setof Y) whose
  //   columns are copies of the row's columns, minimums, maximums and a
  //   counter that h does not read and P reads only through (>= c 1) is the
  //   aggregate over Y: duplicate rows change none of those,
  //     ((_ table.aggr 0) f i (bag.setof Y)) ---> ((_ table.aggr 0) f i Y)
  //   as a component;
  // * AGGREGATE_JOIN_MERGE: two aggregates over one X by the same columns K,
  //   both copying every group column, seeding the copies alike, with P
  //   equating their copies, pair the rows of each group: they are one
  //   aggregate computing the columns of both, the second's copies and
  //   counter read from the first's,
  //     (bag.map h (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
  //                                               ((_ tuple.select 3) p)))
  //                            (table.product ((_ table.aggr 0) fa ia X)
  //                                           ((_ table.aggr 0) fb ib X))))
  //     --->
  //     (bag.map h' ((_ table.aggr 0) fm im X))
  //   for rows (tuple k a cnt) of fa and (tuple k b cnt) of fb, where fm's
  //   rows are (tuple k a cnt b) and h' reads B's columns 0, 1, 2 as columns
  //   0, 3, 2 of those. SQL's self-join of two GROUP BY queries over one
  //   table, which Calcite merges into one aggregate.
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
        || f[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
          || B.getKind() != Kind::TABLE_AGGREGATE || A[2] != B[2]
          || A.getOperator() != B.getOperator())
      {
        continue;
      }
      Node fa = asLambda(A[0]);
      Node fb = asLambda(B[0]);
      if (fa.getKind() != Kind::LAMBDA || fb.getKind() != Kind::LAMBDA
          || fa[1].getKind() != Kind::APPLY_CONSTRUCTOR
          || fb[1].getKind() != Kind::APPLY_CONSTRUCTOR
          || A[1].getKind() != Kind::APPLY_CONSTRUCTOR
          || B[1].getKind() != Kind::APPLY_CONSTRUCTOR)
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
          mkLambda(r2, hBody),
          d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r2, pBody), rebuild(cs)));
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_JOIN_MERGE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteAggregateCollapse(const TNode& n) const
{
  // AGGREGATE_COLLAPSE: an aggregate over a union of aggregates, the
  // pattern of an aggregate pushed through a UNION ALL:
  //   (bag.map h (bag.filter Q ((_ table.aggr Ko) g j
  //                               (bag.union_disjoint P1 P2))))
  // where every Pi is (bag.map pi (bag.filter Qi ((_ table.aggr K) f i0 Xi)))
  // with one pi, Qi, K, f and i0, the inner aggregates grouped by exactly the
  // outer group columns, and g merging f's columns (a sum of counts or of
  // sums, a minimum of minimums, a maximum of maximums): a group of the
  // outer aggregate has one row per part its key reached, each part's fold
  // over the key's rows of Xi, so their merge is f's fold over the key's
  // rows of all the Xi:
  //   --->
  //   (bag.map (lambda ((r U)) h[(g r j)]) (bag.filter Q'
  //     ((_ table.aggr K) f i0 (bag.union_disjoint X1 X2))))
  // with (g r j) the outer row that the outer step from j gives on the
  // inner row r, through pi, and Q' the test of the inner counter with Q's
  // other conjuncts on that row. Q and h must read the outer counter only
  // through (>= c 1): its value, the number of parts, is no column here.
  // SQL: SELECT k, SUM(c) FROM (SELECT k, COUNT(*) AS c FROM X1 GROUP BY k
  // UNION ALL SELECT k, COUNT(*) FROM X2 GROUP BY k) GROUP BY k is
  // SELECT k, COUNT(*) FROM (X1 UNION ALL X2) GROUP BY k.
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
  std::vector<Node> inputs;
  for (const Node& p : parts)
  {
    Node pPi = p.getKind() == Kind::BAG_MAP ? p[0] : Node::null();
    Node q = belowMap(p);
    if (pPi != pi || q.getKind() != Kind::BAG_FILTER || q[0] != Qi
        || q[1].getKind() != Kind::TABLE_AGGREGATE
        || q[1].getOperator() != innerAggr.getOperator() || q[1][0] != f
        || q[1][1] != i0)
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

BagsRewriteResponse BagsRewriter::rewriteSetofPushdown(const TNode& n) const
{
  // SETOF_PUSHDOWN: under duplicate removal only membership counts, so each
  // component of a product may be replaced by the set of the columns that g
  // and the rest of p read of it, after the conjuncts of p that read that
  // component alone:
  //   (bag.setof (bag.map g (bag.filter p (table.product C1 C2))))
  //   --->
  //   (bag.setof (bag.map g' (bag.filter p' (table.product
  //     (bag.setof (bag.map pi1 (bag.filter p1 C1)))
  //     (bag.setof (bag.map pi2 (bag.filter p2 C2)))))))
  // where pi1 projects C1 onto the columns read, p1 is the conjuncts of p on
  // C1 alone, and g' and p' read the projected columns. With C1 of two
  // columns of which only column 0 is read,
  //   pi1 = (lambda ((v T)) (tuple ((_ tuple.select 0) v)))
  // A component that is a set whose rows those columns tell apart (all of
  // them, or a key) stays, with its conjuncts above. SQL's SELECT DISTINCT
  // over a join, which Calcite may write with the DISTINCT pushed into a side.
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
  // FILTER_INTO_SETOF: a conjunct c of the filter that reads only a
  // component that is a set moves into it, where the rule that lifts filters
  // out of products does not reach it:
  //   (bag.filter (lambda ((t V)) (and c q))
  //               (table.product X (bag.setof Z)))
  //   --->
  //   (bag.filter (lambda ((t V)) q)
  //               (table.product X (bag.setof (bag.filter (lambda ((v U)) c')
  //                                                       Z))))
  // with c' the conjunct over the component's own rows, column w + k of t
  // read as column k of v, for X of w columns
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
  // AGGREGATE_SEMI_JOIN, SEMI_JOIN under an aggregate: B is a set whose row
  // the equations of p fix (all its columns, or a key), and f and K read of B
  // only columns that p equates to columns of the other components: read
  // those instead, and the product is a semi-join,
  //   ((_ table.aggr K) f i (bag.filter p (table.product A B)))
  //   --->
  //   ((_ table.aggr K') f' i
  //     (bag.filter (lambda ((a U))
  //                   (and pA
  //                        (not (= (bag.filter (lambda ((b W)) pAB) B)
  //                                (as bag.empty (Bag W))))))
  //                 A))
  // with pA the conjuncts that read no column of B and pAB the others, see
  // rewriteSemiJoin; K' and f' read the columns of A
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
  // SEMI_TO_INTERSECTION:
  //   (bag.map g (bag.filter (lambda ((x T)) (and (>= (bag.count (pi x) M) 1)
  //                                               q r))
  //                          X))
  // with pi a projection, (pi x) = (tuple ((_ tuple.select 0) x)
  // ((_ tuple.select 1) x)), g a projection of pi's columns (g is h applied
  // to the result of pi), q
  // reading only pi's columns and r the others: the projected rows of the
  // r-filtered X that are in M and pass q. Under duplicate removal
  // (underSetof), or when those projected rows are a set, that is
  //   (bag.map h (bag.inter_min
  //                (bag.setof (bag.filter q' (bag.map pi (bag.filter r X))))
  //                (bag.setof (bag.filter q' M))))
  // with q' the conjuncts q over the rows w of M, which reads the same
  // whichever side the join was written from: SQL's
  //   SELECT a, b FROM X WHERE (a, b) IN (SELECT .. FROM ..)
  // and the join of X with that subquery. Null when n is not of that shape.
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
    if (E.getKind() != Kind::APPLY_CONSTRUCTOR)
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
                            d_nm->mkNode(Kind::BAG_SETOF, left),
                            d_nm->mkNode(Kind::BAG_SETOF, right));
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

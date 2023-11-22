/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Nullables theory rewriter.
 */

#include "theory/nullables/nullables_rewriter.h"

#include "expr/emptynullable.h"
#include "theory/nullables/nullables_utils.h"
#include "theory/rewriter.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullablesRewriteResponse::NullablesRewriteResponse()
    : d_node(Node::null()), d_rewrite(Rewrite::NONE)
{
}

NullablesRewriteResponse::NullablesRewriteResponse(Node n, Rewrite rewrite)
    : d_node(n), d_rewrite(rewrite)
{
}

NullablesRewriteResponse::NullablesRewriteResponse(const NullablesRewriteResponse& r)
    : d_node(r.d_node), d_rewrite(r.d_rewrite)
{
}

NullablesRewriter::NullablesRewriter(Rewriter* r, HistogramStat<Rewrite>* statistics)
    : d_rewriter(r), d_statistics(statistics)
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

RewriteResponse NullablesRewriter::postRewrite(TNode n)
{
  NullablesRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = NullablesRewriteResponse(n, Rewrite::NONE);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    response = postRewriteEqual(n);
  }
  else if (n.getKind() == Kind::NULLABLE_CHOOSE)
  {
    response = rewriteChoose(n);
  }
  else if (NullablesUtils::areChildrenConstants(n))
  {
    Node value = NullablesUtils::evaluate(d_rewriter, n);
    response = NullablesRewriteResponse(value, Rewrite::CONSTANT_EVALUATION);
  }
  else
  {
    Kind k = n.getKind();
    switch (k)
    {
      case Kind::NULLABLE_MAKE: response = rewriteMakeNullable(n); break;
      case Kind::NULLABLE_COUNT: response = rewriteNullableCount(n); break;
      case Kind::NULLABLE_DUPLICATE_REMOVAL:
        response = rewriteDuplicateRemoval(n);
        break;
      case Kind::NULLABLE_UNION_MAX: response = rewriteUnionMax(n); break;
      case Kind::NULLABLE_UNION_DISJOINT: response = rewriteUnionDisjoint(n); break;
      case Kind::NULLABLE_INTER_MIN: response = rewriteIntersectionMin(n); break;
      case Kind::NULLABLE_DIFFERENCE_SUBTRACT:
        response = rewriteDifferenceSubtract(n);
        break;
      case Kind::NULLABLE_DIFFERENCE_REMOVE:
        response = rewriteDifferenceRemove(n);
        break;
      case Kind::NULLABLE_CARD: response = rewriteCard(n); break;
      case Kind::NULLABLE_IS_SINGLETON: response = rewriteIsSingleton(n); break;
      case Kind::NULLABLE_FROM_SET: response = rewriteFromSet(n); break;
      case Kind::NULLABLE_TO_SET: response = rewriteToSet(n); break;
      case Kind::NULLABLE_MAP: response = postRewriteMap(n); break;
      case Kind::NULLABLE_FILTER: response = postRewriteFilter(n); break;
      case Kind::NULLABLE_FOLD: response = postRewriteFold(n); break;
      case Kind::NULLABLE_PARTITION: response = postRewritePartition(n); break;
      case Kind::TABLE_PRODUCT: response = postRewriteProduct(n); break;
      case Kind::TABLE_AGGREGATE: response = postRewriteAggregate(n); break;
      default: response = NullablesRewriteResponse(n, Rewrite::NONE); break;
    }
  }

  Trace("nullables-rewrite") << "postRewrite " << n << " to " << response.d_node
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

RewriteResponse NullablesRewriter::preRewrite(TNode n)
{
  NullablesRewriteResponse response;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::EQUAL: response = preRewriteEqual(n); break;
    case Kind::NULLABLE_SUBNULLABLE: response = rewriteSubNullable(n); break;
    case Kind::NULLABLE_MEMBER: response = rewriteMember(n); break;
    default: response = NullablesRewriteResponse(n, Rewrite::NONE);
  }

  Trace("nullables-rewrite") << "preRewrite " << n << " to " << response.d_node
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

NullablesRewriteResponse NullablesRewriter::preRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a nullable
    return NullablesRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteSubNullable(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_SUBNULLABLE);

  // (nullable.subnullable A B) = ((nullable.difference_subtract A B) == nullable.empty)
  Node emptynullable = d_nm->mkConst(EmptyNullable(n[0].getType()));
  Node subtract = d_nm->mkNode(Kind::NULLABLE_DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptynullable);
  return NullablesRewriteResponse(equal, Rewrite::SUB_NULLABLE);
}

NullablesRewriteResponse NullablesRewriter::rewriteMember(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_MEMBER);

  // - (nullable.member x A) = (>= (nullable.count x A) 1)
  Node count = d_nm->mkNode(Kind::NULLABLE_COUNT, n[0], n[1]);
  Node geq = d_nm->mkNode(Kind::GEQ, count, d_one);
  return NullablesRewriteResponse(geq, Rewrite::MEMBER);
}

NullablesRewriteResponse NullablesRewriter::rewriteMakeNullable(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_MAKE);
  // return nullable.empty for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (nullable x c) = nullable.empty where c <= 0
    Node emptynullable = d_nm->mkConst(EmptyNullable(n.getType()));
    return NullablesRewriteResponse(emptynullable, Rewrite::NULLABLE_MAKE_COUNT_NEGATIVE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteNullableCount(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_COUNT);
  if (n[1].isConst() && n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.count x nullable.empty) = 0
    return NullablesRewriteResponse(d_zero, Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == Kind::NULLABLE_MAKE && n[0] == n[1][0] && n[1][1].isConst()
      && n[1][1].getConst<Rational>() > Rational(0))
  {
    // (nullable.count x (nullable x c)) = c, c > 0 is a constant
    Node c = n[1][1];
    return NullablesRewriteResponse(c, Rewrite::COUNT_NULLABLE_MAKE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteDuplicateRemoval(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_DUPLICATE_REMOVAL);
  if (n[0].getKind() == Kind::NULLABLE_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // (nullable.duplicate_removal (nullable x n)) = (nullable x 1)
    //  where n is a positive constant
    Node nullable = d_nm->mkNode(Kind::NULLABLE_MAKE, n[0][0], d_one);
    return NullablesRewriteResponse(nullable, Rewrite::DUPLICATE_REMOVAL_NULLABLE_MAKE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_UNION_MAX);
  if (n[1].getKind() == Kind::NULLABLE_EMPTY || n[0] == n[1])
  {
    // (nullable.union_max A A) = A
    // (nullable.union_max A nullable.empty) = A
    return NullablesRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.union_max nullable.empty A) = A
    return NullablesRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == Kind::NULLABLE_UNION_MAX
       || n[1].getKind() == Kind::NULLABLE_UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (nullable.union_max A (nullable.union_max A B)) = (nullable.union_max A B)
    // (nullable.union_max A (nullable.union_max B A)) = (nullable.union_max B A)
    // (nullable.union_max A (nullable.union_disjoint A B)) = (nullable.union_disjoint A B)
    // (nullable.union_max A (nullable.union_disjoint B A)) = (nullable.union_disjoint B A)
    return NullablesRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == Kind::NULLABLE_UNION_MAX
       || n[0].getKind() == Kind::NULLABLE_UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (nullable.union_max (nullable.union_max A B) A)) = (nullable.union_max A B)
    // (nullable.union_max (nullable.union_max B A) A)) = (nullable.union_max B A)
    // (nullable.union_max (nullable.union_disjoint A B) A)) = (nullable.union_disjoint A B)
    // (nullable.union_max (nullable.union_disjoint B A) A)) = (nullable.union_disjoint B A)
    return NullablesRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_UNION_DISJOINT);
  if (n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.union_disjoint A nullable.empty) = A
    return NullablesRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.union_disjoint nullable.empty A) = A
    return NullablesRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == Kind::NULLABLE_UNION_MAX
       && n[1].getKind() == Kind::NULLABLE_INTER_MIN)
      || (n[1].getKind() == Kind::NULLABLE_UNION_MAX
          && n[0].getKind() == Kind::NULLABLE_INTER_MIN))

  {
    // (nullable.union_disjoint (nullable.union_max A B) (nullable.inter_min A B)) =
    //         (nullable.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    // check if the operands of nullable.union_max and nullable.inter_min are the
    // same
    std::set<Node> left(n[0].begin(), n[0].end());
    std::set<Node> right(n[1].begin(), n[1].end());
    if (left == right)
    {
      Node rewritten = d_nm->mkNode(Kind::NULLABLE_UNION_DISJOINT, n[0][0], n[0][1]);
      return NullablesRewriteResponse(rewritten, Rewrite::UNION_DISJOINT_MAX_MIN);
    }
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_INTER_MIN);
  if (n[0].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.inter_min nullable.empty A) = nullable.empty
    return NullablesRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.inter_min A nullable.empty) = nullable.empty
    return NullablesRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // (nullable.inter_min A A) = A
    return NullablesRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == Kind::NULLABLE_UNION_DISJOINT
      || n[1].getKind() == Kind::NULLABLE_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (nullable.inter_min A (nullable.union_disjoint A B)) = A
      // (nullable.inter_min A (nullable.union_disjoint B A)) = A
      // (nullable.inter_min A (nullable.union_max A B)) = A
      // (nullable.inter_min A (nullable.union_max B A)) = A
      return NullablesRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == Kind::NULLABLE_UNION_DISJOINT
      || n[0].getKind() == Kind::NULLABLE_UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (nullable.inter_min (nullable.union_disjoint A B) A) = A
      // (nullable.inter_min (nullable.union_disjoint B A) A) = A
      // (nullable.inter_min (nullable.union_max A B) A) = A
      // (nullable.inter_min (nullable.union_max B A) A) = A
      return NullablesRewriteResponse(n[1], Rewrite::INTERSECTION_SHARED_RIGHT);
    }
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteDifferenceSubtract(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == Kind::NULLABLE_EMPTY || n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.difference_subtract A nullable.empty) = A
    // (nullable.difference_subtract nullable.empty A) = nullable.empty
    return NullablesRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // (nullable.difference_subtract A A) = nullable.empty
    Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
    return NullablesRewriteResponse(emptyNullable, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == Kind::NULLABLE_UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (nullable.difference_subtract (nullable.union_disjoint A B) A) = B
      return NullablesRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // (nullable.difference_subtract (nullable.union_disjoint B A) A) = B
      return NullablesRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == Kind::NULLABLE_UNION_DISJOINT
      || n[1].getKind() == Kind::NULLABLE_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (nullable.difference_subtract A (nullable.union_disjoint A B)) = nullable.empty
      // (nullable.difference_subtract A (nullable.union_disjoint B A)) = nullable.empty
      // (nullable.difference_subtract A (nullable.union_max A B)) = nullable.empty
      // (nullable.difference_subtract A (nullable.union_max B A)) = nullable.empty
      Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
      return NullablesRewriteResponse(emptyNullable, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::NULLABLE_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (nullable.difference_subtract (nullable.inter_min A B) A) = nullable.empty
      // (nullable.difference_subtract (nullable.inter_min B A) A) = nullable.empty
      Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
      return NullablesRewriteResponse(emptyNullable, Rewrite::SUBTRACT_MIN);
    }
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_DIFFERENCE_REMOVE);

  if (n[0].getKind() == Kind::NULLABLE_EMPTY || n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    // (nullable.difference_remove A nullable.empty) = A
    // (nullable.difference_remove nullable.empty B) = nullable.empty
    return NullablesRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // (nullable.difference_remove A A) = nullable.empty
    Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
    return NullablesRewriteResponse(emptyNullable, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == Kind::NULLABLE_UNION_DISJOINT
      || n[1].getKind() == Kind::NULLABLE_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (nullable.difference_remove A (nullable.union_disjoint A B)) = nullable.empty
      // (nullable.difference_remove A (nullable.union_disjoint B A)) = nullable.empty
      // (nullable.difference_remove A (nullable.union_max A B)) = nullable.empty
      // (nullable.difference_remove A (nullable.union_max B A)) = nullable.empty
      Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
      return NullablesRewriteResponse(emptyNullable, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::NULLABLE_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (nullable.difference_remove (nullable.inter_min A B) A) = nullable.empty
      // (nullable.difference_remove (nullable.inter_min B A) A) = nullable.empty
      Node emptyNullable = d_nm->mkConst(EmptyNullable(n.getType()));
      return NullablesRewriteResponse(emptyNullable, Rewrite::REMOVE_MIN);
    }
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_CHOOSE);
  if (n[0].getKind() == Kind::NULLABLE_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>() > 0)
  {
    // (nullable.choose (nullable x c)) = x where c is a constant > 0
    return NullablesRewriteResponse(n[0][0], Rewrite::CHOOSE_NULLABLE_MAKE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_CARD);
  if (n[0].getKind() == Kind::NULLABLE_MAKE && n[0][1].isConst())
  {
    // (nullable.card (nullable x c)) = c where c is a constant > 0
    return NullablesRewriteResponse(n[0][1], Rewrite::CARD_NULLABLE_MAKE);
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteIsSingleton(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_IS_SINGLETON);
  if (n[0].getKind() == Kind::NULLABLE_MAKE)
  {
    // (nullable.is_singleton (nullable x c)) = (c == 1)
    Node equal = n[0][1].eqNode(d_one);
    return NullablesRewriteResponse(equal, Rewrite::IS_SINGLETON_NULLABLE_MAKE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteFromSet(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_FROM_SET);
  if (n[0].getKind() == Kind::SET_SINGLETON)
  {
    // (nullable.from_set (set.singleton x)) = (nullable x 1)
    Node nullable = d_nm->mkNode(Kind::NULLABLE_MAKE, n[0][0], d_one);
    return NullablesRewriteResponse(nullable, Rewrite::FROM_SINGLETON);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::rewriteToSet(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_TO_SET);
  if (n[0].getKind() == Kind::NULLABLE_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // (nullable.to_set (nullable x n)) = (set.singleton x)
    // where n is a positive constant and T is the type of the nullable's elements
    Node set = d_nm->mkNode(Kind::SET_SINGLETON, n[0][0]);
    return NullablesRewriteResponse(set, Rewrite::TO_SINGLETON);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    Node ret = d_nm->mkConst(true);
    return NullablesRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    Node ret = d_nm->mkConst(false);
    return NullablesRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // standard ordering
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return NullablesRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_MAP);
  if (n[1].isConst())
  {
    // (nullable.map f (as nullable.empty (Nullable T1)) = (as nullable.empty (Nullable T2))
    // (nullable.map f (nullable "a" 3)) = (nullable (f "a") 3)
    std::map<Node, Rational> elements = NullablesUtils::getNullableElements(n[1]);
    std::map<Node, Rational> mappedElements;
    std::map<Node, Rational>::iterator it = elements.begin();
    while (it != elements.end())
    {
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], it->first);
      mappedElements[mappedElement] = it->second;
      ++it;
    }
    TypeNode t = d_nm->mkNullableType(n[0].getType().getRangeType());
    Node ret = NullablesUtils::constructConstantNullableFromElements(t, mappedElements);
    return NullablesRewriteResponse(ret, Rewrite::MAP_CONST);
  }
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::NULLABLE_MAKE:
    {
      // (nullable.map f (nullable x y)) = (nullable (apply f x) y)
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::NULLABLE_MAKE, mappedElement, n[1][1]);
      return NullablesRewriteResponse(ret, Rewrite::MAP_NULLABLE_MAKE);
    }

    case Kind::NULLABLE_UNION_DISJOINT:
    {
      // (nullable.map f (nullable.union_disjoint A B)) =
      //    (nullable.union_disjoint (nullable.map f A) (nullable.map f B))
      Node a = d_nm->mkNode(Kind::NULLABLE_MAP, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::NULLABLE_MAP, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::NULLABLE_UNION_DISJOINT, a, b);
      return NullablesRewriteResponse(ret, Rewrite::MAP_UNION_DISJOINT);
    }

    default: return NullablesRewriteResponse(n, Rewrite::NONE);
  }
}

NullablesRewriteResponse NullablesRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_FILTER);
  Node P = n[0];
  Node A = n[1];
  TypeNode t = A.getType();
  if (A.isConst())
  {
    // (nullable.filter p (as nullable.empty (Nullable T)) = (as nullable.empty (Nullable T))
    // (nullable.filter p (nullable "a" 3) ((nullable "b" 2))) =
    //   (nullable.union_disjoint
    //     (ite (p "a") (nullable "a" 3) (as nullable.empty (Nullable T)))
    //     (ite (p "b") (nullable "b" 2) (as nullable.empty (Nullable T)))

    Node ret = NullablesUtils::evaluateNullableFilter(n);
    return NullablesRewriteResponse(ret, Rewrite::FILTER_CONST);
  }
  Kind k = A.getKind();
  switch (k)
  {
    case Kind::NULLABLE_MAKE:
    {
      // (nullable.filter p (nullable x y)) = (ite (p x) (nullable x y) (as nullable.empty (Nullable T)))
      Node empty = d_nm->mkConst(EmptyNullable(t));
      Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, A[0]);
      Node ret = d_nm->mkNode(Kind::ITE, pOfe, A, empty);
      return NullablesRewriteResponse(ret, Rewrite::FILTER_NULLABLE_MAKE);
    }

    case Kind::NULLABLE_UNION_DISJOINT:
    {
      // (nullable.filter p (nullable.union_disjoint A B)) =
      //    (nullable.union_disjoint (nullable.filter p A) (nullable.filter p B))
      Node a = d_nm->mkNode(Kind::NULLABLE_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::NULLABLE_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::NULLABLE_UNION_DISJOINT, a, b);
      return NullablesRewriteResponse(ret, Rewrite::FILTER_UNION_DISJOINT);
    }

    default: return NullablesRewriteResponse(n, Rewrite::NONE);
  }
}

NullablesRewriteResponse NullablesRewriter::postRewriteFold(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_FOLD);
  Node f = n[0];
  Node t = n[1];
  Node nullable = n[2];
  if (nullable.isConst())
  {
    Node value = NullablesUtils::evaluateNullableFold(n);
    return NullablesRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  Kind k = nullable.getKind();
  switch (k)
  {
    case Kind::NULLABLE_MAKE:
    {
      if (nullable[1].isConst() && nullable[1].getConst<Rational>() > Rational(0))
      {
        // (nullable.fold f t (nullable x n)) = (f t ... (f t (f t x))) n times, n > 0
        Node value = NullablesUtils::evaluateNullableFold(n);
        return NullablesRewriteResponse(value, Rewrite::FOLD_NULLABLE);
      }
      break;
    }
    case Kind::NULLABLE_UNION_DISJOINT:
    {
      // (nullable.fold f t (nullable.union_disjoint A B)) =
      //       (nullable.fold f (nullable.fold f t A) B) where A < B to break symmetry
      Node A = nullable[0] < nullable[1] ? nullable[0] : nullable[1];
      Node B = nullable[0] < nullable[1] ? nullable[1] : nullable[0];
      Node foldA = d_nm->mkNode(Kind::NULLABLE_FOLD, f, t, A);
      Node fold = d_nm->mkNode(Kind::NULLABLE_FOLD, f, foldA, B);
      return NullablesRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
    }
    default: return NullablesRewriteResponse(n, Rewrite::NONE);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewritePartition(const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_PARTITION);
  if (n[1].isConst())
  {
    Node ret = NullablesUtils::evaluateNullablePartition(d_rewriter, n);
    if (ret != n)
    {
      return NullablesRewriteResponse(ret, Rewrite::PARTITION_CONST);
    }
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = NullablesUtils::evaluateTableAggregate(d_rewriter, n);
    if (ret != n)
    {
      return NullablesRewriteResponse(ret, Rewrite::AGGREGATE_CONST);
    }
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyNullable(tableType));
  if (n[0].getKind() == Kind::NULLABLE_EMPTY || n[1].getKind() == Kind::NULLABLE_EMPTY)
  {
    return NullablesRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  return NullablesRewriteResponse(n, Rewrite::NONE);
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

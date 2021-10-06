/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference generator utility.
 */

#include "inference_generator.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/uf/equality_engine.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(SolverState* state, InferenceManager* im)
    : d_state(state), d_im(im)
{
  d_nm = NodeManager::currentNM();
  d_sm = d_nm->getSkolemManager();
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConst(Rational(0));
  d_one = d_nm->mkConst(Rational(1));
}

InferInfo InferenceGenerator::nonNegativeCount(Node n, Node e)
{
  Assert(n.getType().isBag());
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node count = d_nm->mkNode(kind::BAG_COUNT, e, n);

  Node gte = d_nm->mkNode(kind::GEQ, count, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::mkBag(Node n, Node e)
{
  Assert(n.getKind() == kind::MK_BAG);
  Assert(e.getType() == n.getType().getBagElementType());

  if (n[0] == e)
  {
    // TODO issue #78: refactor this with BagRewriter
    // (=> true (= (bag.count e (bag e c)) c))
    InferInfo inferInfo(d_im, InferenceId::BAGS_MK_BAG_SAME_ELEMENT);
    Node skolem = getSkolem(n, inferInfo);
    Node count = getMultiplicityTerm(e, skolem);
    inferInfo.d_conclusion = count.eqNode(n[1]);
    return inferInfo;
  }
  else
  {
    // (=>
    //   true
    //   (= (bag.count e (bag x c)) (ite (= e x) c 0)))
    InferInfo inferInfo(d_im, InferenceId::BAGS_MK_BAG);
    Node skolem = getSkolem(n, inferInfo);
    Node count = getMultiplicityTerm(e, skolem);
    Node same = d_nm->mkNode(kind::EQUAL, n[0], e);
    Node ite = d_nm->mkNode(kind::ITE, same, n[1], d_zero);
    Node equal = count.eqNode(ite);
    inferInfo.d_conclusion = equal;
    return inferInfo;
  }
}

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the distinct elements in a bag, used
 * for axiomatizing the behavior of some term.
 */
struct IndexVarAttributeId
{
};
typedef expr::Attribute<IndexVarAttributeId, Node> IndexVarAttribute;

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the distinct elements in a bag, used
 * for axiomatizing the behavior of some term.
 */
struct SecondIndexVarAttributeId
{
};
typedef expr::Attribute<SecondIndexVarAttributeId, Node>
    SecondIndexVarAttribute;

struct BagsDeqAttributeId
{
};
typedef expr::Attribute<BagsDeqAttributeId, Node> BagsDeqAttribute;

InferInfo InferenceGenerator::bagDisequality(Node n)
{
  Assert(n.getKind() == kind::EQUAL && n[0].getType().isBag());

  Node A = n[0];
  Node B = n[1];

  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY);

  TypeNode elementType = A.getType().getBagElementType();
  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node element = bvm->mkBoundVar<BagsDeqAttribute>(n, elementType);
  Node skolem =
      d_sm->mkSkolem(element,
                     n,
                     "bag_disequal",
                     "an extensional lemma for disequality of two bags");

  Node countA = getMultiplicityTerm(skolem, A);
  Node countB = getMultiplicityTerm(skolem, B);

  Node disEqual = countA.eqNode(countB).notNode();

  inferInfo.d_premises.push_back(n.notNode());
  inferInfo.d_conclusion = disEqual;
  return inferInfo;
}

Node InferenceGenerator::getSkolem(Node& n, InferInfo& inferInfo)
{
  Node skolem = d_sm->mkPurifySkolem(n, "skolem_bag", "skolem bag");
  inferInfo.d_skolems[n] = skolem;
  return skolem;
}

InferInfo InferenceGenerator::empty(Node n, Node e)
{
  Assert(n.getKind() == kind::EMPTYBAG);
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_EMPTY);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node equal = count.eqNode(d_zero);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionDisjoint(Node n, Node e)
{
  Assert(n.getKind() == kind::UNION_DISJOINT && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_DISJOINT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node sum = d_nm->mkNode(kind::PLUS, countA, countB);
  Node equal = count.eqNode(sum);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionMax(Node n, Node e)
{
  Assert(n.getKind() == kind::UNION_MAX && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_MAX);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gt = d_nm->mkNode(kind::GT, countA, countB);
  Node max = d_nm->mkNode(kind::ITE, gt, countA, countB);
  Node equal = count.eqNode(max);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::intersection(Node n, Node e)
{
  Assert(n.getKind() == kind::INTERSECTION_MIN && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_INTERSECTION_MIN);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node lt = d_nm->mkNode(kind::LT, countA, countB);
  Node min = d_nm->mkNode(kind::ITE, lt, countA, countB);
  Node equal = count.eqNode(min);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceSubtract(Node n, Node e)
{
  Assert(n.getKind() == kind::DIFFERENCE_SUBTRACT && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_SUBTRACT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node subtract = d_nm->mkNode(kind::MINUS, countA, countB);
  Node gte = d_nm->mkNode(kind::GEQ, countA, countB);
  Node difference = d_nm->mkNode(kind::ITE, gte, subtract, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceRemove(Node n, Node e)
{
  Assert(n.getKind() == kind::DIFFERENCE_REMOVE && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_REMOVE);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node notInB = d_nm->mkNode(kind::EQUAL, countB, d_zero);
  Node difference = d_nm->mkNode(kind::ITE, notInB, countA, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::duplicateRemoval(Node n, Node e)
{
  Assert(n.getKind() == kind::DUPLICATE_REMOVAL && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DUPLICATE_REMOVAL);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gte = d_nm->mkNode(kind::GEQ, countA, d_one);
  Node ite = d_nm->mkNode(kind::ITE, gte, d_one, d_zero);
  Node equal = count.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

Node InferenceGenerator::getMultiplicityTerm(Node element, Node bag)
{
  Node count = d_nm->mkNode(kind::BAG_COUNT, element, bag);
  return count;
}

InferInfo InferenceGenerator::map(Node n, Node e)
{
  Assert(n.getKind() == kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);
  Assert(e.getType() == n[0].getType().getRangeType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP);
  Node f = n[0];
  Node A = n[1];
  std::cout << "f: " << f << std::endl;
  std::cout << "A: " << A << std::endl;

  TypeNode domainType = f.getType().getArgTypes()[0];
  Node emptybag = d_nm->mkConst(EmptyBag(A.getType()));
  Node isEmpty = d_nm->mkNode(kind::EQUAL, A, emptybag);
  Node mapSkolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, mapSkolem);

  Node x = d_nm->mkNode(kind::BAG_CHOOSE, A);
  Node countX = getMultiplicityTerm(x, A);
  Node bagX = d_nm->mkBag(domainType, x, countX);
  Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
  Node f_xEqualE = d_nm->mkNode(kind::EQUAL, e, f_x);

  Node difference = d_nm->mkNode(kind::DIFFERENCE_REMOVE, A, bagX);
  Node differenceSkolem = getSkolem(difference, inferInfo);
  Node mapDifference = d_nm->mkNode(kind::BAG_MAP, f, differenceSkolem);
  Node mapDifferenceSkolem = getSkolem(mapDifference, inferInfo);
  Node countMapDifference1 =
      d_nm->mkNode(kind::BAG_COUNT, e, mapDifferenceSkolem);
  Node countMapDifference2 =
      d_nm->mkNode(kind::PLUS, countX, countMapDifference1);
  Node ite = d_nm->mkNode(
      kind::ITE,
      isEmpty,
      d_zero,
      d_nm->mkNode(
          kind::ITE, f_xEqualE, countMapDifference2, countMapDifference1));

  Node equal = d_nm->mkNode(kind::EQUAL, count, ite);
  TypeNode rangeType = n[0].getType().getRangeType();
  Node mapDefinition1 = d_nm->mkNode(
      kind::EQUAL,
      isEmpty,
      d_nm->mkNode(kind::EQUAL, n, d_nm->mkConst(EmptyBag(d_nm->mkBagType(rangeType)))));

  Node mapDefinition2 = d_nm->mkNode(
      kind::EQUAL,
      isEmpty.negate(),
      d_nm->mkNode(kind::EQUAL,
                   n,
                   d_nm->mkNode(kind::UNION_DISJOINT,
                                d_nm->mkBag(rangeType, f_x, countX),
                                mapDifference)));
  inferInfo.d_conclusion =
      equal.andNode(mapDefinition1).andNode(mapDefinition2);

  std::cout << "conclusion: " << inferInfo.d_conclusion << std::endl << std::endl;

  return inferInfo;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

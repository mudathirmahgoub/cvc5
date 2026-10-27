/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(Env& env,
                                       SolverState* state,
                                       InferenceManager* im)
    : EnvObj(env),
      d_nm(env.getNodeManager()),
      d_sm(d_nm->getSkolemManager()),
      d_state(state),
      d_im(im)
{
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

void InferenceGenerator::registerCountTerm(Node n)
{
  Assert(n.getKind() == Kind::BAG_COUNT);
  Node element = d_state->getRepresentative(n[0]);
  Node bag = d_state->getRepresentative(n[1]);
  Node count = d_nm->mkNode(Kind::BAG_COUNT, element, bag);
  Node skolem = registerAndAssertSkolemLemma(count);
  d_state->registerCountTerm(bag, element, skolem);
}

void InferenceGenerator::registerCardinalityTerm(Node n)
{
  Assert(n.getKind() == Kind::BAG_CARD);
  Node bag = d_state->getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(Kind::BAG_CARD, bag);
  Node skolem = registerAndAssertSkolemLemma(cardTerm);
  d_state->registerCardinalityTerm(cardTerm, skolem);
  Node premise = n[0].eqNode(bag);
  Node conclusion = skolem.eqNode(n);
  Node lemma = premise.notNode().orNode(conclusion);
  d_im->addPendingLemma(lemma, InferenceId::BAGS_SKOLEM);
}

InferInfo InferenceGenerator::nonNegativeCount(Node n, Node e)
{
  Assert(n.getType().isBag());
  AssertEqual(e.getType(), n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node count = d_nm->mkNode(Kind::BAG_COUNT, e, n);
  Node gte = d_nm->mkNode(Kind::GEQ, count, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::nonNegativeCardinality(Node n)
{
  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node gte = d_nm->mkNode(Kind::GEQ, n, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::bagMake(Node n)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  /*
   * (or
   *   (and (<  c 1) (= (bag x c) (as bag.empty (Bag E))))
   *   (and (>= c 1) (not (= (bag x c) (as bag.empty (Bag E))))
   */
  Node x = n[0];
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_BAG_MAKE_SPLIT);
  Node empty = d_nm->mkConst(EmptyBag(n.getType()));
  Node equal = d_nm->mkNode(Kind::EQUAL, n, empty);
  Node geq = d_nm->mkNode(Kind::GEQ, c, d_one);
  Node isEmpty = geq.notNode().andNode(equal);
  Node isNotEmpty = geq.andNode(equal.notNode());
  Node orNode = isEmpty.orNode(isNotEmpty);
  inferInfo.d_conclusion = orNode;
  return inferInfo;
}

InferInfo InferenceGenerator::bagMake(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  AssertEqual(e.getType(), n.getType().getBagElementType());

  /*
   * (ite (and (= e x) (>= c 1))
   *   (= (bag.count e skolem) c)
   *   (= (bag.count e skolem) 0))
   */
  Node x = n[0];
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_BAG_MAKE);
  Node same = d_nm->mkNode(Kind::EQUAL, e, x);
  Node geq = d_nm->mkNode(Kind::GEQ, c, d_one);
  Node andNode = same.andNode(geq);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);
  Node equalC = d_nm->mkNode(Kind::EQUAL, count, c);
  Node equalZero = d_nm->mkNode(Kind::EQUAL, count, d_zero);
  Node ite = d_nm->mkNode(Kind::ITE, andNode, equalC, equalZero);
  inferInfo.d_conclusion = ite;
  return inferInfo;
}

InferInfo InferenceGenerator::bagDisequality(Node equality, Node witness)
{
  Assert(equality.getKind() == Kind::EQUAL && equality[0].getType().isBag());
  Node A = equality[0];
  Node B = equality[1];

  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY);

  Node countA = getMultiplicityTerm(witness, A);
  Node countB = getMultiplicityTerm(witness, B);

  Node disequal = countA.eqNode(countB).notNode();

  inferInfo.d_premises.push_back(equality.notNode());
  inferInfo.d_conclusion = disequal;
  return inferInfo;
}

namespace {
/**
 * a part of a union: (bag.map f (bag.filter p X)), f or p null when absent;
 * for (bag.filter p X) f is null, for (bag.map f X) p is null, and for a
 * table X both are
 */
struct UnionPart
{
  Node f;
  Node p;
  Node X;
};
/**
 * the parts of n, a tree of bag.union_disjoint, as UnionPart: for
 * (bag.union_disjoint (bag.map f X) (bag.union_disjoint (bag.filter p X)
 * Y)), the parts (f, null, X), (null, p, X) and (null, null, Y); an empty bag
 * is no part
 */
void unionParts(const Node& n, std::vector<UnionPart>& parts)
{
  if (n.getKind() == Kind::BAG_UNION_DISJOINT)
  {
    unionParts(n[0], parts);
    unionParts(n[1], parts);
    return;
  }
  if (n.getKind() == Kind::BAG_EMPTY)
  {
    return;
  }
  UnionPart part;
  Node rest = n;
  if (rest.getKind() == Kind::BAG_MAP)
  {
    part.f = rest[0];
    rest = rest[1];
  }
  if (rest.getKind() == Kind::BAG_FILTER)
  {
    part.p = rest[0];
    rest = rest[1];
  }
  part.X = rest;
  parts.push_back(part);
}
}  // namespace

InferInfo InferenceGenerator::bagDisequalityPointwise(Node equality)
{
  // equality is (= A B), A and B unions of parts (bag.map f (bag.filter p
  // X)). Grouped by f and X, the parts of a group give a row e of X the
  // multiplicity (+ (ite (p1 e) 1 0) .. (ite (pn e) 1 0)) times its own; if
  // every group gives every row the same sum on both sides, the two sides are
  // equal. So when they are not, some row of some group differs:
  //   (=> (not (= A B))
  //       (or (and (>= (bag.count e1 X1) 1)
  //                (not (= (+ (ite (p1 e1) 1 0) (ite (p2 e1) 1 0))
  //                        (ite (q1 e1) 1 0))))
  //           ..))
  // with one fresh element e1 per group (f1, X1), the parts with p1 and p2 on
  // the left, q1 on the right. E.g. for
  //   (= (bag.union_disjoint (bag.filter p X) (bag.filter q X))
  //      (bag.filter r X))
  // the conclusion is
  //   (and (>= (bag.count e X) 1)
  //        (not (= (+ (ite (p e) 1 0) (ite (q e) 1 0)) (ite (r e) 1 0))))
  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY_POINTWISE);
  std::vector<UnionPart> pa, pb;
  unionParts(equality[0], pa);
  unionParts(equality[1], pb);
  if (pa.size() + pb.size() <= 2)
  {
    return inferInfo;
  }
  // groups (f, X), in order of first appearance, with the predicates of their
  // parts on each side; a part without a filter has the predicate true
  std::vector<std::pair<Node, Node>> keys;
  std::map<std::pair<Node, Node>,
           std::pair<std::vector<Node>, std::vector<Node>>>
      groups;
  auto add = [&](const UnionPart& part, bool left) {
    std::pair<Node, Node> key(part.f, part.X);
    if (groups.find(key) == groups.end())
    {
      keys.push_back(key);
    }
    std::vector<Node>& side = left ? groups[key].first : groups[key].second;
    side.push_back(part.p.isNull() ? d_nm->mkConst(true) : part.p);
  };
  for (const UnionPart& part : pa)
  {
    add(part, true);
  }
  for (const UnionPart& part : pb)
  {
    add(part, false);
  }
  std::vector<Node> disjuncts;
  for (const std::pair<Node, Node>& key : keys)
  {
    const std::vector<Node>& ps = groups[key].first;
    const std::vector<Node>& qs = groups[key].second;
    if (ps == qs)
    {
      continue;
    }
    Node X = key.second;
    Node cacheKey = d_nm->mkNode(
        Kind::SEXPR, equality, key.first.isNull() ? X : key.first, X);
    std::map<Node, Node>::iterator it = d_elementWitnesses.find(cacheKey);
    if (it == d_elementWitnesses.end())
    {
      Node e = NodeManager::mkDummySkolem("e", X.getType().getBagElementType());
      it = d_elementWitnesses.emplace(cacheKey, e).first;
    }
    Node e = it->second;
    // (+ (ite (p1 e) 1 0) (ite (p2 e) 1 0)), or 0 for no part
    auto sum = [&](const std::vector<Node>& preds) {
      std::vector<Node> terms;
      for (const Node& p : preds)
      {
        Node holds = p.isConst() ? p : mkApplyFunction(p, e);
        terms.push_back(d_nm->mkNode(Kind::ITE, holds, d_one, d_zero));
      }
      if (terms.empty())
      {
        return d_zero;
      }
      return terms.size() == 1 ? terms[0] : d_nm->mkNode(Kind::ADD, terms);
    };
    Node inX =
        d_nm->mkNode(Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, e, X), d_one);
    disjuncts.push_back(inX.andNode(sum(ps).eqNode(sum(qs)).notNode()));
  }
  if (disjuncts.empty())
  {
    return inferInfo;
  }
  inferInfo.d_premises.push_back(equality.notNode());
  inferInfo.d_conclusion =
      disjuncts.size() == 1 ? disjuncts[0] : d_nm->mkNode(Kind::OR, disjuncts);
  return inferInfo;
}

InferInfo InferenceGenerator::bagDisequalityDecompose(Node equality)
{
  // equality is (= A B) with A = (op A1 .. An) and B = (op B1 .. Bn) of one
  // operator: when they differ, some pair of arguments does, the converse of
  // congruence,
  //   (=> (not (= (table.product X1 Y1) (table.product X2 Y2)))
  //       (or (not (= X1 X2)) (not (= Y1 Y2))))
  // A pair of functions differs at a witness: for a map or a filter at an
  // element e of the bag it is applied to,
  //   (=> (not (= (bag.map f X) (bag.map g X)))
  //       (and (>= (bag.count e X) 1) (not (= (f e) (g e)))))
  // and at fresh arguments w1, w2 for the step of a fold or an aggregate,
  // (not (= (f w1 w2) (g w1 w2))). It lets the solver find the place where
  // two queries of the same shape differ, instead of relating the
  // multiplicities of their results, which for a non-injective map needs the
  // sums of two preimages.
  Assert(equality.getKind() == Kind::EQUAL && equality[0].getType().isBag());
  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY_DECOMPOSE);
  Node A = equality[0];
  Node B = equality[1];
  Kind k = A.getKind();
  if (k != B.getKind() || A.getNumChildren() == 0
      || A.getNumChildren() != B.getNumChildren())
  {
    return inferInfo;
  }
  bool paramA = A.getMetaKind() == kind::metakind::PARAMETERIZED;
  bool paramB = B.getMetaKind() == kind::metakind::PARAMETERIZED;
  if (paramA != paramB || (paramA && A.getOperator() != B.getOperator()))
  {
    return inferInfo;
  }
  switch (k)
  {
    case Kind::BAG_MAP:
    case Kind::BAG_FILTER:
    case Kind::BAG_SETOF:
    case Kind::BAG_UNION_DISJOINT:
    case Kind::BAG_UNION_MAX:
    case Kind::BAG_INTER_MIN:
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE:
    case Kind::TABLE_PRODUCT:
    case Kind::TABLE_JOIN:
    case Kind::TABLE_AGGREGATE:
    case Kind::TABLE_GROUP:
    case Kind::TABLE_PROJECT: break;
    default: return inferInfo;
  }
  std::vector<Node> disjuncts;
  for (size_t i = 0, n = A.getNumChildren(); i < n; i++)
  {
    if (A[i].getType() != B[i].getType())
    {
      // two maps of one result type over rows of different types: the
      // arguments differ trivially and the lemma would say nothing
      return InferInfo(d_im, InferenceId::BAGS_DISEQUALITY_DECOMPOSE);
    }
    if (A[i] == B[i])
    {
      continue;
    }
    if (A[i].getType().isFunction())
    {
      // two functions differ where they differ on some argument, applied to
      // both so that no equality between functions is asserted and the
      // lambdas reduce. For a map or a filter the argument is an element of
      // the bag they are applied to: the functions only have to agree there,
      // like the two sides of "select a .. where a = b" and "select b ..",
      // and the filter below tells the solver what holds of such an element
      if (A[i].getType().getArgTypes().size() != 1)
      {
        // a fold's or an aggregate's step: compared at a witness per argument
        std::vector<Node> args;
        for (size_t a = 0, na = A[i].getType().getArgTypes().size(); a < na;
             a++)
        {
          args.push_back(d_sm->mkSkolemFunction(
              SkolemId::HO_DEQ_DIFF,
              {A[i], B[i], d_nm->mkConstInt(Rational(a))}));
        }
        Node fa = mkApplyFunction(A[i], args);
        Node fb = mkApplyFunction(B[i], args);
        disjuncts.push_back(fa.eqNode(fb).notNode());
        continue;
      }
      Node fa, fb, inBag;
      if ((k == Kind::BAG_MAP || k == Kind::BAG_FILTER) && i == 0)
      {
        Node X = A[1];
        Node key = d_nm->mkNode(Kind::SEXPR, A[i], B[i], X);
        std::map<Node, Node>::iterator it = d_elementWitnesses.find(key);
        if (it == d_elementWitnesses.end())
        {
          Node e =
              NodeManager::mkDummySkolem("e", X.getType().getBagElementType());
          it = d_elementWitnesses.emplace(key, e).first;
        }
        Node e = it->second;
        inBag =
            d_nm->mkNode(Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, e, X), d_one);
        fa = mkApplyFunction(A[i], e);
        fb = mkApplyFunction(B[i], e);
      }
      else
      {
        Node w = d_sm->mkSkolemFunction(
            SkolemId::HO_DEQ_DIFF, {A[i], B[i], d_nm->mkConstInt(Rational(0))});
        fa = mkApplyFunction(A[i], w);
        fb = mkApplyFunction(B[i], w);
      }
      Node differ = fa.eqNode(fb).notNode();
      disjuncts.push_back(inBag.isNull() ? differ : inBag.andNode(differ));
      continue;
    }
    disjuncts.push_back(A[i].eqNode(B[i]).notNode());
  }
  if (disjuncts.empty())
  {
    return inferInfo;
  }
  if ((k == Kind::BAG_UNION_DISJOINT || k == Kind::BAG_UNION_MAX
       || k == Kind::BAG_INTER_MIN)
      && A[0] != B[1] && A[1] != B[0])
  {
    // a commutative operator: the arguments may meet in the other order, and
    //   (not (= (bag.union_disjoint A1 A2) (bag.union_disjoint B1 B2)))
    // also gives (or (not (= A1 B2)) (not (= A2 B1))). One lemma says both:
    // some pairing of the arguments differs in each,
    //   (and (or (not (= A1 B1)) (not (= A2 B2)))
    //        (or (not (= A1 B2)) (not (= A2 B1))))
    Node straight = disjuncts.size() == 1 ? disjuncts[0]
                                          : d_nm->mkNode(Kind::OR, disjuncts);
    Node swapped = d_nm->mkNode(
        Kind::OR, A[0].eqNode(B[1]).notNode(), A[1].eqNode(B[0]).notNode());
    inferInfo.d_premises.push_back(equality.notNode());
    inferInfo.d_conclusion = straight.andNode(swapped);
    return inferInfo;
  }
  inferInfo.d_premises.push_back(equality.notNode());
  inferInfo.d_conclusion =
      disjuncts.size() == 1 ? disjuncts[0] : d_nm->mkNode(Kind::OR, disjuncts);
  return inferInfo;
}

Node InferenceGenerator::registerAndAssertSkolemLemma(Node& n)
{
  Node skolem = d_sm->mkPurifySkolem(n);
  Node lemma = n.eqNode(skolem);
  d_im->addPendingLemma(lemma, InferenceId::BAGS_SKOLEM);
  Trace("bags-skolems") << "bags-skolems:  " << skolem << " = " << n
                        << std::endl;
  return skolem;
}

InferInfo InferenceGenerator::empty(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_EMPTY);
  AssertEqual(e.getType(), n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_EMPTY);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node equal = count.eqNode(d_zero);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionDisjoint(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_DISJOINT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node sum = d_nm->mkNode(Kind::ADD, countA, countB);
  Node equal = count.eqNode(sum);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionMax(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_MAX);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node gt = d_nm->mkNode(Kind::GT, countA, countB);
  Node max = d_nm->mkNode(Kind::ITE, gt, countA, countB);
  Node equal = count.eqNode(max);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::intersection(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_INTERSECTION_MIN);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node lt = d_nm->mkNode(Kind::LT, countA, countB);
  Node min = d_nm->mkNode(Kind::ITE, lt, countA, countB);
  Node equal = count.eqNode(min);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceSubtract(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT
         && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_SUBTRACT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node subtract = d_nm->mkNode(Kind::SUB, countA, countB);
  Node gte = d_nm->mkNode(Kind::GEQ, countA, countB);
  Node difference = d_nm->mkNode(Kind::ITE, gte, subtract, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceRemove(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_REMOVE);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node notInB = d_nm->mkNode(Kind::LEQ, countB, d_zero);
  Node difference = d_nm->mkNode(Kind::ITE, notInB, countA, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::setof(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_SETOF && n[0].getType().isBag());
  AssertEqual(e.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  InferInfo inferInfo(d_im, InferenceId::BAGS_SETOF);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node gte = d_nm->mkNode(Kind::GEQ, countA, d_one);
  Node ite = d_nm->mkNode(Kind::ITE, gte, d_one, d_zero);
  Node equal = count.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::cardEmpty(const std::pair<Node, Node>& pair,
                                        Node n)
{
  Assert(pair.first.getKind() == Kind::BAG_CARD);
  Assert(n.getKind() == Kind::BAG_EMPTY
         && CVC5_EQUAL(n.getType(), pair.first[0].getType()));
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD_EMPTY);
  Node premise = pair.first[0].eqNode(n);
  Node conclusion = pair.second.eqNode(d_zero);
  inferInfo.d_conclusion = premise.eqNode(conclusion);
  return inferInfo;
}

InferInfo InferenceGenerator::cardBagMake(const std::pair<Node, Node>& pair,
                                          Node n)
{
  Assert(pair.first.getKind() == Kind::BAG_CARD);
  Assert(n.getKind() == Kind::BAG_MAKE
         && CVC5_EQUAL(n.getType(), pair.first[0].getType()));
  //(=>
  //  (and (= A (bag x c)) (>= 0 c))
  //  (= (bag.card A) c))
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD);
  Node nonNegative = d_nm->mkNode(Kind::GEQ, c, d_zero);
  Node premise = pair.first[0].eqNode(n).andNode(nonNegative);
  Node conclusion = pair.second.eqNode(c);
  inferInfo.d_conclusion = premise.notNode().orNode(conclusion);
  return inferInfo;
}

InferInfo InferenceGenerator::cardUnionDisjoint(
    Node premise, Node parent, const std::vector<Node>& children)
{
  Assert(premise.getType().isBoolean());
  Assert(!children.empty());
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD);

  std::vector<Node>::const_iterator it = children.cbegin();
  Node child = *it;
  d_state->registerBag(child);
  Node unionDisjoints = child;
  Node card = d_nm->mkNode(Kind::BAG_CARD, child);
  std::vector<Node> lemmas;
  Node sum = registerAndAssertSkolemLemma(card);
  ++it;
  while (it != children.end())
  {
    child = *it;
    d_state->registerBag(child);
    unionDisjoints =
        d_nm->mkNode(Kind::BAG_UNION_DISJOINT, unionDisjoints, child);
    card = d_nm->mkNode(Kind::BAG_CARD, child);
    Node skolem = registerAndAssertSkolemLemma(card);
    sum = d_nm->mkNode(Kind::ADD, sum, skolem);
    ++it;
  }
  Node parentCard = d_nm->mkNode(Kind::BAG_CARD, parent);
  Node parentSkolem = registerAndAssertSkolemLemma(parentCard);

  Node bags = parent.eqNode(unionDisjoints);
  lemmas.push_back(bags);
  Node cards = parentSkolem.eqNode(sum);
  lemmas.push_back(cards);
  Node conclusion = d_nm->mkNode(Kind::AND, lemmas);
  inferInfo.d_conclusion = premise.notNode().orNode(conclusion);
  return inferInfo;
}

Node InferenceGenerator::getMultiplicityTerm(Node element, Node bag)
{
  Node count = d_nm->mkNode(Kind::BAG_COUNT, element, bag);
  return count;
}

std::tuple<InferInfo, Node, Node> InferenceGenerator::mapDown(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);
  AssertEqual(e.getType(), n[0].getType().getRangeType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_DOWN);

  Node f = n[0];
  Node A = n[1];
  // declare an uninterpreted function uf: Int -> T
  Node uf = d_sm->mkSkolemFunction(SkolemId::BAGS_DISTINCT_ELEMENTS, {A});

  // declare uninterpreted function sum: Int -> Int
  Node sum = d_sm->mkSkolemFunction(SkolemId::BAGS_MAP_SUM, {f, A, e});

  // (= (sum 0) 0)
  Node sum_zero = d_nm->mkNode(Kind::APPLY_UF, sum, d_zero);
  Node baseCase = d_nm->mkNode(Kind::EQUAL, sum_zero, d_zero);

  // guess the size of distinct elements in A
  Node size =
      d_sm->mkSkolemFunction(SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE, {A});

  // (= (sum size) (bag.count e skolem))
  Node mapSkolem = registerAndAssertSkolemLemma(n);
  Node countE = getMultiplicityTerm(e, mapSkolem);
  Node totalSum = d_nm->mkNode(Kind::APPLY_UF, sum, size);
  Node totalSumEqualCountE = d_nm->mkNode(Kind::EQUAL, totalSum, countE);

  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node i = bvm->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, n, "i", d_nm->integerType());
  Node j = bvm->mkBoundVar(
      BoundVarId::BAGS_SECOND_INDEX, n, "j", d_nm->integerType());
  Node iList = d_nm->mkNode(Kind::BOUND_VAR_LIST, i);
  Node jList = d_nm->mkNode(Kind::BOUND_VAR_LIST, j);
  Node iPlusOne = d_nm->mkNode(Kind::ADD, i, d_one);
  Node iMinusOne = d_nm->mkNode(Kind::SUB, i, d_one);
  Node uf_i = d_nm->mkNode(Kind::APPLY_UF, uf, i);
  Node uf_j = d_nm->mkNode(Kind::APPLY_UF, uf, j);
  Node f_uf_i = d_nm->mkNode(Kind::APPLY_UF, f, uf_i);
  Node uf_iPlusOne = d_nm->mkNode(Kind::APPLY_UF, uf, iPlusOne);
  Node uf_iMinusOne = d_nm->mkNode(Kind::APPLY_UF, uf, iMinusOne);
  Node interval_i = d_nm->mkNode(
      Kind::AND,
      {d_nm->mkNode(Kind::GEQ, i, d_one), d_nm->mkNode(Kind::LEQ, i, size)});
  Node sum_i = d_nm->mkNode(Kind::APPLY_UF, sum, i);
  Node sum_iPlusOne = d_nm->mkNode(Kind::APPLY_UF, sum, iPlusOne);
  Node sum_iMinusOne = d_nm->mkNode(Kind::APPLY_UF, sum, iMinusOne);
  Node count_iMinusOne = d_nm->mkNode(Kind::BAG_COUNT, uf_iMinusOne, A);
  Node count_uf_i = d_nm->mkNode(Kind::BAG_COUNT, uf_i, A);
  Node addMultiplicity = d_nm->mkNode(
      Kind::EQUAL, sum_i, d_nm->mkNode(Kind::ADD, sum_iMinusOne, count_uf_i));
  Node previousValue = d_nm->mkNode(Kind::EQUAL, sum_i, sum_iMinusOne);
  Node f_iEqualE = d_nm->mkNode(Kind::EQUAL, f_uf_i, e);
  Node distinct = d_nm->mkNode(Kind::DISTINCT, f_uf_i, e);
  Node geqOne = d_nm->mkNode(Kind::GEQ, count_uf_i, d_one);

  // i < j <= size
  Node interval_j = d_nm->mkNode(
      Kind::AND,
      {d_nm->mkNode(Kind::LT, i, j), d_nm->mkNode(Kind::LEQ, j, size)});
  // uf(i) != uf(j)
  Node uf_i_equals_uf_j = d_nm->mkNode(Kind::EQUAL, uf_i, uf_j);
  Node notEqual = d_nm->mkNode(Kind::EQUAL, uf_i, uf_j).negate();
  Node body_j = d_nm->mkNode(Kind::OR, interval_j.negate(), notEqual);
  Node forAll_j =
      quantifiers::BoundedIntegers::mkBoundedForall(d_nm, jList, body_j);
  Node disjunct1 = d_nm->mkNode(Kind::AND, {f_iEqualE, addMultiplicity});
  Node disjunct2 = d_nm->mkNode(Kind::AND, {distinct, previousValue});
  Node orNode = disjunct1.orNode(disjunct2);
  Node andNode = d_nm->mkNode(Kind::AND, {forAll_j, geqOne, orNode});
  Node body_i = d_nm->mkNode(Kind::OR, interval_i.negate(), andNode);
  Node forAll_i =
      quantifiers::BoundedIntegers::mkBoundedForall(d_nm, iList, body_i);
  Node sizeGTE_zero = d_nm->mkNode(Kind::GEQ, size, d_zero);
  Node conclusion = d_nm->mkNode(
      Kind::AND, {baseCase, totalSumEqualCountE, forAll_i, sizeGTE_zero});
  inferInfo.d_conclusion = conclusion;

  Trace("bags::InferenceGenerator::mapDown")
      << "conclusion: " << inferInfo.d_conclusion << std::endl;
  return std::tuple(inferInfo, uf, size);
}

Node InferenceGenerator::mkApplyFunction(const Node& f,
                                         const std::vector<Node>& args)
{
  // (f a1 .. an), beta-reduced and rewritten when f is (the constant of) a
  // lambda
  Node lambda = uf::FunctionConst::getDefinition(f);
  std::vector<Node> children{lambda.isNull() ? f : lambda};
  children.insert(children.end(), args.begin(), args.end());
  Node app = d_nm->mkNode(Kind::APPLY_UF, children);
  return lambda.isNull() ? app : rewrite(app);
}

InferInfo InferenceGenerator::foldDecompose(Node a, Node b)
{
  // a = (bag.fold f1 i1 X1) and b = (bag.fold f2 i2 X2):
  //   (or (= a b) (not (= i1 i2)) (not (= X1 X2))
  //       (and (>= (bag.count x X1) 1) (not (= (f1 x acc) (f2 x acc)))))
  // with fresh x and acc, one pair per (f1, f2, X1); the disjuncts for
  // arguments that are one node are left out
  Assert(a.getKind() == Kind::BAG_FOLD && b.getKind() == Kind::BAG_FOLD);
  InferInfo inferInfo(d_im, InferenceId::BAGS_FOLD_DECOMPOSE);
  std::vector<Node> disjuncts;
  disjuncts.push_back(a.eqNode(b));
  if (a[1] != b[1])
  {
    disjuncts.push_back(a[1].eqNode(b[1]).notNode());
  }
  if (a[2] != b[2])
  {
    disjuncts.push_back(a[2].eqNode(b[2]).notNode());
  }
  if (a[0] != b[0])
  {
    Node X = a[2];
    Node key = d_nm->mkNode(Kind::SEXPR, a[0], b[0], X);
    std::map<Node, Node>::iterator it = d_elementWitnesses.find(key);
    if (it == d_elementWitnesses.end())
    {
      TypeNode accType = a.getType();
      Node x = NodeManager::mkDummySkolem("x", X.getType().getBagElementType());
      Node acc = NodeManager::mkDummySkolem("acc", accType);
      it = d_elementWitnesses.emplace(key, d_nm->mkNode(Kind::SEXPR, x, acc))
               .first;
    }
    Node x = it->second[0];
    Node acc = it->second[1];
    Node inBag =
        d_nm->mkNode(Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, x, X), d_one);
    Node fa = mkApplyFunction(a[0], {x, acc});
    Node fb = mkApplyFunction(b[0], {x, acc});
    disjuncts.push_back(inBag.andNode(fa.eqNode(fb).notNode()));
  }
  inferInfo.d_conclusion = d_nm->mkNode(Kind::OR, disjuncts);
  return inferInfo;
}

Node InferenceGenerator::mkApplyFunction(const Node& f, const Node& x)
{
  Node lambda = uf::FunctionConst::getDefinition(f);
  if (lambda.isNull())
  {
    return d_nm->mkNode(Kind::APPLY_UF, f, x);
  }
  return rewrite(d_nm->mkNode(Kind::APPLY_UF, lambda, x));
}

InferInfo InferenceGenerator::mapDownWitness(Node n, Node y)
{
  // (=> (>= (bag.count y (bag.map f A)) 1)
  //     (and (>= (bag.count w A) 1) (= (f w) y)))
  // for a fresh w: an element of a map's image has a preimage. Weaker than
  // mapDown, which sums the multiplicities of the whole preimage, and ground:
  // it is what refutes a y no element of A maps to.
  Assert(n.getKind() == Kind::BAG_MAP);
  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_DOWN_WITNESS);
  Node f = n[0];
  Node A = n[1];
  const std::set<Node>& aElements = d_state->getElements(A);
  for (const Node& x : aElements)
  {
    if (d_state->areEqual(mkApplyFunction(f, x), y))
    {
      // an element of A already maps to y: the map's up lemma for it says
      // the rest, and a witness would only add another element
      inferInfo.d_conclusion = d_true;
      return inferInfo;
    }
  }
  Node key = d_nm->mkNode(Kind::SEXPR, n, y, d_one);
  std::map<Node, Node>::iterator it = d_elementWitnesses.find(key);
  if (it == d_elementWitnesses.end())
  {
    Node w = NodeManager::mkDummySkolem("w", A.getType().getBagElementType());
    it = d_elementWitnesses.emplace(key, w).first;
  }
  Node w = it->second;
  Node inMap =
      d_nm->mkNode(Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, y, n), d_one);
  Node inA =
      d_nm->mkNode(Kind::GEQ, d_nm->mkNode(Kind::BAG_COUNT, w, A), d_one);
  inferInfo.d_premises.push_back(inMap);
  inferInfo.d_conclusion = inA.andNode(mkApplyFunction(f, w).eqNode(y));
  return inferInfo;
}

InferInfo InferenceGenerator::mapDownInjective(Node n, Node y)
{
  Assert(n.getKind() == Kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);
  AssertEqual(y.getType(), n[0].getType().getRangeType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_DOWN_INJECTIVE);

  Node f = n[0];
  Node A = n[1];
  // Skip y if some element x of A is already known to map to y.
  //
  // Since f is injective, x is then the only preimage of y, so the skolem
  // below would be equal to x and the inference it is used in would restate
  // a constraint mapUpInjective already generates for x. This is sound only
  // because f is injective: for an arbitrary f the multiplicity of y in
  // (bag.map f A) is the sum of the multiplicities of its whole preimage, so
  // a single witness does not discharge it.
  bool preimageFound = false;
  const std::set<Node>& aElements = d_state->getElements(A);
  for (const Node& x : aElements)
  {
    if (d_state->areEqual(mkApplyFunction(f, x), y))
    {
      preimageFound = true;
      break;
    }
  }
  if (preimageFound)
  {
    inferInfo.d_conclusion = d_true;
    return inferInfo;
  }

  // declare a fresh skolem of type T
  Node x =
      d_sm->mkSkolemFunction(SkolemId::BAGS_MAP_PREIMAGE_INJECTIVE, {f, A, y});

  Node mapSkolem = registerAndAssertSkolemLemma(n);
  Node countY = getMultiplicityTerm(y, mapSkolem);
  Node countX = getMultiplicityTerm(x, A);

  Node f_x = mkApplyFunction(f, x);
  Node y_equals_f_x = y.eqNode(f_x);

  // Since f is injective, x is the only candidate preimage of y. So the
  // multiplicity of y in (bag.map f A) is the multiplicity of x in A when x is
  // a preimage of y, and zero otherwise. Stating this as an equality, rather
  // than only constraining the case (>= (bag.count y skolem) 1), lets the
  // multiplicity of y be propagated directly.
  Node ite = d_nm->mkNode(Kind::ITE, y_equals_f_x, countX, d_zero);
  inferInfo.d_conclusion = countY.eqNode(ite);

  Trace("bags::InferenceGenerator::mapDown")
      << "conclusion: " << inferInfo.d_conclusion << std::endl;
  return inferInfo;
}

InferInfo InferenceGenerator::mapUpInjective(Node n, Node x)
{
  Assert(n.getKind() == Kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_UP_INJECTIVE);
  Node f = n[0];
  Node A = n[1];

  Node countA = getMultiplicityTerm(x, A);
  registerCountTerm(countA);
  Node f_x = mkApplyFunction(f, x);
  Node mapSkolem = registerAndAssertSkolemLemma(n);
  Node countN = getMultiplicityTerm(f_x, mapSkolem);
  registerCountTerm(countN);
  inferInfo.d_conclusion = countA.eqNode(countN);
  return inferInfo;
}

InferInfo InferenceGenerator::mapUp1(Node n, Node x)
{
  Assert(n.getKind() == Kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_UP1);
  Node f = n[0];
  Node A = n[1];

  Node countA = getMultiplicityTerm(x, A);
  registerCountTerm(countA);
  Node f_x = d_nm->mkNode(Kind::APPLY_UF, f, x);
  Node mapSkolem = registerAndAssertSkolemLemma(n);
  Node countN = getMultiplicityTerm(f_x, mapSkolem);
  registerCountTerm(countN);
  Node leq = d_nm->mkNode(Kind::LEQ, countA, countN);
  inferInfo.d_conclusion = leq;
  return inferInfo;
}

InferInfo InferenceGenerator::mapUp2(Node n, Node uf, Node size, Node y, Node x)
{
  Assert(n.getKind() == Kind::BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_UP2);
  Node f = n[0];
  Node A = n[1];

  Node countA = getMultiplicityTerm(x, A);
  Node xInA = d_nm->mkNode(Kind::GEQ, countA, d_one);
  Node notEqual =
      d_nm->mkNode(Kind::EQUAL, d_nm->mkNode(Kind::APPLY_UF, f, x), y).negate();

  Node k =
      d_sm->mkSkolemFunction(SkolemId::BAGS_MAP_INDEX, {n, uf, size, y, x});
  Node inRange = d_nm->mkNode(
      Kind::AND,
      {d_nm->mkNode(Kind::GEQ, k, d_one), d_nm->mkNode(Kind::LEQ, k, size)});
  Node equal =
      d_nm->mkNode(Kind::EQUAL, d_nm->mkNode(Kind::APPLY_UF, uf, k), x);
  Node andNode = d_nm->mkNode(Kind::AND, inRange, equal);
  Node orNode = d_nm->mkNode(Kind::OR, notEqual, andNode);
  Node implies = d_nm->mkNode(Kind::IMPLIES, xInA, orNode);
  inferInfo.d_conclusion = implies;
  return inferInfo;
}

InferInfo InferenceGenerator::filterDown(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_FILTER && n[1].getType().isBag());
  AssertEqual(e.getType(), n[1].getType().getBagElementType());

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_DOWN);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node member = d_nm->mkNode(Kind::GEQ, count, d_one);
  Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, e);
  Node equal = count.eqNode(countA);

  inferInfo.d_conclusion = pOfe.andNode(equal);
  inferInfo.d_premises.push_back(member);
  return inferInfo;
}

InferInfo InferenceGenerator::filterUp(Node n, Node e)
{
  Assert(n.getKind() == Kind::BAG_FILTER && n[1].getType().isBag());
  AssertEqual(e.getType(), n[1].getType().getBagElementType());

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_UP);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node member = d_nm->mkNode(Kind::GEQ, countA, d_one);
  Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, e);
  Node equal = count.eqNode(countA);
  Node included = pOfe.andNode(equal);
  Node equalZero = count.eqNode(d_zero);
  Node excluded = pOfe.notNode().andNode(equalZero);
  inferInfo.d_conclusion = included.orNode(excluded);
  inferInfo.d_premises.push_back(member);
  return inferInfo;
}

InferInfo InferenceGenerator::productUp(Node n, Node e1, Node e2)
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  Node A = n[0];
  Node B = n[1];
  Node tuple = BagsUtils::constructProductTuple(n, e1, e2);

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_UP);

  Node countA = getMultiplicityTerm(e1, A);
  Node countB = getMultiplicityTerm(e2, B);

  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, countA, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, countB, d_one));

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(tuple, skolem);

  Node multiply = d_nm->mkNode(Kind::MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

InferInfo InferenceGenerator::productDown(Node n, Node e)
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  AssertEqual(e.getType(), n.getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];

  TypeNode tupleBType = B.getType().getBagElementType();
  TypeNode tupleAType = A.getType().getBagElementType();
  size_t tupleALength = tupleAType.getTupleLength();
  size_t productTupleLength = n.getType().getBagElementType().getTupleLength();

  std::vector<Node> elements = TupleUtils::getTupleElements(e);
  Node a = TupleUtils::constructTupleFromElements(
      tupleAType, elements, 0, tupleALength - 1);
  Node b = TupleUtils::constructTupleFromElements(
      tupleBType, elements, tupleALength, productTupleLength - 1);

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_DOWN);

  Node countA = getMultiplicityTerm(a, A);
  Node countB = getMultiplicityTerm(b, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count, d_one));

  Node multiply = d_nm->mkNode(Kind::MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

InferInfo InferenceGenerator::joinUp(Node n, Node e1, Node e2)
{
  Assert(n.getKind() == Kind::TABLE_JOIN);
  Node A = n[0];
  Node B = n[1];
  Node tuple = BagsUtils::constructProductTuple(n, e1, e2);

  std::vector<Node> aElements = TupleUtils::getTupleElements(e1);
  std::vector<Node> bElements = TupleUtils::getTupleElements(e2);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_UP);

  for (size_t i = 0; i < indices.size(); i += 2)
  {
    Node x = aElements[indices[i]];
    Node y = bElements[indices[i + 1]];
    Node equal = x.eqNode(y);
    inferInfo.d_premises.push_back(equal);
  }

  Node countA = getMultiplicityTerm(e1, A);
  Node countB = getMultiplicityTerm(e2, B);

  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, countA, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, countB, d_one));

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(tuple, skolem);

  Node multiply = d_nm->mkNode(Kind::MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);
  return inferInfo;
}

InferInfo InferenceGenerator::joinDown(Node n, Node e)
{
  Assert(n.getKind() == Kind::TABLE_JOIN);
  AssertEqual(e.getType(), n.getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];

  TypeNode tupleBType = B.getType().getBagElementType();
  TypeNode tupleAType = A.getType().getBagElementType();
  size_t tupleALength = tupleAType.getTupleLength();
  size_t productTupleLength = n.getType().getBagElementType().getTupleLength();

  std::vector<Node> elements = TupleUtils::getTupleElements(e);
  Node a = TupleUtils::constructTupleFromElements(
      tupleAType, elements, 0, tupleALength - 1);
  Node b = TupleUtils::constructTupleFromElements(
      tupleBType, elements, tupleALength, productTupleLength - 1);

  InferInfo inferInfo(d_im, InferenceId::TABLES_JOIN_DOWN);

  Node countA = getMultiplicityTerm(a, A);
  Node countB = getMultiplicityTerm(b, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count, d_one));

  Node multiply = d_nm->mkNode(Kind::MULT, countA, countB);
  Node multiplicityConstraint = count.eqNode(multiply);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();
  Node joinConstraints = d_true;
  for (size_t i = 0; i < indices.size(); i += 2)
  {
    Node x = elements[indices[i]];
    Node y = elements[tupleALength + indices[i + 1]];
    Node equal = x.eqNode(y);
    joinConstraints = joinConstraints.andNode(equal);
  }
  inferInfo.d_conclusion = joinConstraints.andNode(multiplicityConstraint);

  return inferInfo;
}

InferInfo InferenceGenerator::groupNotEmpty(Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);

  TypeNode bagType = n.getType();
  Node A = n[0];
  Node emptyPart = d_nm->mkConst(EmptyBag(A.getType()));
  Node skolem = registerAndAssertSkolemLemma(n);
  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_NOT_EMPTY);
  Node A_isEmpty = A.eqNode(emptyPart);
  inferInfo.d_premises.push_back(A_isEmpty);
  Node singleton = d_nm->mkNode(Kind::BAG_MAKE, emptyPart, d_one);
  Node groupIsSingleton = skolem.eqNode(singleton);

  inferInfo.d_conclusion = groupIsSingleton;
  return inferInfo;
}

InferInfo InferenceGenerator::groupUp1(Node n, Node x, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(x.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_UP1);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node x_member_A = d_nm->mkNode(Kind::GEQ, count_x_A, d_one);
  inferInfo.d_premises.push_back(x_member_A);

  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);

  Node count_x_part_x = getMultiplicityTerm(x, part_x);

  Node sameMultiplicity = count_x_part_x.eqNode(count_x_A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_part_x = getMultiplicityTerm(part_x, skolem);
  Node part_x_member = d_nm->mkNode(Kind::EQUAL, count_part_x, d_one);

  Node emptyPart = d_nm->mkConst(EmptyBag(bagType));
  Node count_emptyPart = getMultiplicityTerm(emptyPart, skolem);
  Node emptyPart_not_member = count_emptyPart.eqNode(d_zero);

  inferInfo.d_conclusion = d_nm->mkNode(
      Kind::AND, {sameMultiplicity, part_x_member, emptyPart_not_member});
  return inferInfo;
}

InferInfo InferenceGenerator::groupUp2(Node n, Node x, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(x.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_UP2);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node x_not_in_A = d_nm->mkNode(Kind::EQUAL, count_x_A, d_zero);
  inferInfo.d_premises.push_back(x_not_in_A);

  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_x_is_empty = part_x.eqNode(d_nm->mkConst(EmptyBag(bagType)));
  inferInfo.d_conclusion = part_x_is_empty;
  return inferInfo;
}

InferInfo InferenceGenerator::groupDown(Node n, Node B, Node x, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(B.getType(), n.getType().getBagElementType());
  AssertEqual(x.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_DOWN);
  Node count_x_B = getMultiplicityTerm(x, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_x_B, d_one));
  Node count_x_A = getMultiplicityTerm(x, A);
  Node sameMultiplicity = count_x_B.eqNode(count_x_A);
  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion =
      d_nm->mkNode(Kind::AND, sameMultiplicity, part_x_is_B);
  return inferInfo;
}

InferInfo InferenceGenerator::groupPartCount(Node n, Node B, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(B.getType(), n.getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();
  Node empty = d_nm->mkConst(EmptyBag(bagType));

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_PART_COUNT);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_B_n, d_one));
  Node A_notEmpty = A.eqNode(empty).notNode();
  inferInfo.d_premises.push_back(A_notEmpty);

  Node x = d_sm->mkSkolemFunction(SkolemId::TABLES_GROUP_PART_ELEMENT, {n, B});
  d_state->registerPartElementSkolem(n, x);
  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node B_is_part_x = B.eqNode(part_x);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node sameMultiplicity = count_x_A.eqNode(count_x_B);
  Node x_in_B = d_nm->mkNode(Kind::GEQ, count_x_B, d_one);
  Node count_B_n_is_one = count_B_n.eqNode(d_one);
  inferInfo.d_conclusion = d_nm->mkNode(Kind::AND,
                                        {
                                            count_B_n_is_one,
                                            B_is_part_x,
                                            x_in_B,
                                            sameMultiplicity,
                                        });
  return inferInfo;
}

InferInfo InferenceGenerator::groupSameProjection(
    Node n, Node B, Node x, Node y, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(B.getType(), n.getType().getBagElementType());
  AssertEqual(x.getType(), n[0].getType().getBagElementType());
  AssertEqual(y.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_SAME_PROJECTION);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node count_y_B = getMultiplicityTerm(y, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);

  // premises
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_x_B, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_y_B, d_one));
  inferInfo.d_premises.push_back(x.eqNode(y).notNode());

  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  Node xProjection = TupleUtils::getTupleProjection(indices, x);
  Node yProjection = TupleUtils::getTupleProjection(indices, y);
  Node sameProjection = xProjection.eqNode(yProjection);
  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_y = d_nm->mkNode(Kind::APPLY_UF, part, y);
  part_y = registerAndAssertSkolemLemma(part_y);
  Node samePart = part_x.eqNode(part_y);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion =
      d_nm->mkNode(Kind::AND, sameProjection, samePart, part_x_is_B);
  return inferInfo;
}

InferInfo InferenceGenerator::groupSamePart(
    Node n, Node B, Node x, Node y, Node part)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  AssertEqual(B.getType(), n.getType().getBagElementType());
  AssertEqual(x.getType(), n[0].getType().getBagElementType());
  AssertEqual(y.getType(), n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_SAME_PART);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node count_y_A = getMultiplicityTerm(y, A);
  Node count_y_B = getMultiplicityTerm(y, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  Node xProjection = TupleUtils::getTupleProjection(indices, x);
  Node yProjection = TupleUtils::getTupleProjection(indices, y);

  // premises
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_x_B, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(Kind::GEQ, count_y_A, d_one));
  inferInfo.d_premises.push_back(x.eqNode(y).notNode());
  inferInfo.d_premises.push_back(xProjection.eqNode(yProjection));

  Node sameMultiplicity = count_y_B.eqNode(count_y_A);
  Node part_x = d_nm->mkNode(Kind::APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_y = d_nm->mkNode(Kind::APPLY_UF, part, y);
  part_y = registerAndAssertSkolemLemma(part_y);
  Node samePart = part_x.eqNode(part_y);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion =
      d_nm->mkNode(Kind::AND, sameMultiplicity, samePart, part_x_is_B);

  return inferInfo;
}

Node InferenceGenerator::defineSkolemPartFunction(Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  Node A = n[0];
  TypeNode tableType = A.getType();
  TypeNode elementType = tableType.getBagElementType();

  // declare an uninterpreted function part: T -> (Table T)
  Node part = d_sm->mkSkolemFunction(SkolemId::TABLES_GROUP_PART, {n});
  return part;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "theory/bags/bag_solver.h"

#include "expr/emptybag.h"
#include "options/bags_options.h"
#include "theory/bags/bag_reduction.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/uf/equality_engine_iterator.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

BagSolver::BagSolver(Env& env, SolverState& s, InferenceManager& im)
    : EnvObj(env),
      d_state(s),
      d_folds(context()),
      d_ig(env, &s, &im),
      d_im(im),
      d_mapCache(userContext())
{
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::checkBasicOperations()
{
  checkDisequalBagTerms();
  checkFolds();

  // At this point, all bag and count representatives should be in the solver
  // state.
  for (const Node& bag : d_state.getBags())
  {
    // iterate through all bags terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::BAG_EMPTY: checkEmpty(n); break;
        case Kind::BAG_MAKE: checkBagMake(n); break;
        case Kind::BAG_UNION_DISJOINT: checkUnionDisjoint(n); break;
        case Kind::BAG_UNION_MAX: checkUnionMax(n); break;
        case Kind::BAG_INTER_MIN: checkIntersectionMin(n); break;
        case Kind::BAG_DIFFERENCE_SUBTRACT: checkDifferenceSubtract(n); break;
        case Kind::BAG_DIFFERENCE_REMOVE: checkDifferenceRemove(n); break;
        case Kind::BAG_SETOF: checkSetof(n); break;
        case Kind::BAG_FILTER: checkFilter(n); break;
        case Kind::TABLE_PRODUCT: checkProduct(n); break;
        case Kind::TABLE_JOIN: checkJoin(n); break;
        case Kind::TABLE_GROUP: checkGroup(n); break;
        default: break;
      }
      it++;
    }
  }

  // add non negative constraints for all multiplicities
  for (const Node& n : d_state.getBags())
  {
    for (const Node& e : d_state.getElements(n))
    {
      checkNonNegativeCountTerms(n, d_state.getRepresentative(e));
    }
  }
}

void BagSolver::checkQuantifiedOperations()
{
  for (const Node& bag : d_state.getBags())
  {
    // iterate through all bags terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::BAG_MAP: checkMap(n); break;
        default: break;
      }
      it++;
    }
  }

  // add non negative constraints for all multiplicities
  for (const Node& n : d_state.getBags())
  {
    for (const Node& e : d_state.getElements(n))
    {
      checkNonNegativeCountTerms(n, d_state.getRepresentative(e));
    }
  }
}

set<Node> BagSolver::getElementsForBinaryOperator(const Node& n)
{
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards0 = d_state.getElements(n[0]);
  const set<Node>& upwards1 = d_state.getElements(n[1]);

  set_union(downwards.begin(),
            downwards.end(),
            upwards0.begin(),
            upwards0.end(),
            inserter(elements, elements.begin()));
  elements.insert(upwards1.begin(), upwards1.end());
  return elements;
}

void BagSolver::checkEmpty(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_EMPTY);
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.empty(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionDisjoint(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionMax(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkIntersectionMin(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.intersection(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceSubtract(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

bool BagSolver::checkBagMake()
{
  bool sentLemma = false;
  for (const Node& bag : d_state.getBags())
  {
    TypeNode bagType = bag.getType();
    NodeManager* nm = nodeManager();
    Node empty = nm->mkConst(EmptyBag(bagType));
    if (d_state.areEqual(empty, bag) || d_state.areDisequal(empty, bag))
    {
      continue;
    }

    // look for BAG_MAKE terms in the equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      if (n.getKind() == Kind::BAG_MAKE)
      {
        Trace("bags-check") << "splitting on node " << std::endl;
        InferInfo i = d_ig.bagMake(n);
        sentLemma |= d_im.lemmaTheoryInference(&i);
        // it is enough to split only once per equivalent class
        break;
      }
      it++;
    }
  }
  return sentLemma;
}

void BagSolver::checkBagMake(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  Trace("bags::BagSolver::postCheck")
      << "BagSolver::checkBagMake Elements of " << n
      << " are: " << d_state.getElements(n) << std::endl;
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.bagMake(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}
void BagSolver::checkNonNegativeCountTerms(const Node& bag, const Node& element)
{
  InferInfo i = d_ig.nonNegativeCount(bag, element);
  d_im.lemmaTheoryInference(&i);
}

void BagSolver::checkDifferenceRemove(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceRemove(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkSetof(Node n)
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[0]);

  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.setof(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDisequalBagTerms()
{
  for (const auto& [equality, witness] : d_state.getDisequalBagTerms())
  {
    if (options().bags.bagsDeqDecompose)
    {
      InferInfo pointwise = d_ig.bagDisequalityPointwise(equality);
      if (!pointwise.d_conclusion.isNull())
      {
        d_im.lemmaTheoryInference(&pointwise);
      }
      InferInfo decompose = d_ig.bagDisequalityDecompose(equality);
      if (!decompose.d_conclusion.isNull())
      {
        // two applications of one operator differ only where some arguments
        // differ: case split on those first. The element witness lemma, which
        // reduces both sides to multiplicities, waits until a model is about
        // to be reported (checkDisequalBagTermsLastCall), since for an
        // equivalence proof the case split alone closes every branch
        d_im.lemmaTheoryInference(&decompose);
        continue;
      }
    }
    InferInfo info = d_ig.bagDisequality(equality, witness);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::registerFold(Node n)
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  d_folds.push_back(n);
}

Node BagSolver::countLemma(const Node& fold)
{
  Node f = uf::FunctionConst::getDefinition(fold[0]);
  if (f.isNull() || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2)
  {
    return Node::null();
  }
  NodeManager* nm = nodeManager();
  Node a = f[0][1];
  Node body = f[1];
  Node seed = fold[1];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  Node empty = nm->mkConst(EmptyBag(fold[2].getType()));
  auto isIncrement = [&](const Node& t, const Node& acc) {
    return t.getKind() == Kind::ADD && t.getNumChildren() == 2
           && ((t[0] == acc && t[1] == one) || (t[1] == acc && t[0] == one));
  };
  if (isIncrement(body, a) && seed == zero)
  {
    // (and (>= F 0) (= (= F 0) (= X (as bag.empty (Bag T)))))
    return nm->mkNode(Kind::AND,
                      nm->mkNode(Kind::GEQ, fold, zero),
                      fold.eqNode(zero).eqNode(fold[2].eqNode(empty)));
  }
  // (nullable.some (+ (nullable.val a) 1)) from (nullable.some 0), where
  // (nullable.val a) is the selector of a's constructor, sel below
  if (body.getKind() == Kind::APPLY_CONSTRUCTOR && body.getNumChildren() == 1
      && seed.getKind() == Kind::APPLY_CONSTRUCTOR
      && seed.getOperator() == body.getOperator() && seed.getNumChildren() == 1
      && seed[0] == zero && body[0].getKind() == Kind::ADD
      && body[0].getNumChildren() == 2)
  {
    Node inc = body[0];
    for (size_t k = 0; k < 2; k++)
    {
      Node sel = inc[k];
      if (inc[1 - k] == one && sel.getKind() == Kind::APPLY_SELECTOR
          && sel[0] == a)
      {
        Node value = nm->mkNode(Kind::APPLY_SELECTOR, sel.getOperator(), fold);
        Node some =
            nm->mkNode(Kind::APPLY_CONSTRUCTOR, body.getOperator(), value);
        return nm->mkNode(Kind::AND,
                          fold.eqNode(some),
                          nm->mkNode(Kind::GEQ, value, zero),
                          value.eqNode(zero).eqNode(fold[2].eqNode(empty)));
      }
    }
  }
  return Node::null();
}

void BagSolver::checkFolds()
{
  if (!options().bags.bagsLazyFold)
  {
    return;
  }
  for (size_t i = 0, n = d_folds.size(); i < n; i++)
  {
    Node fold = d_folds[i];
    if (!d_countedFolds.insert(fold).second)
    {
      continue;
    }
    Node lemma = countLemma(fold);
    if (!lemma.isNull())
    {
      d_im.lemma(lemma, InferenceId::BAGS_FOLD_COUNT);
    }
  }
  for (size_t i = 0, n = d_folds.size(); i < n; i++)
  {
    for (size_t j = i + 1; j < n; j++)
    {
      Node a = d_folds[i];
      Node b = d_folds[j];
      if (a.getType() != b.getType() || a[2].getType() != b[2].getType()
          || (a[0] == b[0] && a[1] == b[1]))
      {
        // folds of different types never meet, and folds over bags of
        // different element types have no argument-wise relation; folds with
        // one function and one initial value over equal bags are equal by
        // congruence
        continue;
      }
      std::pair<Node, Node> key =
          a < b ? std::make_pair(a, b) : std::make_pair(b, a);
      if (!d_foldPairs.insert(key).second)
      {
        continue;
      }
      InferInfo info = d_ig.foldDecompose(key.first, key.second);
      d_im.lemmaTheoryInference(&info);
    }
  }
}

void BagSolver::reduceFoldsLastCall()
{
  if (!options().bags.bagsLazyFold)
  {
    return;
  }
  for (size_t i = 0, n = d_folds.size(); i < n; i++)
  {
    Node fold = d_folds[i];
    if (!d_reducedFolds.insert(fold).second)
    {
      continue;
    }
    std::vector<Node> asserts;
    Node ret = BagReduction::reduceFoldOperator(fold, asserts);
    asserts.push_back(fold.eqNode(ret));
    Node lemma = nodeManager()->mkNode(Kind::AND, asserts);
    d_im.lemma(lemma, InferenceId::BAGS_FOLD);
  }
}

void BagSolver::checkDisequalBagTermsLastCall()
{
  if (!options().bags.bagsDeqDecompose)
  {
    return;
  }
  for (const auto& [equality, witness] : d_state.getDisequalBagTerms())
  {
    InferInfo decompose = d_ig.bagDisequalityDecompose(equality);
    if (decompose.d_conclusion.isNull())
    {
      continue;
    }
    InferInfo info = d_ig.bagDisequality(equality, witness);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::checkMap(Node n)
{
  Assert(n.getKind() == Kind::BAG_MAP);
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  if (d_state.isInjective(n[0]))
  {
    for (const Node& z : downwards)
    {
      InferInfo upInference = d_ig.mapDownInjective(n, z);
      d_im.lemmaTheoryInference(&upInference);
    }
    for (const Node& x : upwards)
    {
      InferInfo upInference = d_ig.mapUpInjective(n, x);
      d_im.lemmaTheoryInference(&upInference);
    }
  }
  else
  {
    for (const Node& x : upwards)
    {
      InferInfo upInference = d_ig.mapUp1(n, x);
      d_im.lemmaTheoryInference(&upInference);
    }

    for (const Node& z : downwards)
    {
      if (!options().bags.bagsMapWitness)
      {
        break;
      }
      // first the cheap ground witness, which refutes most of what the
      // quantified preimage sum below would
      InferInfo witness = d_ig.mapDownWitness(n, z);
      if (witness.d_conclusion != d_true)
      {
        d_im.lemmaTheoryInference(&witness);
      }
    }
    for (const Node& z : downwards)
    {
      Node y = d_state.getRepresentative(z);
      if (!d_mapCache.count(n))
      {
        std::shared_ptr<context::CDHashMap<Node, std::pair<Node, Node>>> nMap =
            std::make_shared<context::CDHashMap<Node, std::pair<Node, Node>>>(
                userContext());
        d_mapCache[n] = nMap;
      }
      if (!d_mapCache[n].get()->count(y))
      {
        auto [downInference, uf, preImageSize] = d_ig.mapDown(n, y);
        d_im.lemmaTheoryInference(&downInference);
        std::pair<Node, Node> yPair = std::make_pair(uf, preImageSize);
        d_mapCache[n].get()->insert(y, yPair);
      }

      context::CDHashMap<Node, std::pair<Node, Node>>::iterator it =
          d_mapCache[n].get()->find(y);

      auto [uf, preImageSize] = it->second;

      for (const Node& x : upwards)
      {
        InferInfo upInference = d_ig.mapUp2(n, uf, preImageSize, y, x);
        d_im.lemmaTheoryInference(&upInference);
      }
    }
  }
}

void BagSolver::checkFilter(Node n)
{
  Assert(n.getKind() == Kind::BAG_FILTER);

  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterUp(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkProduct(Node n)
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.productUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.productDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkJoin(Node n)
{
  Assert(n.getKind() == Kind::TABLE_JOIN);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.joinUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.joinDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkGroup(Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);

  InferInfo notEmpty = d_ig.groupNotEmpty(n);
  d_im.lemmaTheoryInference(&notEmpty);

  Node part = d_ig.defineSkolemPartFunction(n);

  const set<Node>& elementsA = d_state.getElements(n[0]);
  std::shared_ptr<context::CDHashSet<Node>> skolems =
      d_state.getPartElementSkolems(n);
  for (const Node& a : elementsA)
  {
    if (skolems->contains(a))
    {
      // skip skolem elements that were introduced by groupPartCount below.
      continue;
    }
    Node aRep = d_state.getRepresentative(a);
    InferInfo i = d_ig.groupUp1(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
    i = d_ig.groupUp2(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
  }

  std::set<Node> parts = d_state.getElements(n);
  for (std::set<Node>::iterator partIt1 = parts.begin(); partIt1 != parts.end();
       ++partIt1)
  {
    Node part1 = d_state.getRepresentative(*partIt1);
    std::vector<Node> partEqc;
    d_state.getEquivalenceClass(part1, partEqc);
    bool newPart = true;
    for (Node p : partEqc)
    {
      if (p.getKind() == Kind::APPLY_UF && p.getOperator() == part)
      {
        newPart = false;
      }
    }
    if (newPart)
    {
      // only apply the groupPartCount rule for a part that does not have
      // nodes of the form (part x) introduced by the group up rule above.
      InferInfo partCardinality = d_ig.groupPartCount(n, part1, part);
      d_im.lemmaTheoryInference(&partCardinality);
    }

    std::set<Node> partElements = d_state.getElements(part1);
    for (std::set<Node>::iterator i = partElements.begin();
         i != partElements.end();
         ++i)
    {
      Node x = d_state.getRepresentative(*i);
      if (!skolems->contains(x))
      {
        // only apply down rules for elements not generated by groupPartCount
        // rule above
        InferInfo down = d_ig.groupDown(n, part1, x, part);
        d_im.lemmaTheoryInference(&down);
      }

      std::set<Node>::iterator j = i;
      ++j;
      while (j != partElements.end())
      {
        Node y = d_state.getRepresentative(*j);
        // x, y should have the same projection
        InferInfo sameProjection =
            d_ig.groupSameProjection(n, part1, x, y, part);
        d_im.lemmaTheoryInference(&sameProjection);
        ++j;
      }

      for (const Node& a : elementsA)
      {
        Node y = d_state.getRepresentative(a);
        if (x != y)
        {
          // x, y should have the same projection
          InferInfo samePart = d_ig.groupSamePart(n, part1, x, y, part);
          d_im.lemmaTheoryInference(&samePart);
        }
      }
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

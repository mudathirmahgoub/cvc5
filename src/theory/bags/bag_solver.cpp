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

#include <limits>
#include <unordered_set>

#include "expr/bound_var_manager.h"
#include "expr/emptybag.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/bags_options.h"
#include "options/smt_options.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/incomplete_id.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_model.h"
#include "theory/uf/equality_engine_iterator.h"
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
      d_ig(env, &s, &im, options().bags.bagsToLiastar),
      d_im(im),
      d_mapCache(userContext()),
      d_liastarElements(userContext(), 0)
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

void BagSolver::checkLiastarConstraints()
{
  if (!options().bags.bagsToLiastar)
  {
    return;
  }
  // Both maps are state of this check, not caches. The keys of d_bagBoundVars
  // are the bags the star ranges over, and they must be the bags of the
  // current context: these maps are plain maps, so they would never shrink on
  // backtracking, and every later star would carry the bags of the branches
  // that were abandoned in between. The values of d_cardinalityVars depend on
  // the context as well, since getCardinalityVar reuses the skolem that the
  // current context registered for (bag.card bag), and the cardinality terms
  // of the state are themselves collected afresh by TheoryBags::initialize,
  // under the representatives of the current context.
  d_cardinalityVars.clear();
  d_bagBoundVars.clear();
  d_lastSlots.clear();
  d_lastBody = Node::null();
  d_lastPremises.clear();
  d_lastSums.clear();
  d_groupColumns.clear();

  eq::EqualityEngine* ee = d_state.getEqualityEngine();

  // The bag atoms are literals of the current context, so the positive top
  // level atoms are the equalities in the equivalence class of true, and the
  // non top level atoms of step 1 are the equalities in the equivalence class
  // of false.
  std::vector<Node> equalities;
  std::vector<Node> disequalities;
  eq::EqClassIterator trueIt = eq::EqClassIterator(d_true, ee);
  while (!trueIt.isFinished())
  {
    Node n = (*trueIt);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isBag())
    {
      equalities.push_back(n);
    }
    ++trueIt;
  }
  eq::EqClassIterator falseIt = eq::EqClassIterator(d_false, ee);
  while (!falseIt.isFinished())
  {
    Node n = (*falseIt);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isBag())
    {
      disequalities.push_back(n);
    }
    ++falseIt;
  }
  const std::map<Node, Node>& cardTerms = d_state.getCardinalityTerms();
  Trace("bags-liastar") << "equalities: " << equalities << std::endl;
  Trace("bags-liastar") << "disequalities: " << disequalities << std::endl;
  if (cardTerms.empty())
  {
    // Nothing to translate. Without a cardinality term the star could only
    // restate, at every element, the pointwise facts that the element-wise
    // rules of the theory derive anyway, and its cost grows with the number
    // of bag terms: a SQL equivalence query with 87 bag terms and no
    // cardinality spends the whole time limit in the liastar check, where the
    // element-wise rules refute it in 0.1s. The cardinality terms that the
    // translation itself introduces (mapCard, mapDown) are only introduced
    // once one is present, so this is a check on the input and the fold
    // reduction, see checkMap and InferenceGenerator::mapDown.
    return;
  }

  // the bags of the positive atoms need slots in the star, and so do the bags
  // whose cardinality the input constrains, even when they occur in no atom:
  // the star is the only thing that relates a cardinality term to the bag it
  // is the cardinality of
  for (const Node& equality : equalities)
  {
    Node a;
    Node b;
    if (isInclusionAtom(equality, a, b))
    {
      // the difference term needs no slot, see isInclusionAtom
      getBagBoundVar(a);
      getBagBoundVar(b);
      continue;
    }
    getBagBoundVar(equality[0]);
    getBagBoundVar(equality[1]);
  }
  for (const std::pair<const Node, Node>& pair : cardTerms)
  {
    Assert(pair.first.getKind() == Kind::BAG_CARD);
    getBagBoundVar(pair.first[0]);
  }
  // step 1: move the negated atoms out of the star. This introduces the
  // difference bags, which get their slots here so that step 3 below sees
  // them.
  for (const Node& disequality : disequalities)
  {
    evictNegatedAtom(disequality);
  }
  // step 3
  addCardinalityVars();
  // the constraints of the constructed bags, which Figure 4 does not cover
  addBagMakeCardinalities();
  if (options().bags.bagsLiastarModel
      == options::BagsLiastarModelMode::SUBSOLVER)
  {
    // the star assumes an element for every row it needs, which a finite
    // element type may not have, see the documentation of this method
    for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
    {
      if (d_env.isFiniteType(pair.first.getType().getBagElementType()))
      {
        d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_FINITE_ELEMENTS);
        break;
      }
    }
  }
  // step 4
  std::vector<Node> premises;
  Node star = buildStar(equalities, premises);
  // Part of the body only holds in the contexts the conjuncts were read from,
  // and buildStar collected those contexts in premises. The star must be
  // guarded by them: a lemma is asserted at the assertion level, not at the
  // current decision level, so an unguarded star would keep forcing
  // (= c_A c_B) at every element in the branches where A and B are not equal,
  // which would refute satisfiable inputs. The negated atoms need no guard
  // here since they contribute nothing to the body; each of them is asserted
  // by its own guarded lemma in evictNegatedAtom above.
  Node lemma =
      premises.empty() ? star : nodeManager()->mkAnd(premises).impNode(star);
  Trace("bags-liastar") << "lemma: " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
}

Node BagSolver::getRowCount(const Node& e, const Node& bag)
{
  if (bag.getType().getBagElementType() != e.getType())
  {
    return d_zero;
  }
  NodeManager* nm = nodeManager();
  Node count = nm->mkNode(Kind::BAG_COUNT, e, bag);
  Node r = d_state.getRepresentative(bag);
  for (const std::pair<Node, Node>& pair : d_state.getElementCountPairs(r))
  {
    if (pair.first == e)
    {
      // the theory knows this count, and the row has to be tied to it
      return count;
    }
  }
  if (options().bags.bagsLiastarModel == options::BagsLiastarModelMode::ELEMENTS
      && Theory::isLeafOf(bag, TheoryId::THEORY_BAGS))
  {
    // the elements mode builds the leaves from the count terms the theory
    // has, so the known elements need theirs in every leaf
    return count;
  }
  // A count term the theory does not have yet would make it run its
  // element-wise rules for e in bag, which the star does not need and which
  // are expensive when the bags are many, e.g. the bags of a fold reduction,
  // or when the operator is bag.map or a table operator. A variable that
  // stands for the count is enough for the row, and the purification skolem of
  // the count term is the very variable the theory uses if it registers the
  // term later on. The model construction of the subsolver mode leaves such
  // counts to the subsolver.
  return nm->getSkolemManager()->mkPurifySkolem(count);
}

void BagSolver::collectLiastarModelValues(TheoryModel* m,
                                          std::map<Node, Node>& processedBags)
{
  if (d_lastSlots.empty())
  {
    // the last check translated nothing
    return;
  }
  if (options().bags.bagsLiastarModel
      == options::BagsLiastarModelMode::ELEMENTS)
  {
    // checkLiastarCandidateModel made the known elements add up to the
    // cardinalities during the search, or marked the model unsound
    return;
  }
  if (!d_groupColumns.empty())
  {
    // a fresh row of a group is a fresh element of the source of a map whose
    // image is the group; this construction does not invent such elements
    Trace("bags-liastar-model")
        << "give up: the star has group columns" << std::endl;
    d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_MODEL);
    return;
  }
  NodeManager* nm = nodeManager();
  size_t n = d_lastSlots.size();
  Trace("bags-liastar-model")
      << "rebuild the bags of " << n << " slots" << std::endl;

  // ---- the leaves are the bags the theory assigns a value to, and a slot
  // without a pointwise translation is where a fresh row cannot be read back
  std::vector<size_t> leaves;
  std::vector<bool> readable(n, true);
  for (size_t i = 0; i < n; i++)
  {
    const Node& bag = d_lastSlots[i];
    Kind k = bag.getKind();
    if (bag.isConst())
    {
      continue;
    }
    if (Theory::isLeafOf(bag, TheoryId::THEORY_BAGS))
    {
      leaves.push_back(i);
    }
    else if (!hasPointwiseTranslation(k) && k != Kind::BAG_MAKE)
    {
      readable[i] = false;
    }
  }
  if (leaves.empty())
  {
    return;
  }

  // ---- what the model assigns: the cardinality of every slot, and the count
  // of every known element in every slot. The known elements are the rows of
  // the lemma, one per representative.
  std::vector<Node> cards(n);
  for (size_t i = 0; i < n; i++)
  {
    Node x = d_cardinalityVars[d_lastSlots[i]];
    if (m->hasTerm(x))
    {
      Node v = m->getRepresentative(x);
      if (v.isConst())
      {
        cards[i] = v;
      }
    }
    Trace("bags-liastar-model")
        << "  slot " << d_lastSlots[i] << ": cardinality "
        << (cards[i].isNull() ? std::string("free") : cards[i].toString())
        << std::endl;
  }
  std::vector<Node> known;
  std::vector<std::map<size_t, Node>> knownCounts;
  for (size_t i = 0; i < n; i++)
  {
    Node r = d_state.getRepresentative(d_lastSlots[i]);
    for (const std::pair<Node, Node>& pair : d_state.getElementCountPairs(r))
    {
      Node e = d_state.getRepresentative(pair.first);
      Node c = m->hasTerm(pair.second) ? m->getRepresentative(pair.second)
                                       : Node::null();
      if (c.isNull() || !c.isConst())
      {
        Trace("bags-liastar-model")
            << "  give up: no value for the count of " << e << " in "
            << d_lastSlots[i] << std::endl;
        d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_MODEL);
        return;
      }
      size_t j = std::find(known.begin(), known.end(), e) - known.begin();
      if (j == known.size())
      {
        known.push_back(e);
        knownCounts.emplace_back();
      }
      knownCounts[j][i] = c;
    }
  }

  // a known element has count 0 in the slots of another element type, which
  // no count term states
  for (size_t j = 0, numKnown = known.size(); j < numKnown; j++)
  {
    TypeNode type = known[j].getType();
    for (size_t i = 0; i < n; i++)
    {
      if (d_lastSlots[i].getType().getBagElementType() != type)
      {
        knownCounts[j][i] = d_zero;
      }
    }
  }

  // ---- nothing to do when the known elements add up to the cardinalities:
  // the generic construction from them is exact
  bool exact = true;
  for (size_t i = 0; i < n && exact; i++)
  {
    if (cards[i].isNull())
    {
      continue;
    }
    Rational sum(0);
    for (size_t j = 0, numKnown = known.size(); j < numKnown && exact; j++)
    {
      std::map<size_t, Node>::iterator it = knownCounts[j].find(i);
      if (it == knownCounts[j].end())
      {
        // no count term, so whether the row adds up is for the subsolver
        exact = false;
      }
      else
      {
        sum += it->second.getConst<Rational>();
      }
    }
    exact = exact && sum == cards[i].getConst<Rational>();
  }
  if (exact)
  {
    Trace("bags-liastar-model")
        << "  the " << known.size() << " known elements add up" << std::endl;
    return;
  }

  // ---- the rows: those of the known elements, whose counts are fixed where
  // the model assigns them, and fresh ones, until the columns add up to the
  // cardinalities. A row of zeros satisfies the body, so a query with more
  // fresh rows subsumes one with fewer, and the number is doubled.
  std::vector<Node> boundVars;
  for (const Node& bag : d_lastSlots)
  {
    boundVars.push_back(d_bagBoundVars[bag]);
  }
  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.write_bags().bagsToLiastar = false;
  subOptions.write_smt().produceModels = true;
  SubsolverSetupInfo ssi(d_env, subOptions);
  // Removing the fresh rows that are zero in every slot with a cardinality
  // keeps a solution, and each other fresh row adds at least 1 to such a slot.
  // So fresh rows beyond the sum of the cardinalities are never needed.
  Rational cardinalitySum(0);
  for (const Node& c : cards)
  {
    if (!c.isNull())
    {
      cardinalitySum += c.getConst<Rational>();
    }
  }
  const Integer& total = cardinalitySum.getNumerator();
  const size_t maxFresh =
      total.fitsUnsignedInt() ? total.toUnsignedInt() : UINT32_MAX;
  std::vector<std::vector<Node>> rows;  // rows[j][i]: variable of row j, slot i
  std::vector<Node> rowValues;
  size_t fresh = 0;
  bool found = false;
  while (!found)
  {
    size_t numRows = known.size() + fresh;
    rows.assign(numRows, std::vector<Node>(n));
    std::vector<Node> conjuncts;
    std::vector<Node> vars;
    for (size_t j = 0; j < numRows; j++)
    {
      for (size_t i = 0; i < n; i++)
      {
        rows[j][i] = NodeManager::mkDummySkolem("row", nm->integerType());
        vars.push_back(rows[j][i]);
      }
      conjuncts.push_back(d_lastBody.substitute(
          boundVars.begin(), boundVars.end(), rows[j].begin(), rows[j].end()));
      if (j < known.size())
      {
        for (const std::pair<const size_t, Node>& ic : knownCounts[j])
        {
          conjuncts.push_back(rows[j][ic.first].eqNode(ic.second));
        }
      }
    }
    for (size_t i = 0; i < n; i++)
    {
      if (cards[i].isNull())
      {
        continue;
      }
      std::vector<Node> column;
      for (size_t j = 0; j < numRows; j++)
      {
        column.push_back(rows[j][i]);
      }
      Node sum = column.empty()       ? d_zero
                 : column.size() == 1 ? column[0]
                                      : nm->mkNode(Kind::ADD, column);
      conjuncts.push_back(sum.eqNode(cards[i]));
    }
    Node query = nm->mkAnd(conjuncts);
    rowValues.clear();
    Result r = checkWithSubsolver(query, vars, rowValues, ssi);
    Trace("bags-liastar-model") << "  " << known.size() << " known + " << fresh
                                << " fresh rows: " << r << std::endl;
    found = r.getStatus() == Result::SAT;
    if (!found)
    {
      if (fresh >= maxFresh)
      {
        d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_MODEL);
        return;
      }
      fresh = fresh == 0 ? 1 : 2 * fresh;
    }
  }
  size_t numRows = rows.size();
  if (fresh == 0)
  {
    // the known elements account for the cardinalities after all, e.g. with
    // the counts the model does not assign, and the generic construction from
    // them is exact
    return;
  }
  // ---- a fresh element cannot be read back into a bag without a pointwise
  // translation: its count there is not a function of its counts in the
  // leaves, and a count of 0 constrains it as much as a positive one, e.g.
  // (p e) has to be false for a filter. So give up when a fresh row occurs in
  // such a bag, or when a fresh element has the element type of such a bag or
  // of one of its arguments.
  std::set<TypeNode> freshTypes;
  for (size_t j = known.size(); j < numRows; j++)
  {
    for (size_t i : leaves)
    {
      if (rowValues[j * n + i].getConst<Rational>().sgn() > 0)
      {
        freshTypes.insert(d_lastSlots[i].getType().getBagElementType());
      }
    }
  }
  for (size_t i = 0; i < n; i++)
  {
    if (readable[i])
    {
      continue;
    }
    const Node& bag = d_lastSlots[i];
    bool occurs = freshTypes.count(bag.getType().getBagElementType()) > 0;
    for (const Node& child : bag)
    {
      if (child.getType().isBag()
          && freshTypes.count(child.getType().getBagElementType()) > 0)
      {
        occurs = true;
      }
    }
    for (size_t j = known.size(); j < numRows && !occurs; j++)
    {
      occurs = rowValues[j * n + i].getConst<Rational>().sgn() > 0;
    }
    if (occurs)
    {
      Trace("bags-liastar-model")
          << "  give up: a fresh element may occur in " << bag
          << ", which has no pointwise translation" << std::endl;
      d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_MODEL);
      return;
    }
  }

  // ---- one fresh element per fresh row and element type, and the leaves
  std::map<std::pair<size_t, TypeNode>, Node> freshElements;
  for (size_t i : leaves)
  {
    const Node& bag = d_lastSlots[i];
    Node r = d_state.getRepresentative(bag);
    if (processedBags.find(r) != processedBags.end())
    {
      continue;
    }
    TypeNode elementType = bag.getType().getBagElementType();
    std::map<Node, Node> elementCounts;
    for (size_t j = 0; j < numRows; j++)
    {
      Node c = rowValues[j * n + i];
      if (c.getConst<Rational>().sgn() <= 0)
      {
        continue;
      }
      Node e;
      if (j < known.size())
      {
        // a positive count only in a slot of its type, see knownCounts
        Assert(known[j].getType() == elementType);
        e = known[j];
      }
      else
      {
        std::pair<size_t, TypeNode> key(j, elementType);
        std::map<std::pair<size_t, TypeNode>, Node>::iterator it =
            freshElements.find(key);
        if (it == freshElements.end())
        {
          e = NodeManager::mkDummySkolem("bags_liastar_element", elementType);
          freshElements[key] = e;
        }
        else
        {
          e = it->second;
        }
      }
      elementCounts[e] = c;
    }
    Node value =
        BagsUtils::constructBagFromElements(bag.getType(), elementCounts);
    value = rewrite(value);
    Trace("bags-liastar-model") << "  " << bag << " := " << value << std::endl;
    m->assertEquality(value, bag, true);
    m->assertSkeleton(value);
    processedBags[r] = value;
  }
}

void BagSolver::checkLiastarCandidateModel()
{
  if (d_lastSlots.empty())
  {
    return;
  }
  NodeManager* nm = nodeManager();
  TheoryModel* m = d_state.getModel();
  size_t n = d_lastSlots.size();
  // the element types whose slots the known elements do not add up to
  std::set<TypeNode> types;
  for (size_t i = 0; i < n; i++)
  {
    Node x = m->getValue(d_cardinalityVars[d_lastSlots[i]]);
    Node sum = d_lastSums[i].isNull() ? d_zero : m->getValue(d_lastSums[i]);
    Trace("bags-liastar-model")
        << "candidate slot " << d_lastSlots[i] << ": cardinality " << x
        << ", known elements " << sum << std::endl;
    if (x != sum)
    {
      types.insert(d_lastSlots[i].getType().getBagElementType());
    }
  }
  if (types.empty())
  {
    return;
  }
  const size_t maxElements = 64;
  if (d_liastarElements.get() >= maxElements)
  {
    Trace("bags-liastar-model")
        << "give up: " << maxElements << " fresh elements" << std::endl;
    d_im.setModelUnsound(IncompleteId::BAGS_LIASTAR_MODEL);
    return;
  }
  // the known elements of a type
  std::map<TypeNode, std::vector<Node>> known;
  for (const Node& bag : d_lastSlots)
  {
    Node r = d_state.getRepresentative(bag);
    for (const std::pair<Node, Node>& pair : d_state.getElementCountPairs(r))
    {
      Node e = d_state.getRepresentative(pair.first);
      std::vector<Node>& elements = known[e.getType()];
      if (std::find(elements.begin(), elements.end(), e) == elements.end())
      {
        elements.push_back(e);
      }
    }
  }
  for (const TypeNode& type : types)
  {
    Node e = NodeManager::mkDummySkolem("bags_liastar_element", type);
    d_liastarElements = d_liastarElements.get() + 1;
    // either the known elements add up, or e is another element
    std::vector<Node> addUp;
    std::vector<Node> counts;
    for (size_t i = 0; i < n; i++)
    {
      const Node& bag = d_lastSlots[i];
      if (bag.getType().getBagElementType() != type)
      {
        continue;
      }
      Node x = d_cardinalityVars[bag];
      addUp.push_back(
          x.eqNode(d_lastSums[i].isNull() ? d_zero : d_lastSums[i]));
      counts.push_back(nm->mkNode(Kind::BAG_COUNT, e, bag));
    }
    std::vector<Node> isNew;
    for (const Node& k : known[type])
    {
      isNew.push_back(k.eqNode(e).notNode());
    }
    Node total = counts.size() == 1 ? counts[0] : nm->mkNode(Kind::ADD, counts);
    isNew.push_back(nm->mkNode(Kind::GEQ, total, d_one));
    Node lemma = nm->mkAnd(addUp).orNode(nm->mkAnd(isNew));
    if (!d_lastPremises.empty())
    {
      lemma = nm->mkAnd(d_lastPremises).impNode(lemma);
    }
    Trace("bags-liastar-model")
        << "fresh element " << e << ": " << lemma << std::endl;
    d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR_ELEMENT);
  }
}

void BagSolver::evictNegatedAtom(const Node& equality)
{
  Assert(equality.getKind() == Kind::EQUAL && equality[0].getType().isBag());
  NodeManager* nm = nodeManager();
  Node A = equality[0];
  Node B = equality[1];
  // the bound variables of A and B are related to those of the difference
  // bags by the pointwise definitions of the latter
  Node AminusB = rewrite(nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, A, B));
  Node BminusA = rewrite(nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, B, A));
  getBagBoundVar(A);
  getBagBoundVar(B);
  getBagBoundVar(AminusB);
  getBagBoundVar(BminusA);

  Node xA = getCardinalityVar(A);
  Node xB = getCardinalityVar(B);
  Node xAminusB = getCardinalityVar(AminusB);
  Node xBminusA = getCardinalityVar(BminusA);
  Node cards = nm->mkNode(
      Kind::AND,
      {xA.eqNode(xB), xAminusB.eqNode(d_zero), xBminusA.eqNode(d_zero)});
  // (or (= A B) (not (and (= x_A x_B) (= x_{A - B} 0) (= x_{B - A} 0))))
  // Note this lemma is valid, and not merely a consequence of the current
  // context: the cardinality variables are exactly the cardinalities of their
  // bags, and two bags are equal iff both their differences are empty.
  Node lemma = equality.orNode(cards.notNode());
  Trace("bags-liastar") << "evict " << equality << ": " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
}

void BagSolver::addCardinalityVars()
{
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    getCardinalityVar(pair.first);
  }
}

Node BagSolver::buildStar(const std::vector<Node>& equalities,
                          std::vector<Node>& premises)
{
  NodeManager* nm = nodeManager();
  // one fixed order for both vectors
  std::vector<Node> bags;
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    bags.push_back(pair.first);
  }
  // the outer vector, the inner vector, and the body of the star. The
  // constraints on the slots are kept by the element type of the slots they
  // constrain, since the rows of one type are what a map groups, see
  // addGroupConstraints.
  std::vector<Node> cardinalities;
  std::vector<Node> boundVars;
  std::map<TypeNode, std::vector<Node>> typedConstraints;
  std::vector<Node> constraints;
  for (const Node& bag : bags)
  {
    Node c = d_bagBoundVars[bag];
    Node x = getCardinalityVar(bag);
    boundVars.push_back(c);
    cardinalities.push_back(x);
    // the cardinality variables are skolems whose names do not mention their
    // bags, so print the slots of bag here
    Trace("bags-liastar") << "slot " << bag << ": cardinality = " << x
                          << ", bound var = " << c << std::endl;
    std::vector<Node>& typed =
        typedConstraints[bag.getType().getBagElementType()];
    // a count is non negative. Never omit the sign constraints: negative
    // summands would let the star cancel, and a cardinality of zero would no
    // longer mean that the bag is empty.
    typed.push_back(nm->mkNode(Kind::GEQ, c, d_zero));
    if (hasPointwiseTranslation(bag.getKind()))
    {
      typed.push_back(getPointwiseConstraint(bag));
    }
    else if (bag.getKind() == Kind::BAG_MAKE)
    {
      addBagMakeConstraints(bag, typed);
    }
    else if (bag.getKind() == Kind::BAG_FILTER)
    {
      // (bag.filter p A)(e) is A(e) or 0, depending on (p e), which the star
      // has no slot for. What is left is the inclusion (<= c c_A), which is
      // still worth having: without it a filter could have elements its bag
      // does not.
      typed.push_back(nm->mkNode(Kind::LEQ, c, d_bagBoundVars[bag[1]]));
    }
  }
  // the positive atoms hold at every element
  for (const Node& equality : equalities)
  {
    std::vector<Node>& typed =
        typedConstraints[equality[0].getType().getBagElementType()];
    Node a;
    Node b;
    if (isInclusionAtom(equality, a, b))
    {
      // (<= c_A c_B), the inclusion rule of the table
      typed.push_back(
          nm->mkNode(Kind::LEQ, d_bagBoundVars[a], d_bagBoundVars[b]));
    }
    else
    {
      typed.push_back(
          d_bagBoundVars[equality[0]].eqNode(d_bagBoundVars[equality[1]]));
    }
    premises.push_back(equality);
  }
  addBagMakeOverlaps(constraints, premises);
  for (const std::pair<const TypeNode, std::vector<Node>>& pair :
       typedConstraints)
  {
    constraints.insert(
        constraints.end(), pair.second.begin(), pair.second.end());
  }
  // no bag term was discovered while building the body, so the two vectors
  // cover all the bound variables that occur in it
  Assert(d_bagBoundVars.size() == bags.size());
  // the group columns of the map terms extend the two vectors
  addGroupConstraints(
      bags, typedConstraints, boundVars, cardinalities, constraints);

  Node boundVarList = nm->mkNode(Kind::BOUND_VAR_LIST, boundVars);
  Node body = nm->mkAnd(constraints);
  // kept for collectLiastarModelValues
  d_lastSlots = bags;
  d_lastBody = body;
  // the rows of the known elements are summands of the star that the context
  // already names, so they are taken out of it
  std::vector<Node> rows;
  std::vector<Node> sums;
  addElementRows(bags, boundVars, body, premises, rows, sums);
  d_lastSums = sums;
  d_lastPremises = premises;
  Node lambda = nm->mkNode(Kind::LAMBDA, boundVarList, body);
  std::vector<Node> children;
  children.push_back(lambda);
  for (size_t i = 0, n = boundVars.size(); i < n; i++)
  {
    children.push_back(sums[i].isNull()
                           ? cardinalities[i]
                           : nm->mkNode(Kind::SUB, cardinalities[i], sums[i]));
  }
  Node star = nm->mkNode(Kind::STAR_CONTAINS, children);
  if (rows.empty())
  {
    return star;
  }
  rows.push_back(star);
  return nm->mkAnd(rows);
}

void BagSolver::addGroupConstraints(
    const std::vector<Node>& bags,
    const std::map<TypeNode, std::vector<Node>>& typedConstraints,
    std::vector<Node>& boundVars,
    std::vector<Node>& coordinates,
    std::vector<Node>& constraints)
{
  NodeManager* nm = nodeManager();
  BoundVarManager* bvm = nm->getBoundVarManager();
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode intType = nm->integerType();
  // Every variable of a group is cached by the terms it stands for, so that
  // the same context builds the same star atom at every check and the
  // liastar extension expands it once.
  // the groupings, one per function and source type. The rows of the source
  // type that f sends to the same element form one group whatever bag they
  // are counted in, so every map with the same f over that type reads its
  // count off the same group sums.
  std::map<std::pair<Node, TypeNode>, size_t> groups;
  for (const Node& bag : bags)
  {
    if (bag.getKind() != Kind::BAG_MAP)
    {
      continue;
    }
    Node f = bag[0];
    TypeNode sourceType = bag[1].getType().getBagElementType();
    TypeNode targetType = bag.getType().getBagElementType();
    std::pair<Node, TypeNode> key(f, sourceType);
    std::map<std::pair<Node, TypeNode>, size_t>::iterator it = groups.find(key);
    if (it == groups.end())
    {
      // (the grouping of f is built on its first map)
      // The slots of the grouping: the sources of the maps of f, the slots
      // they are built from, and the setof of any of those, which is what a
      // count of distinct values reads. Every other slot of the source type
      // is left out: its group sums carry nothing the row equations use, and
      // each one adds a dimension to the star and a factor to the DNF of its
      // body, which a fold reduction, with its dozens of slots, makes
      // prohibitive. The groupings with more slots than
      // --bags-liastar-group-slots are dropped altogether.
      std::vector<Node> sources;
      for (const Node& b : bags)
      {
        if (b.getKind() == Kind::BAG_MAP && b[0] == f
            && b[1].getType().getBagElementType() == sourceType
            && std::find(sources.begin(), sources.end(), b[1]) == sources.end())
        {
          sources.push_back(b[1]);
        }
      }
      bool changed = true;
      while (changed)
      {
        changed = false;
        for (size_t i = 0; i < sources.size(); i++)
        {
          for (const Node& child : sources[i])
          {
            if (child.getType().isBag()
                && child.getType().getBagElementType() == sourceType
                && d_bagBoundVars.find(child) != d_bagBoundVars.end()
                && std::find(sources.begin(), sources.end(), child)
                       == sources.end())
            {
              sources.push_back(child);
              changed = true;
            }
          }
        }
        for (const Node& b : bags)
        {
          if (b.getKind() == Kind::BAG_SETOF
              && std::find(sources.begin(), sources.end(), b[0])
                     != sources.end()
              && std::find(sources.begin(), sources.end(), b) == sources.end())
          {
            sources.push_back(b);
            changed = true;
          }
        }
      }
      if (sources.size() > options().bags.bagsLiastarGroupSlots)
      {
        Trace("bags-liastar") << "no group of " << f << ": " << sources.size()
                              << " slots" << std::endl;
        groups[key] = std::numeric_limits<size_t>::max();
        continue;
      }
      it = groups.insert({key, d_groupColumns.size()}).first;
      // the slots in the order of the slots, so that the same context builds
      // the same inner star
      std::vector<Node> ordered;
      for (const Node& b : bags)
      {
        if (std::find(sources.begin(), sources.end(), b) != sources.end())
        {
          ordered.push_back(b);
        }
      }
      sources = ordered;
      // the fresh variables of the rows of the inner star: the outer lambda
      // binds the slot variables, so the inner body is the typed constraints
      // of the slots of the grouping over variables of its own
      std::vector<Node> sourceVars;
      std::vector<Node> innerVars;
      for (const Node& b : sources)
      {
        sourceVars.push_back(d_bagBoundVars[b]);
        innerVars.push_back(bvm->mkBoundVar(BoundVarId::BAGS_LIASTAR_ROW_COUNT,
                                            nm->mkNode(Kind::BAG_MAP, f, b),
                                            "row",
                                            intType));
      }
      std::unordered_set<Node> sourceVarSet(sourceVars.begin(),
                                            sourceVars.end());
      std::vector<Node> innerBody;
      std::map<TypeNode, std::vector<Node>>::const_iterator typedIt =
          typedConstraints.find(sourceType);
      if (typedIt != typedConstraints.end())
      {
        for (const Node& c : typedIt->second)
        {
          // only the constraints over the slots of the grouping
          std::unordered_set<Node> fvs;
          expr::getFreeVariables(c, fvs);
          bool inGroup = true;
          for (const Node& v : fvs)
          {
            inGroup = inGroup && sourceVarSet.find(v) != sourceVarSet.end();
          }
          if (!inGroup)
          {
            continue;
          }
          innerBody.push_back(c.substitute(sourceVars.begin(),
                                           sourceVars.end(),
                                           innerVars.begin(),
                                           innerVars.end()));
        }
      }
      // the group sum columns: the column of a source slot B sums B over the
      // rows of a group, so its column sum over all groups is the cardinality
      // of B
      std::vector<Node> vec;
      for (size_t i = 0, n = sources.size(); i < n; i++)
      {
        Node g = bvm->mkBoundVar(BoundVarId::BAGS_LIASTAR_GROUP_SUM,
                                 nm->mkNode(Kind::BAG_MAP, f, sources[i]),
                                 "group",
                                 intType);
        GroupColumn column;
        column.d_function = f;
        column.d_targetType = targetType;
        column.d_source = sources[i];
        column.d_boundVar = g;
        column.d_coordinate = getCardinalityVar(sources[i]);
        d_groupColumns.push_back(column);
        boundVars.push_back(g);
        coordinates.push_back(column.d_coordinate);
        constraints.push_back(nm->mkNode(Kind::GEQ, g, d_zero));
        vec.push_back(g);
      }
      bool injective = d_state.isInjective(f);
      if (injective)
      {
        // an injective f sends at most one row to a group: an indicator
        // column counts the rows of a group, and its column sum is free
        Node one = bvm->mkBoundVar(
            BoundVarId::BAGS_LIASTAR_ROW_ONE, f, "row_one", intType);
        innerVars.push_back(one);
        innerBody.push_back(one.eqNode(d_one));
        Node size = bvm->mkBoundVar(
            BoundVarId::BAGS_LIASTAR_GROUP_SIZE, f, "group_size", intType);
        GroupColumn column;
        column.d_function = f;
        column.d_targetType = targetType;
        column.d_boundVar = size;
        column.d_coordinate =
            sm->mkSkolemFunction(SkolemId::BAGS_LIASTAR_BAG_INTEGER, {f});
        d_groupColumns.push_back(column);
        boundVars.push_back(size);
        coordinates.push_back(column.d_coordinate);
        constraints.push_back(nm->mkNode(Kind::GEQ, size, d_zero));
        constraints.push_back(nm->mkNode(Kind::LEQ, size, d_one));
        vec.push_back(size);
      }
      Node innerLambda = nm->mkNode(Kind::LAMBDA,
                                    nm->mkNode(Kind::BOUND_VAR_LIST, innerVars),
                                    nm->mkAnd(innerBody));
      std::vector<Node> children;
      children.push_back(innerLambda);
      children.insert(children.end(), vec.begin(), vec.end());
      constraints.push_back(nm->mkNode(Kind::STAR_CONTAINS, children));
      Trace("bags-liastar") << "group of " << f << " over " << sourceType
                            << ": " << sources.size() << " source slots"
                            << (injective ? ", injective" : "") << std::endl;
    }
    if (it->second == std::numeric_limits<size_t>::max())
    {
      // the grouping of f was dropped
      continue;
    }
    // the row equation: the count of a group in the map is the group sum of
    // the source of the map
    for (size_t i = it->second, n = d_groupColumns.size(); i < n; i++)
    {
      const GroupColumn& column = d_groupColumns[i];
      if (column.d_function == f && column.d_source == bag[1])
      {
        constraints.push_back(d_bagBoundVars[bag].eqNode(column.d_boundVar));
        break;
      }
    }
  }
}

void BagSolver::addElementRows(const std::vector<Node>& bags,
                               const std::vector<Node>& boundVars,
                               const Node& body,
                               std::vector<Node>& premises,
                               std::vector<Node>& rows,
                               std::vector<Node>& sums)
{
  NodeManager* nm = nodeManager();
  SkolemManager* sm = nm->getSkolemManager();
  size_t n = bags.size();
  // the columns: the slots, then the group columns
  size_t m = boundVars.size();
  Assert(m == n + d_groupColumns.size());
  // the known elements, by their representatives, in one fixed order
  std::vector<Node> elements;
  for (const Node& bag : bags)
  {
    Node r = d_state.getRepresentative(bag);
    for (const std::pair<Node, Node>& pair : d_state.getElementCountPairs(r))
    {
      Node e = d_state.getRepresentative(pair.first);
      if (std::find(elements.begin(), elements.end(), e) == elements.end())
      {
        elements.push_back(e);
      }
    }
  }
  sums.assign(m, Node::null());
  std::vector<std::vector<Node>> summands(m);
  for (size_t j = 0, numElements = elements.size(); j < numElements; j++)
  {
    const Node& e = elements[j];
    TypeNode type = e.getType();
    // the row of e: its count terms in the slots of its type
    std::vector<Node> row(m);
    for (size_t i = 0; i < n; i++)
    {
      row[i] = getRowCount(e, bags[i]);
    }
    for (size_t i = n; i < m; i++)
    {
      // a known element of the target type of a grouping is a group, whose
      // sums the inner star of the row constrains; an element of another type
      // is in no group of it. The group sum of a source slot B at e is the
      // count of e in (bag.map f B): the count term when that map is a slot,
      // otherwise its purification skolem, as in getRowCount. The size of the
      // group is a skolem of f and e.
      const GroupColumn& column = d_groupColumns[i - n];
      if (type != column.d_targetType)
      {
        row[i] = d_zero;
      }
      else if (column.d_source.isNull())
      {
        row[i] = sm->mkSkolemFunction(SkolemId::BAGS_LIASTAR_BAG_INTEGER,
                                      {column.d_function, e});
      }
      else
      {
        Node map =
            nm->mkNode(Kind::BAG_MAP, column.d_function, column.d_source);
        if (d_bagBoundVars.find(map) != d_bagBoundVars.end())
        {
          row[i] = getRowCount(e, map);
        }
        else
        {
          row[i] = sm->mkPurifySkolem(nm->mkNode(Kind::BAG_COUNT, e, map));
        }
      }
    }
    rows.push_back(body.substitute(
        boundVars.begin(), boundVars.end(), row.begin(), row.end()));
    // the row of e is summed when e is equal to none of the earlier elements
    // of its type
    std::vector<Node> conditions;
    for (size_t l = 0; l < j; l++)
    {
      const Node& earlier = elements[l];
      if (earlier.getType() != type)
      {
        continue;
      }
      Node disequal = earlier.eqNode(e).notNode();
      if (d_state.areDisequal(earlier, e))
      {
        premises.push_back(disequal);
      }
      else
      {
        conditions.push_back(disequal);
      }
    }
    Node isNew = conditions.empty() ? Node::null() : nm->mkAnd(conditions);
    Trace("bags-liastar") << "row of " << e << ": " << row
                          << (isNew.isNull() ? "" : " if ") << isNew
                          << std::endl;
    for (size_t i = 0; i < m; i++)
    {
      if (row[i] == d_zero)
      {
        continue;
      }
      summands[i].push_back(isNew.isNull()
                                ? row[i]
                                : nm->mkNode(Kind::ITE, isNew, row[i], d_zero));
    }
  }
  for (size_t i = 0; i < m; i++)
  {
    if (summands[i].empty())
    {
      continue;
    }
    sums[i] = summands[i].size() == 1 ? summands[i][0]
                                      : nm->mkNode(Kind::ADD, summands[i]);
  }
}

Node BagSolver::getCardinalityVar(const Node& bag)
{
  Assert(bag.getType().isBag());
  std::map<Node, Node>::iterator it = d_cardinalityVars.find(bag);
  if (it != d_cardinalityVars.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Node x;
  // Reuse the cardinality variable of the input when there is one, i.e. the
  // skolem registered for the term (bag.card bag). That skolem is a purified
  // form of (bag.card bag), so it denotes the cardinality of bag in every
  // context and needs no guard.
  //
  // Note the lookup is for bag itself and not for its representative. The
  // bags of an equivalence class must not share a slot: sharing only holds in
  // the contexts where they are equal, whereas the slots are asserted by a
  // lemma that outlives them. A bag that is equal to the term the cardinality
  // term was registered for keeps its own slot, which the body of the star
  // ties to that one through their (guarded) equality atom.
  Node card = nm->mkNode(Kind::BAG_CARD, bag);
  const std::map<Node, Node>& cardTerms = d_state.getCardinalityTerms();
  std::map<Node, Node>::const_iterator cardIt = cardTerms.find(card);
  if (cardIt != cardTerms.end())
  {
    x = cardIt->second;
  }
  else
  {
    // a placeholder slot, only constrained by the star
    x = nm->getSkolemManager()->mkSkolemFunction(
        SkolemId::BAGS_LIASTAR_BAG_INTEGER, {bag});
  }
  d_cardinalityVars[bag] = x;
  return x;
}

Node BagSolver::getBagBoundVar(const Node& bag)
{
  Assert(bag.getType().isBag());
  std::map<Node, Node>::iterator it = d_bagBoundVars.find(bag);
  if (it != d_bagBoundVars.end())
  {
    return it->second;
  }
  BoundVarManager* bvm = nodeManager()->getBoundVarManager();
  // The variable is named after the bag it is the count of, e.g.
  // count_(bag.inter_min A B), so that the body of the star can be read
  // against the input. A lambda may bind dozens of these variables, so the
  // name of a large bag term is cut short and made unique again by its id.
  std::stringstream term;
  term << bag;
  std::stringstream name;
  name << "count_";
  if (term.str().size() <= 40)
  {
    name << term.str();
  }
  else
  {
    name << term.str().substr(0, 40) << "..." << bag.getId();
  }
  Node c = bvm->mkBoundVar(BoundVarId::BAGS_LIASTAR_BAG_COUNT,
                           bag,
                           name.str(),
                           nodeManager()->integerType());
  d_bagBoundVars[bag] = c;
  if (hasPointwiseTranslation(bag.getKind()))
  {
    // the pointwise definition of bag needs the slots of its arguments
    for (const Node& child : bag)
    {
      getBagBoundVar(child);
    }
  }
  else if (bag.getKind() == Kind::BAG_MAKE)
  {
    // the constraints of a constructed bag are stated over the slots of its
    // singleton and of their difference. See addBagMakeConstraints.
    Node singleton = getBagMakeSingleton(bag);
    if (singleton != bag)
    {
      getBagBoundVar(singleton);
      getBagBoundVar(getBagMakeDifference(bag));
    }
  }
  else if (bag.getKind() == Kind::BAG_FILTER)
  {
    // the inclusion of a filter in its bag needs the slot of the bag
    getBagBoundVar(bag[1]);
  }
  else if (bag.getKind() == Kind::BAG_MAP)
  {
    // the group sums of a map are sums over the slots of its source, see
    // addGroupConstraints, so the source needs a slot
    getBagBoundVar(bag[1]);
  }
  return c;
}

void BagSolver::addBagMakeConstraints(const Node& bag,
                                      std::vector<Node>& constraints)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  Node singleton = getBagMakeSingleton(bag);
  if (singleton == bag)
  {
    // bag is its own singleton, and its cardinality, which
    // addBagMakeCardinalities asserts to be 1, already concentrates its count
    // on one summand of the star
    return;
  }
  NodeManager* nm = nodeManager();
  Node c = d_bagBoundVars[bag];
  Node cSingleton = d_bagBoundVars[singleton];
  Node cDifference = d_bagBoundVars[getBagMakeDifference(bag)];
  // (bag e n) has no element besides the one of (bag e 1), since their
  // difference_remove is the empty bag
  constraints.push_back(cDifference.eqNode(d_zero));
  if (bag[1].isConst() && bag[1].getConst<Rational>().sgn() > 0)
  {
    // (bag e 1) is a subbag of (bag e n) for a positive n. This conjunct is
    // implied by the constraint above and the cardinalities, and is kept as a
    // redundant constraint for the solver.
    constraints.push_back(nm->mkNode(Kind::LEQ, cSingleton, c));
  }
}

void BagSolver::addBagMakeCardinalities()
{
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    Node bag = pair.first;
    if (bag.getKind() != Kind::BAG_MAKE)
    {
      continue;
    }
    // the cardinality of (bag e n) is n for a positive n, and 0 otherwise
    Node n = bag[1];
    Node isPositive = nm->mkNode(Kind::GEQ, n, d_one);
    Node card = nm->mkNode(Kind::ITE, isPositive, n, d_zero);
    Node x = getCardinalityVar(bag);
    Node lemma = x.eqNode(card);
    Trace("bags-liastar") << "cardinality of " << bag << ": " << lemma
                          << std::endl;
    d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
  }
}

void BagSolver::addBagMakeOverlaps(std::vector<Node>& constraints,
                                   std::vector<Node>& premises)
{
  NodeManager* nm = nodeManager();
  // the distinct singletons of the constructed bags of the star, in the order
  // of d_bagBoundVars, which is fixed
  std::vector<Node> singletons;
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    if (pair.first.getKind() != Kind::BAG_MAKE)
    {
      continue;
    }
    Node singleton = getBagMakeSingleton(pair.first);
    if (std::find(singletons.begin(), singletons.end(), singleton)
        == singletons.end())
    {
      singletons.push_back(singleton);
    }
  }
  for (size_t i = 0, size = singletons.size(); i < size; i++)
  {
    for (size_t j = i + 1; j < size; j++)
    {
      Node x = singletons[i][0];
      Node y = singletons[j][0];
      Node cx = d_bagBoundVars[singletons[i]];
      Node cy = d_bagBoundVars[singletons[j]];
      if (d_state.areDisequal(x, y))
      {
        // the two singletons have no element in common, and each count is 0
        // or 1, so they cannot both be 1 at the same element
        Node sum = nm->mkNode(Kind::ADD, cx, cy);
        constraints.push_back(nm->mkNode(Kind::LEQ, sum, d_one));
        premises.push_back(x.eqNode(y).notNode());
      }
      else if (d_state.areEqual(x, y))
      {
        // the two singletons are the same bag
        constraints.push_back(cx.eqNode(cy));
        premises.push_back(x.eqNode(y));
      }
    }
  }
}

Node BagSolver::getBagMakeSingleton(const Node& bag)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  // note this is bag itself when its multiplicity is the constant 1
  return nodeManager()->mkNode(Kind::BAG_MAKE, bag[0], d_one);
}

Node BagSolver::getBagMakeDifference(const Node& bag)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  Node singleton = getBagMakeSingleton(bag);
  Assert(singleton != bag);
  // The term is deliberately not rewritten. The rewriter only knows that a
  // difference_remove is empty when its arguments are syntactically equal, so
  // it leaves this term alone, but were it to recognize that this one is empty
  // too, the pointwise definition of the rewritten term would no longer relate
  // the counts of bag and of its singleton, which is the point of the term.
  return nodeManager()->mkNode(Kind::BAG_DIFFERENCE_REMOVE, bag, singleton);
}

Node BagSolver::getPointwiseConstraint(const Node& bag)
{
  Assert(hasPointwiseTranslation(bag.getKind()));
  NodeManager* nm = nodeManager();
  Node c = d_bagBoundVars[bag];
  if (bag.getKind() == Kind::BAG_EMPTY)
  {
    // bag.empty(e) = 0
    return c.eqNode(d_zero);
  }
  Node c1 = d_bagBoundVars[bag[0]];
  if (bag.getKind() == Kind::BAG_SETOF)
  {
    // (bag.setof A)(e) = ite(1 <= A(e), 1, 0)
    Node ite =
        nm->mkNode(Kind::ITE, nm->mkNode(Kind::LEQ, d_one, c1), d_one, d_zero);
    return c.eqNode(ite);
  }
  Node c2 = d_bagBoundVars[bag[1]];
  Node leq = nm->mkNode(Kind::LEQ, c1, c2);
  switch (bag.getKind())
  {
    case Kind::BAG_UNION_DISJOINT:
      // (bag.union_disjoint A B)(e) = A(e) + B(e)
      return c.eqNode(nm->mkNode(Kind::ADD, c1, c2));
    case Kind::BAG_UNION_MAX:
      // (bag.union_max A B)(e) = max(A(e), B(e))
      return c.eqNode(nm->mkNode(Kind::ITE, leq, c2, c1));
    case Kind::BAG_INTER_MIN:
      // (bag.inter_min A B)(e) = min(A(e), B(e))
      return c.eqNode(nm->mkNode(Kind::ITE, leq, c1, c2));
    case Kind::BAG_DIFFERENCE_SUBTRACT:
      // (bag.difference_subtract A B)(e) = max(0, A(e) - B(e)). The
      // truncation matters: a count is non negative.
      return c.eqNode(
          nm->mkNode(Kind::ITE, leq, d_zero, nm->mkNode(Kind::SUB, c1, c2)));
    case Kind::BAG_DIFFERENCE_REMOVE:
      // (bag.difference_remove A B)(e) = ite(B(e) = 0, A(e), 0), i.e. every
      // occurrence of e is removed, not just as many as e occurs in B.
      return c.eqNode(nm->mkNode(Kind::ITE, c2.eqNode(d_zero), c1, d_zero));
    default: Unreachable() << "no pointwise translation for " << bag;
  }
  return Node::null();
}

bool BagSolver::isInclusionAtom(const Node& equality, Node& a, Node& b)
{
  Assert(equality.getKind() == Kind::EQUAL && equality[0].getType().isBag());
  for (size_t i = 0; i < 2; i++)
  {
    if (equality[i].getKind() == Kind::BAG_EMPTY
        && equality[1 - i].getKind() == Kind::BAG_DIFFERENCE_SUBTRACT)
    {
      a = equality[1 - i][0];
      b = equality[1 - i][1];
      return true;
    }
  }
  return false;
}

bool BagSolver::hasPointwiseTranslation(Kind k)
{
  switch (k)
  {
    case Kind::BAG_EMPTY:
    case Kind::BAG_UNION_DISJOINT:
    case Kind::BAG_UNION_MAX:
    case Kind::BAG_INTER_MIN:
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE:
    case Kind::BAG_SETOF: return true;
    // Note (bag x c) is missing on purpose: its count at an element is not a
    // function of the counts of its arguments, it is c at x and 0 everywhere
    // else.
    default: return false;
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
    InferInfo info = d_ig.bagDisequality(equality, witness);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::checkMap(Node n)
{
  Assert(n.getKind() == Kind::BAG_MAP);
  if (options().bags.bagsToLiastar && !d_state.getCardinalityTerms().empty())
  {
    // the cardinality of a map is the cardinality of its argument. This is
    // only sent with the translation to liastar, where the cardinality terms
    // are not reduced, since otherwise it introduces two cardinality terms
    // that are each reduced to a bounded quantifier; and only once the
    // context has a cardinality term, since otherwise this would be the term
    // that brings the star into a problem that asks nothing about
    // cardinalities, see checkLiastarConstraints.
    InferInfo card = d_ig.mapCard(n);
    d_im.lemmaTheoryInference(&card);
  }
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

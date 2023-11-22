/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Nullables theory.
 */

#include "theory/nullables/theory_nullables.h"

#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

TheoryNullables::TheoryNullables(Env& env,
                                 OutputChannel& out,
                                 Valuation valuation)
    : Theory(THEORY_NULLABLES, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state),
      d_notify(*this, d_im),
      d_statistics(statisticsRegistry()),
      d_rewriter(env.getRewriter(), &d_statistics.d_rewrites),
      d_termReg(env, d_state, d_im),
      d_solver(env, d_state, d_im, d_termReg),      
      d_cpacb(*this)
{
  // use the official theory state and inference manager objects
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryNullables::~TheoryNullables() {}

TheoryRewriter* TheoryNullables::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryNullables::getProofChecker() { return nullptr; }

bool TheoryNullables::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::nullables::ee";
  return true;
}

void TheoryNullables::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_valuation.setUnevaluatedKind(Kind::WITNESS);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_LIFT);
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_LIFT_OP);
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_NOTHING);
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_TYPE);
  
}

TrustNode TheoryNullables::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  Trace("nullables-ppr") << "TheoryNullables::ppRewrite " << atom << std::endl;

  switch (atom.getKind())
  {    
    {
      Node ret = NullableReduction::reduceProjectOperator(atom);
      Trace("nullables::ppr")
          << "reduce(" << atom << ") = " << ret << std::endl;
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
    default: return TrustNode::null();
  }
}

void TheoryNullables::initialize()
{
  d_state.reset();
  d_opMap.clear();
  d_state.collectDisequalNullableTerms();
  collectNullablesTerms();
}

void TheoryNullables::collectNullablesTerms()
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator repIt = eq::EqClassesIterator(ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    Trace("nullables-eqc") << "Eqc [ " << eqc << " ] = { ";

    if (eqc.getType().isNullable())
    {
      d_state.registerNullable(eqc);
    }

    eq::EqClassIterator it = eq::EqClassIterator(eqc, ee);
    while (!it.isFinished())
    {
      Node n = (*it);
      d_opMap[n.getKind()].push_back(n);
      Trace("nullables-eqc") << (*it) << " ";
      Kind k = n.getKind();
      if (k == Kind::NULLABLE_MAKE)
      {
        // for terms (nullable x c) we need to store x by registering the count
        // term (nullable.count x (nullable x c))
        NodeManager* nm = NodeManager::currentNM();
        Node count = nm->mkNode(Kind::NULLABLE_COUNT, n[0], n);
        d_ig.registerCountTerm(count);
      }
      if (k == Kind::NULLABLE_COUNT)
      {
        // this takes care of all count terms in each equivalent class
        d_ig.registerCountTerm(n);
      }
      if (k == Kind::NULLABLE_CARD)
      {
        d_ig.registerCardinalityTerm(n);
      }
      if (k == Kind::TABLE_GROUP)
      {
        d_state.registerGroupTerm(n);
      }
      ++it;
    }
    Trace("nullables-eqc") << " } " << std::endl;
    ++repIt;
  }
}

void TheoryNullables::postCheck(Effort effort)
{
  d_im.doPendingFacts();
  Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck()
      && d_strat.hasStrategyEffort(effort))
  {
    Trace("nullables::TheoryNullables::postCheck")
        << "effort: " << effort << std::endl;

    // TODO issue #78: add ++(d_statistics.d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    Trace("nullables-check") << "Full effort check..." << std::endl;
    do
    {
      d_im.reset();
      // TODO issue #78: add ++(d_statistics.d_strategyRuns);
      Trace("nullables-check") << "  * Run strategy..." << std::endl;
      initialize();
      d_cardSolver.reset();
      runStrategy(effort);

      // remember if we had pending facts or lemmas
      hadPending = d_im.hasPending();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      d_im.doPending();
      // Did we successfully send a lemma? Notice that if hasPending = true
      // and sentLemma = false, then the above call may have:
      // (1) had no pending lemmas, but successfully processed pending facts,
      // (2) unsuccessfully processed pending lemmas.
      // In either case, we repeat the strategy if we are not in conflict.
      sentLemma = d_im.hasSentLemma();
      if (TraceIsOn("nullables-check"))
      {
        Trace("nullables-check") << "  ...finish run strategy: ";
        Trace("nullables-check") << (hadPending ? "hadPending " : "");
        Trace("nullables-check") << (sentLemma ? "sentLemma " : "");
        Trace("nullables-check") << (d_state.isInConflict() ? "conflict " : "");
        if (!hadPending && !sentLemma && !d_state.isInConflict())
        {
          Trace("nullables-check") << "(none)";
        }
        Trace("nullables-check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict, and we had pending
      // facts or lemmas.
    } while (!d_state.isInConflict() && !sentLemma && hadPending);
  }
  Trace("nullables-check") << "Theory of nullables, done check : " << effort
                           << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
}

void TheoryNullables::runStrategy(Theory::Effort e)
{
  std::vector<std::pair<InferStep, size_t>>::iterator it = d_strat.stepBegin(e);
  std::vector<std::pair<InferStep, size_t>>::iterator stepEnd =
      d_strat.stepEnd(e);

  Trace("nullables-process") << "----check, next round---" << std::endl;
  while (it != stepEnd)
  {
    InferStep curr = it->first;
    if (curr == BREAK)
    {
      if (d_state.isInConflict() || d_im.hasPending())
      {
        break;
      }
    }
    else
    {
      if (runInferStep(curr, it->second) || d_state.isInConflict())
      {
        break;
      }
    }
    ++it;
  }
  Trace("nullables-process") << "----finished round---" << std::endl;
}

/** run the given inference step */
bool TheoryNullables::runInferStep(InferStep s, int effort)
{
  Trace("nullables-process") << "Run " << s;
  if (effort > 0)
  {
    Trace("nullables-process") << ", effort = " << effort;
  }
  Trace("nullables-process") << "..." << std::endl;
  switch (s)
  {
    case CHECK_INIT: break;
    case CHECK_NULLABLE_MAKE:
    {
      if (d_solver.checkNullableMake())
      {
        return true;
      }
      break;
    }
    case CHECK_BASIC_OPERATIONS: d_solver.checkBasicOperations(); break;
    case CHECK_QUANTIFIED_OPERATIONS:
      d_solver.checkQuantifiedOperations();
      break;
    case CHECK_CARDINALITY_CONSTRAINTS:
      d_cardSolver.checkCardinalityGraph();
      break;
    default: Unreachable(); break;
  }
  Trace("nullables-process")
      << "Done " << s << ", addedFact = " << d_im.hasPendingFact()
      << ", addedLemma = " << d_im.hasPendingLemma()
      << ", conflict = " << d_state.isInConflict() << std::endl;
  return false;
}

void TheoryNullables::notifyFact(TNode atom,
                                 bool polarity,
                                 TNode fact,
                                 bool isInternal)
{
}

bool TheoryNullables::collectModelValues(TheoryModel* m,
                                         const std::set<Node>& termSet)
{
  Trace("nullables-model") << "TheoryNullables : Collect model values"
                           << std::endl;

  Trace("nullables-model") << "Term set: " << termSet << std::endl;

  // a map from nullable representatives to their constructed values
  std::map<Node, Node> processedNullables;

  // get the relevant nullable equivalence classes
  for (const Node& n : termSet)
  {
    TypeNode tn = n.getType();
    if (!tn.isNullable())
    {
      // we are only concerned here about nullable terms
      continue;
    }
    Node r = d_state.getRepresentative(n);

    if (processedNullables.find(r) != processedNullables.end())
    {
      // skip nullables whose representatives are already processed
      continue;
    }

    const std::vector<std::pair<Node, Node>>& solverElements =
        d_state.getElementCountPairs(r);
    std::vector<std::pair<Node, Node>> elements;
    for (std::pair<Node, Node> pair : solverElements)
    {
      if (termSet.find(pair.first) == termSet.end())
      {
        continue;
      }
      elements.push_back(pair);
    }

    std::map<Node, Node> elementReps;
    for (std::pair<Node, Node> pair : elements)
    {
      Node key = d_state.getRepresentative(pair.first);
      Node countSkolem = pair.second;
      Node value = m->getRepresentative(countSkolem);
      elementReps[key] = value;
    }
    Node constructedNullable =
        NullablesUtils::constructNullableFromElements(tn, elementReps);
    constructedNullable = rewrite(constructedNullable);
    NodeManager* nm = NodeManager::currentNM();
    if (d_state.hasCardinalityTerms())
    {
      if (d_cardSolver.isLeaf(n))
      {
        Node constructedNullableCard =
            rewrite(nm->mkNode(Kind::NULLABLE_CARD, constructedNullable));
        Trace("nullables-model")
            << "constructed nullable cardinality: " << constructedNullableCard
            << std::endl;
        Node rCard = nm->mkNode(Kind::NULLABLE_CARD, r);
        Node rCardSkolem = d_state.getCardinalitySkolem(rCard);
        Trace("nullables-model")
            << "rCardSkolem : " << rCardSkolem << std::endl;
        if (!rCardSkolem.isNull())
        {
          Node rCardModelValue = m->getRepresentative(rCardSkolem);
          if (rCardModelValue.isConst())
          {
            const Rational& rCardRational =
                rCardModelValue.getConst<Rational>();
            const Rational& constructedRational =
                constructedNullableCard.getConst<Rational>();
            Trace("nullables-model")
                << "constructedRational : " << constructedRational << std::endl;
            Trace("nullables-model")
                << "rCardRational : " << rCardRational << std::endl;
            Assert(constructedRational <= rCardRational);
            TypeNode elementType = r.getType().getNullableElementType();
            if (constructedRational < rCardRational
                && !d_env.isFiniteType(elementType))
            {
              Node newElement =
                  nm->getSkolemManager()->mkDummySkolem("slack", elementType);
              Trace("nullables-model")
                  << "newElement is " << newElement << std::endl;
              Rational difference = rCardRational - constructedRational;
              Node multiplicity = nm->mkConstInt(difference);
              Node slackNullable =
                  nm->mkNode(Kind::NULLABLE_MAKE, newElement, multiplicity);
              constructedNullable = nm->mkNode(Kind::NULLABLE_UNION_DISJOINT,
                                               constructedNullable,
                                               slackNullable);
              constructedNullable = rewrite(constructedNullable);
            }
          }
        }
      }
      else
      {
        std::vector<Node> children = d_cardSolver.getChildren(n);
        Assert(!children.empty());
        constructedNullable = nm->mkConst(EmptyNullable(r.getType()));
        for (Node child : children)
        {
          Trace("nullables-model")
              << "child nullable for " << n << " is: " << child << std::endl;
          constructedNullable = nm->mkNode(
              Kind::NULLABLE_UNION_DISJOINT, child, constructedNullable);
        }
        constructedNullable = rewrite(constructedNullable);
        Trace("nullables-model") << "constructed nullable for " << n
                                 << " is: " << constructedNullable << std::endl;
      }
    }
    m->assertEquality(constructedNullable, n, true);
    m->assertSkeleton(constructedNullable);
    processedNullables[r] = constructedNullable;
  }

  Trace("nullables-model") << "processedNullables:  " << processedNullables
                           << std::endl;
  return true;
}

TrustNode TheoryNullables::explain(TNode node) { return d_im.explainLit(node); }

Node TheoryNullables::getCandidateModelValue(TNode node)
{
  return Node::null();
}

void TheoryNullables::preRegisterTerm(TNode n)
{
  Trace("nullables") << "TheoryNullables::preRegisterTerm(" << n << ")"
                     << std::endl;
  switch (n.getKind())
  {
    case Kind::EQUAL:
    {
      // add trigger predicate for equality and membership
      d_state.addEqualityEngineTriggerPredicate(n);
    }
    break;
    case Kind::NULLABLE_FROM_SET:
    case Kind::NULLABLE_TO_SET:
    case Kind::NULLABLE_IS_SINGLETON:
    case Kind::NULLABLE_PARTITION:
    {
      std::stringstream ss;
      ss << "Term of kind " << n.getKind() << " is not supported yet";
      throw LogicException(ss.str());
    }
    default: d_equalityEngine->addTerm(n); break;
  }
}

void TheoryNullables::presolve()
{
  Trace("nullables-presolve") << "Started presolve" << std::endl;
  d_strat.initializeStrategy();
  Trace("nullables-presolve") << "Finished presolve" << std::endl;
}

/**************************** eq::NotifyClass *****************************/

void TheoryNullables::eqNotifyNewClass(TNode n) {}

void TheoryNullables::eqNotifyMerge(TNode n1, TNode n2) {}

void TheoryNullables::eqNotifyDisequal(TNode n1, TNode n2, TNode reason) {}

void TheoryNullables::NotifyClass::eqNotifyNewClass(TNode n)
{
  Trace("nullables-eq") << "[nullables-eq] eqNotifyNewClass:"
                        << " n = " << n << std::endl;
  d_theory.eqNotifyNewClass(n);
}

void TheoryNullables::NotifyClass::eqNotifyMerge(TNode n1, TNode n2)
{
  Trace("nullables-eq") << "[nullables-eq] eqNotifyMerge:"
                        << " n1 = " << n1 << " n2 = " << n2 << std::endl;
  d_theory.eqNotifyMerge(n1, n2);
}

void TheoryNullables::NotifyClass::eqNotifyDisequal(TNode n1,
                                                    TNode n2,
                                                    TNode reason)
{
  Trace("nullables-eq") << "[nullables-eq] eqNotifyDisequal:"
                        << " n1 = " << n1 << " n2 = " << n2
                        << " reason = " << reason << std::endl;
  d_theory.eqNotifyDisequal(n1, n2, reason);
}

bool TheoryNullables::isCareArg(Node n, unsigned a)
{
  if (d_equalityEngine->isTriggerTerm(n[a], THEORY_NULLABLES))
  {
    return true;
  }
  else if ((n.getKind() == Kind::NULLABLE_COUNT
            || n.getKind() == Kind::NULLABLE_MAKE)
           && a == 0 && n[0].getType().isNullable())
  {
    // when the elements themselves are nullables
    return true;
  }
  return false;
}

void TheoryNullables::computeCareGraph()
{
  Trace("nullables-cg") << "Compute graph for nullables" << std::endl;
  for (const std::pair<const Kind, std::vector<Node>>& it : d_opMap)
  {
    Kind k = it.first;
    if (k == Kind::NULLABLE_MAKE || k == Kind::NULLABLE_COUNT)
    {
      Trace("nullables-cg")
          << "kind: " << k << ", size = " << it.second.size() << std::endl;
      std::map<TypeNode, TNodeTrie> index;
      unsigned arity = 0;
      // populate indices
      for (TNode n : it.second)
      {
        Trace("nullables-cg") << "computing n:  " << n << std::endl;
        Assert(d_equalityEngine->hasTerm(n));
        TypeNode tn;
        if (k == Kind::NULLABLE_MAKE)
        {
          tn = n.getType().getNullableElementType();
        }
        else
        {
          Assert(k == Kind::NULLABLE_COUNT);
          tn = n[1].getType().getNullableElementType();
        }
        std::vector<TNode> childrenReps;
        bool hasCareArg = false;
        for (unsigned j = 0; j < n.getNumChildren(); j++)
        {
          childrenReps.push_back(d_equalityEngine->getRepresentative(n[j]));
          if (isCareArg(n, j))
          {
            hasCareArg = true;
          }
        }
        if (hasCareArg)
        {
          Trace("nullables-cg")
              << "addTerm(" << n << ", " << childrenReps << ")" << std::endl;
          index[tn].addTerm(n, childrenReps);
          arity = childrenReps.size();
        }
        else
        {
          Trace("nullables-cg") << "......skip." << std::endl;
        }
      }
      if (arity > 0)
      {
        // for each index
        for (std::pair<const TypeNode, TNodeTrie>& tt : index)
        {
          Trace("nullables-cg")
              << "Process index " << tt.first << "..." << std::endl;
          nodeTriePathPairProcess(&tt.second, arity, d_cpacb);
        }
      }
      Trace("nullables-cg") << "...done" << std::endl;
    }
  }
}

void TheoryNullables::processCarePairArgs(TNode a, TNode b)
{
  // we care about the equality or disequality between x, y
  // when (nullable.count x A) = (nullable.count y A)
  if (a.getKind() != Kind::NULLABLE_COUNT && d_state.areEqual(a, b))
  {
    return;
  }
  // otherwise, we add pairs for each of their arguments
  addCarePairArgs(a, b);
  size_t childrenSize = a.getNumChildren();
  for (size_t i = 0; i < childrenSize; ++i)
  {
    TNode x = a[i];
    TNode y = b[i];
    if (!d_equalityEngine->areEqual(x, y))
    {
      if (isCareArg(a, i) && isCareArg(b, i))
      {
        // splitting on nullables (necessary for handling nullable of nullables
        // properly)
        if (x.getType().isNullable())
        {
          Assert(y.getType().isNullable());
          Trace("nullables-cg-lemma")
              << "Should split on : " << x << "==" << y << std::endl;
          Node equal = x.eqNode(y);
          Node lemma = equal.orNode(equal.notNode());
          d_im.lemma(lemma, InferenceId::NULLABLES_CG_SPLIT);
        }
      }
    }
  }
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

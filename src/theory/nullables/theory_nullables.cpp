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
      d_rewriter(env.getRewriter(), nullptr),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::nullables::"),
      d_solver(env, d_state, d_im),
      d_notify(*this, d_im)
{
  d_theoryState = &d_state;
  d_inferManager = &d_im;
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

TheoryNullables::~TheoryNullables() {}

TheoryRewriter* TheoryNullables::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryNullables::getProofChecker() { return nullptr; }

std::string TheoryNullables::identify() const { return "THEORY_NULLABLES"; }

bool TheoryNullables::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::nullables::ee";
  return true;
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

    Node constructedNullable = n;
    m->assertEquality(constructedNullable, n, true);
    m->assertSkeleton(constructedNullable);
  }

  Trace("nullables-model") << "processedNullables:  " << processedNullables
                           << std::endl;
  return true;
}

void TheoryNullables::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_NULL);
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_SOME);
  d_equalityEngine->addFunctionKind(Kind::NULLABLE_VAL);
}

void TheoryNullables::preRegisterTerm(TNode n)
{
  Trace("nullables") << "TheoryNullables::preRegisterTerm: " << n << std::endl;
  switch (n.getKind())
  {
    case Kind::NULLABLE_LIFT:
    {
      d_equalityEngine->addTerm(n);
      for (Node arg : n)
      {
        d_equalityEngine->addTerm(arg);
      }
      break;
    }
    default: break;
  }
}

void TheoryNullables::presolve()
{
  Trace("nullables-presolve") << "Started presolve" << std::endl;
  d_strat.initializeStrategy();
  Trace("nullables-presolve") << "Finished presolve" << std::endl;
}

void TheoryNullables::postCheck(Effort level)
{
  d_im.doPendingFacts();
  Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck()
      && d_strat.hasStrategyEffort(level))
  {
    Trace("nullables::TheoryNullables::postCheck")
        << "effort: " << level << std::endl;

    bool sentLemma = false;
    bool hadPending = false;
    Trace("nullables-check") << "Full effort check..." << std::endl;
    do
    {
      d_im.reset();
      d_state.reset();
      Trace("nullables-check") << "  * Run strategy..." << std::endl;
      runStrategy(level);
      // remember if we had pending facts or lemmas
      hadPending = d_im.hasPending();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
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
  Trace("nullables-check") << "Theory of nullables, done check : " << level
                           << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
  std::vector<Node> assertions;
  for (Theory::assertions_iterator it = facts_begin(); it != facts_end(); ++it)
  {
    const Assertion& assertion = *it;
    Node lit = assertion.d_assertion;
    assertions.push_back(lit);
  }
  std::vector<Node> unsatAssertions;
  Trace("nullables-cm") << "Checking " << assertions.size() << " assertions..."
                        << std::endl;
  for (const Node& a : assertions)
  {
    Trace("nullables-cm-debug") << a << std::endl;
  }
}

bool TheoryNullables::checkModelLastCall()
{
  std::vector<Node> assertions;
  for (Theory::assertions_iterator it = facts_begin(); it != facts_end(); ++it)
  {
    const Assertion& assertion = *it;
    Node lit = assertion.d_assertion;
    assertions.push_back(lit);
  }
  std::vector<Node> unsatAssertions;
  Trace("nullables-cm") << "Checking " << assertions.size() << " assertions..."
                        << std::endl;
  TheoryModel* m = d_valuation.getModel();
  for (const Node& a : assertions)
  {
    Node av = m->getValue(a);
    Trace("nullables-cm-debug") << "M[" << a << "] = " << av << std::endl;
    if (av == d_true)
    {
      continue;
    }
    Trace("nullables-cm") << "** M[" << a << "] = " << av << std::endl;
    unsatAssertions.push_back(a);
  }
  Trace("nullables-cm") << "...not satisfied " << unsatAssertions.size()
                        << " / " << assertions.size() << std::endl;
  for (TNode n : d_sharedTerms)
  {
    Node value = m->getValue(n);
    Node rep = m->getRepresentative(n);
    if (value != rep)
    {
      return false;
    }
  }
  return unsatAssertions.empty();
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
    case CHECK_BASIC_OPERATIONS:
      d_solver.checkBasicOperations();
      d_solver.checkLift();
      break;
    case CHECK_SPLIT:
    {
      if (d_solver.checkSplit())
      {
        return true;
      }
      break;
    }
    default: Unreachable(); break;
  }
  Trace("nullables-process")
      << "Done " << s << ", addedFact = " << d_im.hasPendingFact()
      << ", addedLemma = " << d_im.hasPendingLemma()
      << ", conflict = " << d_state.isInConflict() << std::endl;
  return false;
}

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

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

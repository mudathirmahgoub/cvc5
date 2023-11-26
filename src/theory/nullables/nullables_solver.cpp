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
 * Solver for the theory of nullables.
 */

#include "theory/nullables/nullables_solver.h"

#include "theory/nullables/inference_manager.h"
#include "theory/nullables/solver_state.h"
#include "theory/nullables/term_registry.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullablesSolver::NullablesSolver(Env& env,
                                 SolverState& s,
                                 InferenceManagerBuffered& im)
    : EnvObj(env), d_state(s), d_im(&im)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

NullablesSolver::~NullablesSolver() {}

void NullablesSolver::checkBasicOperations()
{
  // checkDisequalNullablesTerms();

  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator repIt = eq::EqClassesIterator(ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    repIt++;
    if (!eqc.getType().isNullable())
    {
      // we only care about nullable terms
      continue;
    }
    Trace("nullables-eqc") << "eqc: " << eqc << std::endl;
    // iterate through all nullables terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(eqc, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      it++;
      if (it.isFinished())
      {
        continue;
      }
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::NULLABLE_VALUE:
        {
          eq::EqClassIterator it2 = it;
          checkValue(n, it2);
          break;
        }
        case Kind::NULLABLE_NULL:
        {
          eq::EqClassIterator it2 = it;
          checkNull(n, it2);
          break;
        }
        default: break;
      }
    }
  }
}

void NullablesSolver::checkValue(const Node& n1, eq::EqClassIterator it)
{
  Assert(n1.getKind() == Kind::NULLABLE_VALUE);
  do
  {
    Node n2 = *it;
    Trace("nullables-eqc") << "n2: " << n2 << std::endl;
    it++;
    if (n2.getKind() == Kind::NULLABLE_VALUE)
    {
      Node x = n1[0];
      Node y = n2[0];
      Node premise = n1.eqNode(n2);
      Node conclusion = x.eqNode(y);
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_INJECT);
    }
    if (n2.getKind() == Kind::NULLABLE_NULL)
    {
      Node premise = n1.eqNode(n2);
      Node conclusion = d_false;
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_CLASH);
    }
  } while (!it.isFinished());
}

void NullablesSolver::checkNull(const Node& n1, eq::EqClassIterator it)
{
  Assert(n1.getKind() == Kind::NULLABLE_NULL);
  do
  {
    Node n2 = *it;
    Trace("nullables-eqc") << "n2: " << n2 << std::endl;
    it++;
    if (n2.getKind() == Kind::NULLABLE_VALUE)
    {
      Node premise = n1.eqNode(n2);
      Node conclusion = d_false;
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_INJECT);
    }
  } while (!it.isFinished());
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

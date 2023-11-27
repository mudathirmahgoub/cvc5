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
 * Implementation of nullables state object.
 */

#include "theory/nullables/solver_state.h"

#include "theory/uf/equality_engine.h"
#include "theory/uf/equality_engine_iterator.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

SolverState::SolverState(Env& env, Valuation val) : TheoryState(env, val)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_nm = NodeManager::currentNM();
}

const std::map<Node, std::vector<Node>>& SolverState::getNullables() const
{
  return d_nullables;
}

const std::set<Node>& SolverState::getSelectTerms() const
{
  return d_selectTerms;
}

void SolverState::reset()
{
  d_nullables.clear();
  eq::EqualityEngine* ee = getEqualityEngine();
  eq::EqClassesIterator repIt = eq::EqClassesIterator(ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    repIt++;
    if (eqc.getKind() == Kind::NULLABLE_SELECT)
    {
      d_selectTerms.insert(eqc);
      continue;
    }
    eq::EqClassIterator it = eq::EqClassIterator(eqc, getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      it++;
      if (n.getKind() == Kind::NULLABLE_SELECT)
      {
        d_selectTerms.insert(n);
      }
    }
    continue;

    d_nullables[eqc] = std::vector<Node>();
    d_nullables[eqc].push_back(eqc);
    while (!it.isFinished())
    {
      Node n = (*it);
      it++;
      d_nullables[eqc].push_back(n);
    }
  }
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

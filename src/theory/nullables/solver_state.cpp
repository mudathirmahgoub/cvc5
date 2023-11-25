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

void SolverState::registerNullable(TNode n)
{
  Assert(n.getType().isNullable());
  d_nullables.insert(n);
}

const std::set<Node>& SolverState::getNullables() { return d_nullables; }

void SolverState::reset() { d_nullables.clear(); }

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

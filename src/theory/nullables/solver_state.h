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
 * Nullables state object.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__THEORY_SOLVER_STATE_H
#define CVC5__THEORY__NULLABLES__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

class SolverState : public TheoryState
{
 public:
  SolverState(Env& env, Valuation val);

  /**
   * This function adds the nullable representative n to the set d_nullables if
   * it is not already there. This function is called during postCheck to
   * collect nullable terms in the equality engine. See the documentation of
   * @link SolverState::collectNullablesAndCountTerms
   */
  void registerNullable(TNode n);

  /** get all nullable terms that are representatives in the equality engine.
   * This function is valid after the current solver is initialized during
   * postCheck. See SolverState::initialize and NullableSolver::postCheck
   */
  const std::map<Node, std::vector<Node>>& getNullables() const;

  /** clear all nullables data structures */
  void reset();

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** node manager for this solver state */
  NodeManager* d_nm;
  /** collection of nullable representatives */
  std::map<Node, std::vector<Node>> d_nullables;
}; /* class SolverState */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_SOLVER_STATE_H */

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

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "cvc5_private.h"
#include "smt/env_obj.h"
#include "theory/inference_manager_buffered.h"
#include "theory/uf/equality_engine_iterator.h"

#ifndef CVC5__THEORY__NULLABLE__SOLVER_H
#define CVC5__THEORY__NULLABLE__SOLVER_H

namespace cvc5::internal {
namespace theory {
namespace nullables {

class SolverState;
class TermRegistry;

/** The solver for the theory of nullables
 *
 */
class NullablesSolver : protected EnvObj
{
 public:
  NullablesSolver(Env& env, SolverState& s, InferenceManagerBuffered& im);
  ~NullablesSolver();

  /**
   * apply inference rules for basic nullable operators
   */
  void checkBasicOperations();

  bool checkSplit();
  bool isNullOrValue(Node eqc);

 private:
  /**
   * Apply inference rules:
   * 1. Inject rule:
   *   (=>
   *     (= (null.value x) (null.value y))
   *     (= x y)
   *   )
   * 2. Clash rule:
   *   (=>
   *     (= (null.value x) (as nullable.null (Nullable Int)))
   *     false
   *   )
   */
  void checkValue(const Node& n1, eq::EqClassIterator it);
  /**
   * Apply clash rule:
   * (=>
   *   (= (as nullable.null (Nullable Int)) (null.value y))
   *   false
   * )
   */
  void checkNull(const Node& n1, eq::EqClassIterator it);

  /** The solver state object */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of nullables */
  InferenceManagerBuffered* d_im;

  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class NullablesSolver */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLE__SOLVER_H */

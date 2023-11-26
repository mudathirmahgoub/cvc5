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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__THEORY_NULLABLES_H
#define CVC5__THEORY__NULLABLES__THEORY_NULLABLES_H

#include "theory/inference_manager_buffered.h"
#include "theory/nullables/nullables_rewriter.h"
#include "theory/nullables/nullables_solver.h"
#include "theory/nullables/nullables_statistics.h"
#include "theory/nullables/solver_state.h"
#include "theory/nullables/strategy.h"
#include "theory/nullables/term_registry.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

class TheoryNullables : public Theory
{
 public:
  /** Constructs a new instance of TheoryNullables w.r.t. the provided contexts.
   */
  TheoryNullables(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryNullables() override;

  /**
   * @return The theory rewriter associated with this theory.
   */
  TheoryRewriter* getTheoryRewriter() override;
  /**
   * @return The proof checker associated with this theory.
   */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Identify this theory (for debugging, dynamic configuration,
   * etc..)
   */
  std::string identify() const override;

  /**
   * Returns true if this theory needs an equality engine for checking
   * satisfiability.
   *
   * If this method returns true, then the equality engine manager will
   * initialize its equality engine field via setEqualityEngine above during
   * TheoryEngine::finishInit, prior to calling finishInit for this theory.
   *
   * Additionally, if this method returns true, then this method is required
   * to update the argument esi with instructions for initializing and setting
   * up notifications from its equality engine, which is commonly done with a
   * notifications class (eq::EqualityEngineNotify).
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  /** finish initialization */
  void finishInit() override;

  /**
   * Collect model values, after equality information is added to the model.
   * The argument termSet is the set of relevant terms returned by
   * computeRelevantTerms.
   */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /**
   * Post-check, called after the fact queue of the theory is processed.
   */
  void postCheck(Effort level = EFFORT_FULL) override;

 private:
  /** The theory rewriter for this theory. */
  NullablesRewriter d_rewriter;
  /** The state at full effort */
  SolverState d_state;
  /** The inference manager */
  InferenceManagerBuffered d_im;
  /** the main solver for nullables */
  NullablesSolver d_solver;
}; /* class TheoryNullables */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_NULLABLES_H */

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
}; /* class TheoryNullables */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_NULLABLES_H */

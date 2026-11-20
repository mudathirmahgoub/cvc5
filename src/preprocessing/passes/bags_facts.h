/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bags-facts preprocessing pass.
 *
 * Records the keys and NOT NULL columns of tables that the top-level
 * assertions state, before any assertion is rewritten, so that the bags
 * rewriter uses facts that hold and only those, see
 * theory::bags::BagsRewriter::recordFacts.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BAGS_FACTS_H
#define CVC5__PREPROCESSING__PASSES__BAGS_FACTS_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class BagsFacts : public PreprocessingPass
{
 public:
  BagsFacts(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Reads the facts off the assertions, which it leaves unchanged. Does
   * nothing once a scope is pushed (by the user, or for the assumptions of a
   * check): an assertion of an inner scope does not hold after a pop, while
   * the facts, attributes of the table constants, would remain. The
   * assertions of the outermost scope are never popped. The facts are not
   * forgotten by reset-assertions either, nor are they local to one solver:
   * the attributes, like the rewriter's cache, belong to the node manager.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__BAGS_FACTS_H */

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
 */

#include "preprocessing/passes/bags_facts.h"

#include "preprocessing/assertion_pipeline.h"
#include "smt/env.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

BagsFacts::BagsFacts(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bags-facts")
{
}

PreprocessingPassResult BagsFacts::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // the solver pushes one level around everything (ContextManager::setup);
  // above it, an assertion of a pushed scope, or an assumption of a check, may
  // be popped while the fact would remain
  if (userContext()->getLevel() > 1)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  theory::bags::BagsRewriter* rewriter =
      dynamic_cast<theory::bags::BagsRewriter*>(
          d_env.getRewriter()->getTheoryRewriter(theory::THEORY_BAGS));
  if (rewriter == nullptr)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    rewriter->recordFacts((*assertionsToPreprocess)[i]);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

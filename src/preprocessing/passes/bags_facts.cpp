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

#include "options/bags_options.h"
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
  if (options().bags.bagsFacts != options::BagsFactsMode::ATTR
      || userContext()->getLevel() > 1)
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
  // The fact literals are rewritten before any fact is recorded, so the
  // rewriter caches the forms that state the facts: a fact is not rewritten to
  // true by itself later, which would let a model break it.
  std::vector<Node> lits;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    std::vector<Node> visit{(*assertionsToPreprocess)[i]};
    while (!visit.empty())
    {
      Node a = visit.back();
      visit.pop_back();
      if (a.getKind() == Kind::AND)
      {
        visit.insert(visit.end(), a.begin(), a.end());
        continue;
      }
      // only an equality of bags may state a fact; rewriting anything else
      // here would cache its normal form before the facts are known
      if (a.getKind() != Kind::EQUAL || !a[0].getType().isBag())
      {
        continue;
      }
      lits.push_back(rewrite(a));
    }
  }
  for (const Node& l : lits)
  {
    rewriter->recordFact(l);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the inference manager for the theory of bags.
 */

#include "theory/bags/inference_manager.h"

#include "theory/bags/solver_state.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

InferenceManager::InferenceManager(Env& env, Theory& t, SolverState& s)
    : InferenceManagerBuffered(env, t, s, "theory::bags::"),
      d_state(s),
      d_ipc(isProofEnabled() ? new InferProofCons(env) : nullptr)
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

void InferenceManager::doPending()
{
  doPendingFacts();
  if (d_state.isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    clearPendingLemmas();
    clearPendingPhaseRequirements();
    return;
  }
  doPendingLemmas();
  doPendingPhaseRequirements();
}

ProofGenerator* InferenceManager::notifyLemma(const Node& lem,
                                              InferenceId id,
                                              const Node& exp)
{
  if (d_ipc == nullptr)
  {
    return nullptr;
  }
  d_ipc->notifyLemma(lem, id, exp);
  return d_ipc.get();
}

void InferenceManager::addPendingLemmaWithProof(const Node& lem,
                                                InferenceId id)
{
  ProofGenerator* pg = notifyLemma(lem, id, d_true);
  addPendingLemma(lem, id, LemmaProperty::NONE, pg);
}

bool InferenceManager::lemmaWithProof(const Node& lem, InferenceId id)
{
  ProofGenerator* pg = notifyLemma(lem, id, d_true);
  return trustedLemma(TrustNode::mkTrustLemma(lem, pg), id);
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

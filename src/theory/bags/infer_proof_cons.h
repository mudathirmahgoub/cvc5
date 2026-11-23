/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__INFER_PROOF_CONS_H
#define CVC5__THEORY__BAGS__INFER_PROOF_CONS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"

namespace cvc5::internal {

class TheoryProofStepBuffer;

namespace theory {
namespace bags {

/**
 * A class that is responsible for proofs of the lemmas of the theory of bags.
 * Proofs are constructed lazily when asked for via getProofFor. This class
 * maintains a (user-context-dependent) mapping from lemmas to the inference
 * identifier and the premise they were sent with.
 *
 * For example, the lemma for (bag.union_disjoint A B) and an element e is
 *
 *   (= (bag.count e k) (+ (bag.count e A) (bag.count e B)))
 *
 * where k is the purification skolem of (bag.union_disjoint A B). Its proof is
 *
 *   ---------------------------------------------------------- BAGS_COUNT_DEF
 *   (= (bag.count e (bag.union_disjoint A B))
 *      (+ (bag.count e A) (bag.count e B)))
 *   ---------------------------------------------- MACRO_SR_PRED_TRANSFORM
 *   (= (bag.count e k) (+ (bag.count e A) (bag.count e B)))
 *
 * where the second step only replaces k by the term it purifies, without
 * rewriting.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, InferenceId> NodeInferenceMap;
  typedef context::CDHashMap<Node, Node> NodeExpMap;

 public:
  InferProofCons(Env& env);
  virtual ~InferProofCons() {}

  /**
   * Notify that lem was sent as a lemma for inference id, with premise exp.
   * The premise exp is true if lem has no premises, in which case lem is the
   * conclusion of the inference. Otherwise, lem is (=> exp conc), and exp is
   * the conjunction of the premises.
   */
  void notifyLemma(const Node& lem, InferenceId id, const Node& exp);

  /**
   * This returns the proof for lem, which must have been notified via
   * notifyLemma.
   */
  std::shared_ptr<ProofNode> getProofFor(Node lem) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /**
   * Main conversion routine. Ensures there is a proof of conc with free
   * assumptions assumps stored in psb.
   *
   * @param psb The step buffer to add the steps to
   * @param id The inference identifier
   * @param assumps The premises of the inference
   * @param conc The conclusion of the inference
   * @return true if we successfully added a proof of conc to psb
   */
  bool convert(TheoryProofStepBuffer& psb,
               InferenceId id,
               const std::vector<Node>& assumps,
               const Node& conc);
  /**
   * Ensure psb has a proof of conc, given a proof of src, where src and conc
   * have the same original form, i.e. conc may have purification skolems in
   * places where src has the terms they purify.
   */
  bool transformToSkolemForm(TheoryProofStepBuffer& psb,
                             const Node& src,
                             const Node& conc);
  /**
   * @param count A term of the form (bag.count e k)
   * @return (bag.count e t) if k is the purification skolem of t, and count
   * otherwise.
   */
  Node getUnpurifiedCount(const Node& count);
  /** Maps lemmas to the inference identifier they were sent with */
  NodeInferenceMap d_lemmaId;
  /** Maps lemmas to the premise they were sent with */
  NodeExpMap d_lemmaExp;
  /** The true node */
  Node d_true;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__INFER_PROOF_CONS_H */

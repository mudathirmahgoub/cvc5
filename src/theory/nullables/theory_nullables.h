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

#include "theory/care_pair_argument_callback.h"
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

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  /** preprocess rewrite */
  TrustNode ppRewrite(TNode atom, std::vector<SkolemLemma>& lems) override;
  //--------------------------------- end initialization

  /**
   * initialize nullable and count terms
   */
  void initialize();
  /**
   * collect nullables' representatives and all count terms.
   */
  void collectNullablesAndCountTerms();

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort effort) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  TrustNode explain(TNode) override;
  Node getCandidateModelValue(TNode) override;
  std::string identify() const override { return "THEORY_NULLABLES"; }
  void preRegisterTerm(TNode n) override;
  void presolve() override;
  void computeCareGraph() override;
  void processCarePairArgs(TNode a, TNode b) override;
  bool isCareArg(Node n, unsigned a);
  /** run strategy for effort e */
  void runStrategy(Theory::Effort e);
  /** run the given inference step */
  bool runInferStep(InferStep s, int effort);

 private:
  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public TheoryEqNotifyClass
  {
   public:
    NotifyClass(TheoryNullables& theory,
                TheoryInferenceManager& inferenceManager)

        : TheoryEqNotifyClass(inferenceManager), d_theory(theory)
    {
    }
    void eqNotifyNewClass(TNode n) override;
    void eqNotifyMerge(TNode n1, TNode n2) override;
    void eqNotifyDisequal(TNode n1, TNode n2, TNode reason) override;

   private:
    TheoryNullables& d_theory;
  };

  /** expand the definition of the nullable.choose operator */
  TrustNode expandChooseOperator(const Node& node,
                                 std::vector<SkolemLemma>& lems);

  /** The state of the nullables solver at full effort */
  SolverState d_state;
  /** The inference manager */
  InferenceManager d_im;
  /** Instance of the above class */
  NotifyClass d_notify;
  /** Statistics for the theory of nullables. */
  NullablesStatistics d_statistics;
  /** The theory rewriter for this theory. */
  NullablesRewriter d_rewriter;
  /** The term registry for this theory */
  TermRegistry d_termReg;
  /** the main solver for nullables */
  NullableSolver d_solver;

  /** the main solver for nullables */
  CardSolver d_cardSolver;

  /** The care pair argument callback, used for theory combination */
  CarePairArgumentCallback d_cpacb;
  /** map kinds to their terms. It is cleared during post check */
  std::map<Kind, std::vector<Node>> d_opMap;

  /** The representation of the strategy */
  Strategy d_strat;

  void eqNotifyNewClass(TNode n);
  void eqNotifyMerge(TNode n1, TNode n2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
}; /* class TheoryNullables */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_NULLABLES_H */

/*********************                                                        */
/*! \file theory_bags_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory implementation.
 **
 ** Bags theory implementation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_PRIVATE_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_PRIVATE_H

#include "theory/bags/solver_state.h"
#include "theory/bags/theory_bags_rewriter.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

/** Internal classes, forward declared here */
class TheoryBags;

class TheoryBagsPrivate
{
 public:
  TheoryBagsPrivate(TheoryBags& external,
                    context::Context* c,
                    context::UserContext* u);
  TheoryRewriter* getTheoryRewriter() { return &d_rewriter; }

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  void addSharedTerm(TNode);

  void check(Theory::Effort);

  bool collectModelInfo(TheoryModel* m);

  Node explain(TNode);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void preRegisterTerm(TNode node);

  Node expandDefinition(Node n);

  Theory::PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  void presolve();

  void propagate(Theory::Effort);

  /** Propagate out to output channel */
  bool propagate(TNode);

  /** get default output channel */
  OutputChannel* getOutputChannel();
  /** get the valuation */
  Valuation& getValuation();

  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  /** Assert fact holds in the current context with explanation exp.
  *
  * exp should be explainable by the equality engine of this class, and fact
  * should be a literal.
  */
  bool assertFact(Node fact, Node exp);

 private:
  /** generate and send out conflict node */
  void conflict(TNode, TNode);

  TheoryBags& d_external;

  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify
  {
    TheoryBagsPrivate& d_theory;

   public:
    NotifyClass(TheoryBagsPrivate& theory) : d_theory(theory) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override;
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyPreMerge(TNode t1, TNode t2) override;
    void eqNotifyPostMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
  } d_notify;

  /** The state of the bags solver at full effort */
  SolverState d_state;
  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;
  /** The theory rewriter for this theory. */
  TheoryBagsRewriter d_rewriter;
}; /* class TheoryBagsPrivate */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_PRIVATE_H */

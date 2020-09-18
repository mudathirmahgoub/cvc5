/*********************                                                        */
/*! \file theory_bags_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node_trie.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/bags/theory_bags_rewriter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

/** Internal classes, forward declared here */
class TheoryBags;

class TheoryBagsPrivate
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

 private:
  /**
   * Invoke the decision procedure for this theory, which is run at
   * full effort. This will either send a lemma or conflict on the output
   * channel of this class, or otherwise the current set of constraints is
   * satisfiable w.r.t. the theory of bags.
   */
  void fullEffortCheck();
  /**
   * Reset the information for a full effort check.
   */
  void fullEffortReset();
  /**
   * This ensures that subtype constraints are met for all set terms. In
   * particular, for a set equivalence class E, let Set(T) be the most
   * common type among the types of terms in that class. In other words,
   * if E contains two terms of Set(Int) and Set(Real), then Set(Int) is the
   * most common type. Then, for each membership x in S where S is a set in
   * this equivalence class, we ensure x has type T by asserting:
   *   x = k
   * for a fresh constant k of type T. This is done only if the type of x is not
   * a subtype of Int (e.g. if x is of type Real). We call k the "type
   * constraint skolem for x of type Int".
   */
  void checkSubtypes();

  /**
   * This implements a strategy for splitting for set disequalities which
   * roughly corresponds the BAG DISEQUALITY rule from Bansal et al IJCAR 2016.
   */
  void checkDisequalities();

  Node d_true;
  Node d_false;
  Node d_zero;
  NodeBoolMap d_deq;
  /**
   * The set of terms that we have reduced via a lemma in the current user
   * context.
   */
  NodeSet d_termProcessed;

  // propagation
  class EqcInfo
  {
   public:
    EqcInfo(context::Context* c);
    ~EqcInfo() {}
    // singleton or emptyset equal to this eqc
    context::CDO<Node> d_singleton;
  };
  /** information necessary for equivalence classes */
  std::map<Node, EqcInfo*> d_eqc_info;
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo(TNode n, bool doMake = false);

  /** full check incomplete
   *
   * This flag is set to true during a full effort check if this theory
   * is incomplete for some reason (for instance, if we combine cardinality
   * with a relation or extended function kind).
   */
  bool d_full_check_incomplete;
  std::map<Node, TypeNode> d_most_common_type;
  std::map<Node, Node> d_most_common_type_term;

 public:
  /**
   * Constructs a new instance of TheoryBagsPrivate w.r.t. the provided
   * contexts.
   */
  TheoryBagsPrivate(TheoryBags& external,
                    SolverState& state,
                    InferenceManager& im,
                    SkolemCache& skc);

  ~TheoryBagsPrivate();

  TheoryRewriter* getTheoryRewriter() { return &d_rewriter; }

  /** Get the solver state */
  SolverState* getSolverState() { return &d_state; }

  /**
   * Finish initialize, called after the equality engine of theory bags has
   * been determined.
   */
  void finishInit();

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Theory::Effort level);
  /** Notify new fact */
  void notifyFact(TNode atom, bool polarity, TNode fact);
  //--------------------------------- end standard check

  /** Collect model values in m based on the relevant terms given by termSet */
  void addSharedTerm(TNode);
  bool collectModelValues(TheoryModel* m, const std::set<Node>& termSet);

  void computeCareGraph();

  Node explain(TNode);

  void preRegisterTerm(TNode node);

  /** expandDefinition
   * If the bags-ext option is not set and we have an extended operator,
   * we throw an exception. This function is a no-op otherwise.
   *
   * TheoryBags uses expandDefinition as an entry point to see if the input
   * contains extended operators.
   *
   * We need to be notified when a universe set occurs in our input,
   * before preprocessing and simplification takes place. Otherwise the models
   * may be inaccurate when bagsExt is false, here is an example:
   *
   * x,y : (Set Int)
   * x = (as univset (Set Int));
   * 0 in y;
   * check-sat;
   *
   * If bagsExt is enabled, the model value of (as univset (Set Int)) is always
   * accurate.
   *
   * If bagsExt is not enabled, the following can happen for the above example:
   * x = (as univset (Set Int)) is made into a model substitution during
   * simplification. This means (as univset (Set Int)) is not a term in any
   * assertion, and hence we do not throw an exception, nor do we infer that 0
   * is a member of (as univset (Set Int)). We instead report a model where x =
   * {}. The correct behavior is to throw an exception that says universe set is
   * not supported when bagsExt disabled. Hence we check for the existence of
   * universe set before simplification here.
   *
   * Another option to fix this is to make TheoryModel::getValue more general
   * so that it makes theory-specific calls to evaluate interpreted symbols.
   */
  TrustNode expandDefinition(Node n);

  void presolve();

  /** get default output channel */
  OutputChannel* getOutputChannel();
  /** get the valuation */
  Valuation& getValuation();

  /** Proagate out to output channel */
  bool propagate(TNode);

  /** generate and send out conflict node */
  void conflict(TNode, TNode);

 private:
  TheoryBags& d_external;
  /** The state of the bags solver at full effort */
  SolverState& d_state;
  /** The inference manager of the bags solver */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** The term registry */
  TermRegistry d_treg;

  /** Pointer to the equality engine of theory of bags */
  eq::EqualityEngine* d_equalityEngine;

  bool isCareArg(Node n, unsigned a);

 public:
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) { return d_state.isEntailed(n, pol); }

 private:
  /** get choose function
   *
   * Returns the existing uninterpreted function for the choose operator for the
   * given set type, or creates a new one if it does not exist.
   */
  Node getChooseFunction(const TypeNode& setType);
  /** expand the definition of the choose operator */
  TrustNode expandChooseOperator(const Node& node);
  /** expand the definition of is_singleton operator */
  TrustNode expandIsSingletonOperator(const Node& node);
  /** is cardinality enabled?
   *
   * This flag is set to true during a full effort check if any constraint
   * involving cardinality constraints is asserted to this theory.
   */
  bool d_card_enabled;

  /** The theory rewriter for this theory. */
  TheoryBagsRewriter d_rewriter;

  /** a map that stores the choose functions for set types */
  std::map<TypeNode, Node> d_chooseFunctions;

  /** a map that maps each set to an existential quantifier generated for
   * operator is_singleton */
  std::map<Node, Node> d_isSingletonNodes;
}; /* class TheoryBagsPrivate */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_PRIVATE_H */

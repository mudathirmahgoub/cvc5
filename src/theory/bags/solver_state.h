/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H
#define CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "theory/bags/skolem_cache.h"
#include "theory/sets/inference_manager.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBagsPrivate;

/** Bags state
 *
 * The purpose of this class is to:
 * (1) Maintain information concerning the current set of assertions during a
 * full effort check,
 * (2) Maintain a database of commonly used terms.
 *
 * During a full effort check, the solver for theory of bags should call:
 *   reset; ( registerEqc | registerTerm )*
 * to initialize the information in this class regarding full effort checks.
 * Other query calls are then valid for the remainder of the full effort check.
 */
class SolverState : public State
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

 public:
  SolverState(TheoryBagsPrivate& p,
              eq::EqualityEngine& e,
              context::Context* c,
              context::UserContext* u);
  //-------------------------------- initialize
  /** reset, clears the data structures maintained by this class. */
  void reset();
  /** register equivalence class whose type is tn */
  void registerEqc(TypeNode tn, Node r);
  /** register term n of type tnn in the equivalence class of r */
  void registerTerm(Node r, TypeNode tnn, Node n);
  //-------------------------------- end initialize
  /** Are we currently in conflict? */
  bool isInConflict() const { return d_conflict; }
  /**
   * Indicate that we are in conflict, without a conflict clause. This is
   * called, for instance, when we have propagated a conflicting literal.
   */
  void setConflict();
  /** Set conf is a conflict node to be sent on the output channel.  */
  void setConflict(Node conf);
  /** Is a=b according to equality reasoning in the current context? */
  bool areEqual(Node a, Node b) const;
  /** Is a!=b according to equality reasoning in the current context? */
  bool areDisequal(Node a, Node b) const;
  /** add equality to explanation
   *
   * This adds a = b to exp if a and b are syntactically disequal. The equality
   * a = b should hold in the current context.
   */
  void addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const;
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) const;
  /**
   * Is the disequality between bags s and t entailed in the current context?
   */
  bool isBagDisequalityEntailed(Node s, Node t) const;

  /** Get the empty bag of type tn */
  Node getEmptyBag(TypeNode tn);
  /** Get the list of all equivalence classes of bags terms */
  const std::vector<Node>& getBagsEqClasses() const { return d_bag_eqc; }
  /** Get the list of all equivalence classes of bag terms that have element
   * type t */
  const std::vector<Node> getBagsEqClasses(const TypeNode& t) const;
  /**
   * Get the equivalence class of the empty bag of type tn, or null if it does
   * not exist as a term in the current context.
   */
  Node getEmptyBagEqClass(TypeNode tn) const;
  /**
   * Get a variable bag in the equivalence class with representative r, or null
   * if none exist.
   */
  Node getVariableBag(Node r) const;

  /**
   * Get the skolem cache of this theory, which manages a database of introduced
   * skolem variables used for various inferences.
   */
  SkolemCache& getSkolemCache() { return d_skCache; }

 private:
  /** constants */
  Node d_true;
  Node d_false;

  /** Whether or not we are in conflict. This flag is SAT context dependent. */
  context::CDO<bool> d_conflict;
  /** Reference to the parent theory of bags */
  TheoryBagsPrivate& d_parent;
  /** Reference to the equality engine of theory of bags */
  eq::EqualityEngine& d_ee;
  /** The list of all equivalence classes of type bag in the current context */
  std::vector<Node> d_bag_eqc;
  /** Maps types to the equivalence class containing empty bag of that type */
  std::map<TypeNode, Node> d_eqc_emptybag;

  /** Map from types to empty bag of that type */
  std::map<TypeNode, Node> d_emptybag;
  /** Map from equivalence classes to a variable sets in it */
  std::map<Node, Node> d_var_bag;
  /** the skolem cache */
  SkolemCache d_skCache;

  // --------------------------------------- end commonly used terms

  /** is bag disequality entailed internal
   *
   * This returns true if disequality between bags a and b is entailed in the
   * current context. We use an incomplete test based on equality and
   * multiplicity information.
   *
   * re is the representative of the equivalence class of the empty bag
   * whose type is the same as a and b.
   */
  bool isBagDisequalityEntailedInternal(Node a, Node b, Node re) const;
}; /* class TheoryBagsPrivate */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H */

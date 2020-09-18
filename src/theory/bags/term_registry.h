/*********************                                                        */
/*! \file term_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 ** \brief Bags state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__TERM_REGISTRY_H
#define CVC4__THEORY__BAGS__TERM_REGISTRY_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/skolem_cache.h"
#include "theory/bags/solver_state.h"

namespace CVC4 {
namespace theory {
namespace bags {

/**
 * Term registry, the purpose of this class is to maintain a database of
 * commonly used terms, and mappings from bags to their "proxy variables".
 */
class TermRegistry
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

 public:
  TermRegistry(SolverState& state, InferenceManager& im, SkolemCache& skc);
  /** Get type constraint skolem
   *
   * The bags theory solver outputs equality lemmas of the form:
   *   n = d_tc_skolem[n][tn]
   * where the type of d_tc_skolem[n][tn] is tn, and the type
   * of n is not a subtype of tn. This is required to handle benchmarks like
   *   test/regress/regress0/bags/bags-of-bags-subtypes.smt2
   * where for s : (Bag Int) and t : (Bag Real), we have that
   *   ( s = t ^ y in t ) implies ( exists k : Int. y = k )
   * The type constraint Skolem for (y, Int) is the skolemization of k above.
   */
  Node getTypeConstraintSkolem(Node n, TypeNode tn);
  /** get the proxy variable for bag n
   *
   * Proxy variables are used to communicate information that otherwise would
   * not be possible due to rewriting. For example, the literal
   *   card( singleton( 0 ) ) = 1
   * is rewritten to true. Instead, to communicate this fact (e.g. to other
   * theories), we require introducing a proxy variable x for singleton( 0 ).
   * Then:
   *   card( x ) = 1 ^ x = singleton( 0 )
   * communicates the equivalent of the above literal.
   */
  Node getProxy(Node n);
  /** Get the empty bag of type tn */
  Node getEmptyBag(TypeNode tn);

 private:
  /** The inference manager */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** Map from bag terms to their proxy variables */
  NodeMap d_proxy;
  /** Backwards map of above */
  NodeMap d_proxy_to_term;
  /** Cache of type constraint skolems (see getTypeConstraintSkolem) */
  std::map<Node, std::map<TypeNode, Node> > d_tc_skolem;
  /** Map from types to empty bag of that type */
  std::map<TypeNode, Node> d_emptybag;
}; /* class Term */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__TERM_REGISTRY_H */

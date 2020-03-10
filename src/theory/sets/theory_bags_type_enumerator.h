/*********************                                                        */
/*! \file theory_bags_type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andrew Reynolds, Mudathir Mahgoub
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief type enumerator for bags
 **
 ** A bag enumerator that iterates over bags
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/rewriter.h"
#include "theory/sets/normal_form.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sets {

class BagEnumerator : public TypeEnumeratorBase<BagEnumerator>
{
 public:
  BagEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  BagEnumerator(const BagEnumerator& enumerator);
  ~BagEnumerator();

  Node operator*() override;

  /**
   * This operator iterates over the power set of the element type
   * following the order of a bitvector counter.
   * Example: iterating over a set of bitvecotors of length 2 will return the
   * following sequence consisting of 16 sets:
   * {}, {00}, {01}, {00, 01}, {10}, {00, 10}, {01, 10}, {00, 01, 10}, ...,
   * {00, 01, 10, 11}
   */
  BagEnumerator& operator++() override;

  bool isFinished() override;

 private:
  /** a pointer to the node manager */
  NodeManager* d_nodeManager;
  /** an enumerator for the elements' type */
  TypeEnumerator d_elementEnumerator;
  /** a boolean to indicate whether the set enumerator is finished */
  bool d_isFinished;
  /** a list of the elements encountered so far */
  std::vector<Node> d_elementsSoFar;
  /** stores the index of the current set in the power set */
  unsigned d_currentBagIndex;
  /** the current set returned by the set enumerator */
  Node d_currentBag;
}; /* class BagEnumerator */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__TYPE_ENUMERATOR_H */

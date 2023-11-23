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
 * Type enumerator for nullables
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__TYPE_ENUMERATOR_H
#define CVC5__THEORY__NULLABLES__TYPE_ENUMERATOR_H

#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

class NullableEnumerator : public TypeEnumeratorBase<NullableEnumerator>
{
 public:
  NullableEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  NullableEnumerator(const NullableEnumerator& enumerator);
  ~NullableEnumerator();

  Node operator*() override;

  /**
   * This operator iterates over the nullables constructed from the element
   * type.
   */
  NullableEnumerator& operator++() override;

  bool isFinished() override;

 private:
  /** a pointer to the node manager */
  NodeManager* d_nodeManager;
  /** an enumerator for the set of pairs of element type x integer type */
  TypeEnumerator d_elementTypeEnumerator;
  /** the current set returned by the set enumerator */
  Node d_currentNullable;
  /** the first value returned by the element type enumerator*/
  Node d_element;
}; /* class NullableEnumerator */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__TYPE_ENUMERATOR_H */

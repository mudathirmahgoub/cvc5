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
 * Nullables theory type rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__THEORY_NULLABLES_TYPE_RULES_H
#define CVC5__THEORY__NULLABLES__THEORY_NULLABLES_TYPE_RULES_H

#include "expr/node.h"

namespace cvc5::internal {

class NodeManager;
class TypeNode;

namespace theory {
namespace nullables {

/**
 * Type rule for (as nullable.null (Nullable T)) where T is a type
 */
struct NullTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct NullTypeRule */

/**
 * Table project is indexed by a list of indices (n_1, ..., n_m). It ensures
 * that the argument is a nullable of tuples whose arity k is greater than each
 * n_i for i = 1, ..., m. If the argument is of type (Table T_1 ... T_k), then
 * the returned type is (Table T_{n_1} ... T_{n_m}).
 */
struct NullableLiftTypeRule
{
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
}; /* struct NullableLiftTypeRule */

struct NullablesProperties
{
  static Cardinality computeCardinality(TypeNode type);

  static bool isWellFounded(TypeNode type);

  static Node mkGroundTerm(TypeNode type);
}; /* struct NullablesProperties */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_NULLABLES_TYPE_RULES_H */

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
 * A class for LiftOp operator.
 */

#include "cvc5_private.h"
#include "expr/node.h"
#ifndef CVC5__LIFTOP_H
#define CVC5__LIFTOP_H

#include <ostream>
#include <vector>

namespace cvc5::internal {

class TypeNode;

/**
 * class for lift operator
 */
class LiftOp
{
 public:
  explicit LiftOp(Kind kind);
  LiftOp(const LiftOp& op) = default;

  /** return the kind of the lift operator*/
  const Kind getKind() const;

  bool operator==(const LiftOp& op) const;

 public:
  Kind d_kind;
}; /* class LiftOp */

std::ostream& operator<<(std::ostream& out, const LiftOp& op);

/**
 * Hash function for the LiftOpHashFunction objects.
 */
struct LiftOpHashFunction
{
  size_t operator()(const LiftOp& op) const;
}; /* struct LiftOpHashFunction */

}  // namespace internal

#endif /* CVC5__LIFTOP_H */

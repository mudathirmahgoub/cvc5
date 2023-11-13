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

#include "cvc5_public.h"

#ifndef CVC5__PROJECT_OP_H
#define CVC5__PROJECT_OP_H

#include <ostream>
#include <vector>

namespace cvc5::nullables {

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

 private:
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

}  // namespace cvc5::nullables

#endif /* CVC5__PROJECT_OP_H */

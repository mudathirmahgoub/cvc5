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

#include "lift_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const LiftOp& op)
{
  // should only be used for debugging, not in the smt2 printer.
  out << "(LiftOp "
      << ")";
  return out;
}

size_t LiftOpHashFunction::operator()(const LiftOp& op) const
{
  return static_cast<size_t>(op.d_kind);
}

LiftOp::LiftOp(Kind kind) : d_kind(kind) {}

const Kind LiftOp::getKind() const { return d_kind; }

bool LiftOp::operator==(const LiftOp& op) const { return d_kind == op.d_kind; }

}  // namespace cvc5::internal

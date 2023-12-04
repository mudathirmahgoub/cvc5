/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type for rewrites for nullables.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__REWRITES_H
#define CVC5__THEORY__NULLABLES__REWRITES_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {
namespace nullables {

/** Types of rewrites used by nullables
 *
 * This rewrites are documented where they are used in the rewriter.
 */
enum class Rewrite : uint32_t
{
  NONE,             // no rewrite happened
  IDENTICAL_NODES,  // identical nodes
  ISNULL,
  SELECT_VALUE,
  LIFT_NULL,
  LIFT_SOME,
  EQ_REFL,
  EQ_CONST_FALSE,
  EQ_SYM
};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__REWRITES_H */

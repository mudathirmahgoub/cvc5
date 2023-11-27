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
 * Implementation of inference information utility.
 */

#include "theory/nullables/rewrites.h"

#include <iostream>

namespace cvc5::internal {
namespace theory {
namespace nullables {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::NONE: return "NONE";

    case Rewrite::EQ_CONST_FALSE: return "EQ_CONST_FALSE";
    case Rewrite::EQ_REFL: return "EQ_REFL";
    case Rewrite::EQ_SYM: return "EQ_SYM";

    case Rewrite::IDENTICAL_NODES: return "IDENTICAL_NODES";
    case Rewrite::SELECT_VALUE: return "SELECT_VALUE";

    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

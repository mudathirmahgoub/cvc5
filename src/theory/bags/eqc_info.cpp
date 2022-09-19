/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equivalence class info for the theory of bags.
 */

#include "theory/bags/eqc_info.h"

#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

EqcInfo::EqcInfo(context::Context* c, Node eqc)
    : d_term(eqc), d_firstBound(c), d_secondBound(c)
{
  Assert(!eqc.isNull());
}

bool EqcInfo::addBoundConst(Node t, Node c, bool isLowerBound, Node& conflict)
{
  if (c.isNull())
  {
    return false;
  }

  Rational cRational = c.getConst<Rational>();
  Node otherBound = isLowerBound ? d_secondBound : d_firstBound;
  Node previousBound = isLowerBound ? d_firstBound : d_secondBound;
  NodeManager* nm = NodeManager::currentNM();
  if (!otherBound.isNull())
  {
    // check if there is a conflict with the other bound
    Rational otherRational = otherBound.getConst<Rational>();
    if ((isLowerBound && cRational > otherRational)
        || (!isLowerBound && cRational < otherRational))
    {
      // return a conflict if the new lower bound is strictly greater than the
      // current upper bound, or the new upper bound is strictly smaller than
      // the current lower bound
      // TODO: construct an explanation for the conflict.
      conflict = nm->mkConst(false);
      return false;
    }
  }

  if (previousBound.isNull())
  {
    if (isLowerBound)
    {
      d_firstBound = c;
      return true;
    }
    d_secondBound = c;
    return true;
  }
  // only update the bound if it tightens the interval
  Rational previousRational = previousBound.getConst<Rational>();
  if (isLowerBound && previousRational < cRational)
  {
    d_firstBound = c;
    return true;
  }
  if (!isLowerBound && previousRational > cRational)
  {
    d_secondBound = c;
    return true;
  }
  return false;
}

std::ostream& operator<<(std::ostream& out, const EqcInfo& ei)
{
  out << "(EqcInfo " << ei.d_firstBound.get() << " <= " << ei.d_term
      << " <= " << ei.d_secondBound.get() << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

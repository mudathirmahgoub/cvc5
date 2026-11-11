/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lattice points of a rational polyhedron, as module generators over the
 * recession monoid.
 */

#include "theory/arith/liastar/integer_polyhedron.h"

#include <algorithm>
#include <sstream>

#include "base/check.h"
#include "base/output.h"
#include "theory/arith/liastar/dual_hilbert_basis.h"
#include "theory/arith/liastar/lattice_basis.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

IntegerPolyhedron::IntegerPolyhedron(const LinearConstraints& constraints)
    : d_numSums(0)
{
  size_t n = constraints.getNumVariables();
  // the homogenizing coordinate x_{n+1} is the level
  IntegerVector levelForm = IntegerVectorUtils::unit(n + 1, n);
  DualHilbertBasis dual(n + 1,
                        constraints.getEquations(),
                        constraints.getInequalities(),
                        levelForm);
  dual.compute();
  d_numSums = dual.getNumSums();
  if (!dual.hasLevelOneElements())
  {
    // no integer solutions
    return;
  }
  // the units have level 0, and canonical representatives modulo them are
  // taken with respect to their Hermite normal form
  LatticeBasis units = dual.getUnits();
  units.toHermiteNormalForm();
  for (IntegerVector x : dual.getHilbertBasis())
  {
    units.reduceModulo(x);
    Integer level = x[n];
    x.pop_back();
    if (level.isZero())
    {
      d_hilbertBasis.push_back(x);
    }
    else
    {
      Assert(level.isOne());
      d_moduleGenerators.push_back(x);
    }
  }
  for (IntegerVector u : units.getBasis())
  {
    Assert(u[n].isZero());
    u.pop_back();
    d_maximalSubspace.push_back(u);
  }
  std::sort(d_moduleGenerators.begin(),
            d_moduleGenerators.end(),
            IntegerVectorUtils::lessByNorm);
  std::sort(d_hilbertBasis.begin(),
            d_hilbertBasis.end(),
            IntegerVectorUtils::lessByNorm);
}

std::vector<IntegerVector> IntegerPolyhedron::getRecessionMonoidGenerators()
    const
{
  std::vector<IntegerVector> generators = d_hilbertBasis;
  generators.insert(
      generators.end(), d_maximalSubspace.begin(), d_maximalSubspace.end());
  return generators;
}

std::string IntegerPolyhedron::toString() const
{
  std::stringstream ss;
  ss << "module generators " << IntegerVectorUtils::toString(d_moduleGenerators)
     << ", Hilbert basis " << IntegerVectorUtils::toString(d_hilbertBasis)
     << ", maximal subspace "
     << IntegerVectorUtils::toString(d_maximalSubspace);
  return ss.str();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

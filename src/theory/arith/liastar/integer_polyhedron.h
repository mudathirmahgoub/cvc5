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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__INTEGER_POLYHEDRON_H
#define CVC5__THEORY__ARITH__LIASTAR__INTEGER_POLYHEDRON_H

#include <string>
#include <vector>

#include "theory/arith/liastar/integer_vector.h"
#include "theory/arith/liastar/linear_constraints.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * The integer solutions S = P ∩ Z^n of a conjunction of linear constraints
 * (a LinearConstraints), where P is the rational polyhedron they define, in
 * the form that the liastar extension needs to express the star S* in linear
 * arithmetic:
 *
 *   S = union over g in G of  { g + sum_i l_i h_i + sum_j m_j u_j :
 *                               l_i >= 0 and m_j integers }
 *
 * where
 * - G is the set of module generators (getModuleGenerators),
 * - h_1, ..., h_k is the Hilbert basis of the recession monoid, the integer
 *   points of the recession cone {x : x + P ⊆ P}, modulo its maximal linear
 *   subspace (getHilbertBasis), and
 * - u_1, ..., u_r is a basis of the integer points of that maximal subspace
 *   (getMaximalSubspace).
 * S is empty if and only if G is empty. This is what Normaliz computes for
 * the input properties ModuleGenerators, HilbertBasis and MaximalSubspace,
 * with one difference: Normaliz reports no module generators for a
 * homogeneous input (a cone), where G = {0} here.
 *
 * Algorithm (Section 9 of the Normaliz notes in paper-fmcad26-liastar/
 * normaliz). The constraints are homogenized: each row
 * (a_1, ..., a_n, b) becomes the linear form a_1 x_1 + ... + a_n x_n
 * + b x_{n+1} on Z^{n+1}. Its cone C contains the points (x, 1) for x in P
 * at level x_{n+1} = 1, and the recession cone at level 0. A point (x, 1) of
 * the monoid C ∩ Z^{n+1} is irreducible exactly when x is a minimal module
 * generator, and a point (x, 0) when x is in the Hilbert basis of the
 * recession monoid. DualHilbertBasis computes these irreducible points of
 * level at most 1 with the level form x_{n+1}; the units of the monoid are
 * the points of the maximal subspace. Finally every result is reduced modulo
 * the maximal subspace (LatticeBasis::reduceModulo), which makes it
 * independent of the order of the computation, and the results are sorted.
 *
 * Example (2cone_int.in, Section 9.6 of the notes): the integer points with
 * -x + 2y > 0 and 3x - y > 0 are S = ((1, 1) + M) ∪ ((1, 2) + M) with the
 * recession monoid M = Z>=0 {(1, 1), (2, 1), (1, 2), (1, 3)}.
 *
 * Example with a maximal subspace: x + y = 2 gives G = {(0, 2)}, an empty
 * Hilbert basis and the maximal subspace {(1, -1)}, i.e.
 * S = {(0, 2) + m (1, -1) : m integer}.
 *
 * Example of an empty S: x = 2z and x = 2w + 1 have rational solutions but no
 * integer one, so G is empty. (Normaliz reports affine dimension 0 for this
 * polyhedron.)
 */
class IntegerPolyhedron
{
 public:
  /** Compute the integer solutions of the given constraints. */
  explicit IntegerPolyhedron(const LinearConstraints& constraints);

  /** @return whether there are no integer solutions */
  bool isEmpty() const { return d_moduleGenerators.empty(); }
  /** @return the module generators G, sorted; empty iff isEmpty() */
  const std::vector<IntegerVector>& getModuleGenerators() const
  {
    return d_moduleGenerators;
  }
  /**
   * @return the Hilbert basis of the recession monoid modulo the maximal
   * subspace, sorted; empty if isEmpty()
   */
  const std::vector<IntegerVector>& getHilbertBasis() const
  {
    return d_hilbertBasis;
  }
  /**
   * @return a basis of the integer points of the maximal linear subspace of
   * the recession cone, in Hermite normal form; empty if isEmpty()
   */
  const std::vector<IntegerVector>& getMaximalSubspace() const
  {
    return d_maximalSubspace;
  }
  /**
   * @return the Hilbert basis followed by the maximal subspace basis. These
   * generate the recession monoid when the first getHilbertBasis().size()
   * of them take nonnegative multipliers and the others take arbitrary
   * integer multipliers, since a direction of the maximal subspace can be
   * followed both ways. (Adding both u and -u for each u in the maximal
   * subspace instead would also generate it, but give every point infinitely
   * many representations.)
   */
  std::vector<IntegerVector> getRecessionMonoidGenerators() const;
  /** @return the number of sums formed by the dual algorithm */
  size_t getNumSums() const { return d_numSums; }
  /** @return the results as a string, for tracing */
  std::string toString() const;

 private:
  /** The module generators. */
  std::vector<IntegerVector> d_moduleGenerators;
  /** The Hilbert basis of the recession monoid. */
  std::vector<IntegerVector> d_hilbertBasis;
  /** A basis of the maximal subspace. */
  std::vector<IntegerVector> d_maximalSubspace;
  /** The number of sums formed by the dual algorithm. */
  size_t d_numSums;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__INTEGER_POLYHEDRON_H */

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A Z-basis of a sublattice of Z^d.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__LATTICE_BASIS_H
#define CVC5__THEORY__ARITH__LIASTAR__LATTICE_BASIS_H

#include <vector>

#include "theory/arith/liastar/integer_vector.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * A Z-basis u_1, ..., u_r of a sublattice L of Z^d, i.e. every point of L is
 * m_1 u_1 + ... + m_r u_r for unique integers m_1, ..., m_r.
 *
 * The dual algorithm (DualHilbertBasis) uses this class for two lattices:
 * - the solutions {x in Z^d : e(x) = 0 for every equation e}, and
 * - the unit group of the current monoid M = D ∩ L, i.e. the lattice points
 *   of the largest linear subspace contained in the current cone D. When D
 *   is cut with a halfspace a(x) >= 0, the unit group shrinks to the points
 *   u with a(u) = 0 (steps (D1)-(D2) of [BI, Section 7], Section 8.2.1 of the
 *   Normaliz notes in paper-fmcad26-liastar/normaliz).
 * Both are computed with intersectWithKernel.
 *
 * [BI] W. Bruns, B. Ichim. Normaliz: algorithms for affine monoids and
 *      rational cones. J. Algebra 324 (2010). arXiv:0910.2845.
 */
class LatticeBasis
{
 public:
  /** Construct the standard basis e_1, ..., e_d of Z^d. */
  explicit LatticeBasis(size_t dimension);
  /**
   * Construct the lattice spanned by the given linearly independent vectors
   * of Z^d.
   */
  LatticeBasis(size_t dimension, const std::vector<IntegerVector>& basis);
  /** @return the dimension d of the ambient space Z^d */
  size_t getDimension() const { return d_dimension; }
  /** @return the rank r of the lattice, i.e. the number of basis vectors */
  size_t getRank() const { return d_basis.size(); }
  /** @return the basis vectors u_1, ..., u_r */
  const std::vector<IntegerVector>& getBasis() const { return d_basis; }

  /**
   * Restrict this lattice L to its points on the hyperplane a(x) = 0, i.e.
   * replace L by K = {u in L : a(u) = 0}.
   *
   * If a vanishes on L, then K = L and nothing changes. Otherwise the rank
   * drops by one, and the method also returns a complement h: a point of L
   * with a(h) = g > 0, where g is the smallest positive value of a on L
   * (the gcd of a(u_1), ..., a(u_r)), such that h together with the new
   * basis is a basis of the old L. Every point of L is then m h + k for a
   * unique integer m and point k of K.
   *
   * The computation is the Euclidean algorithm on the values a(u_i), where
   * every step "a(u_j) -= q a(u_i)" is mirrored by "u_j -= q u_i". These are
   * unimodular changes of basis, so the vectors always form a basis of L.
   *
   * Example: L = Z^2 with basis (1, 0), (0, 1), and a = (2, 3). The values
   * are 2 and 3; the step u_2 -= u_1 gives the values 2, 1, and the step
   * u_1 -= 2 u_2 gives the values 0, 1. The result is the kernel basis
   * {(3, -2)} and the complement h = (-1, 1) with a(h) = 1 = gcd(2, 3).
   *
   * @param a a linear form on Z^d
   * @return the complement h, or the empty vector if a vanishes on L
   */
  IntegerVector intersectWithKernel(const IntegerVector& a);

  /**
   * Replace the basis by the (row) Hermite normal form of the matrix whose
   * rows are the basis vectors. This basis is uniquely determined by the
   * lattice: the rows are in echelon form, every pivot (the first nonzero
   * entry of a row) is positive, and every entry above a pivot is
   * nonnegative and smaller than the pivot.
   *
   * Example: the basis {(3, -2), (-1, 1)} of Z^2 becomes {(1, 0), (0, 1)},
   * and the basis {(2, 2, 0), (1, 1, 1)} becomes {(1, 1, 1), (0, 0, 2)}.
   */
  void toHermiteNormalForm();

  /**
   * Replace x by the canonical representative of the coset x + L, assuming
   * the basis is in Hermite normal form: for every basis vector with pivot p
   * in column c, x[c] is brought into the range 0 <= x[c] < p.
   *
   * Example: with L = Z (1, -1), the point (5, -4) becomes (0, 1).
   */
  void reduceModulo(IntegerVector& x) const;

  /** @return the basis as a string, e.g. "{(1, -1)}" */
  std::string toString() const;

 private:
  /**
   * Run the Euclidean algorithm on the values of `values`, mirroring each
   * step on the corresponding vectors of `vectors`, until at most one value
   * is nonzero.
   *
   * @param vectors the vectors, changed by unimodular row operations
   * @param values the values of a linear form at `vectors`, updated with them
   * @return the index of the only nonzero value, or vectors.size() if all
   * values are zero
   */
  static size_t euclid(std::vector<IntegerVector>& vectors,
                       std::vector<Integer>& values);
  /** The dimension d of the ambient space Z^d. */
  size_t d_dimension;
  /** The basis vectors. */
  std::vector<IntegerVector> d_basis;
  /**
   * The pivot column of each basis vector, set by toHermiteNormalForm and
   * used by reduceModulo.
   */
  std::vector<size_t> d_pivots;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__LATTICE_BASIS_H */

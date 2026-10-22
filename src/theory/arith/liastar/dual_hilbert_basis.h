/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Hilbert bases of cones given by linear constraints, computed with the dual
 * algorithm.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__DUAL_HILBERT_BASIS_H
#define CVC5__THEORY__ARITH__LIASTAR__DUAL_HILBERT_BASIS_H

#include <vector>

#include "theory/arith/liastar/integer_vector.h"
#include "theory/arith/liastar/lattice_basis.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * Computes the Hilbert basis of the monoid M = C ∩ L, where
 *
 *   C = {x in R^d : a(x) >= 0 for every inequality a}  is a rational cone,
 *   L = {x in Z^d : e(x) = 0 for every equation e}      is a lattice,
 *
 * with Pottier's dual algorithm, as described by Bruns and Ichim [BI,
 * Section 7] and implemented by Normaliz in cone_dual_mode.cpp (its
 * DualMode). It works directly on constraints, which is the input of the
 * liastar extension, so unlike Normaliz's primal algorithm it needs no
 * conversion to generators by Fourier-Motzkin elimination and no
 * triangulation. The notes in paper-fmcad26-liastar/normaliz
 * (normaliz_algorithms.pdf) explain it in Sections 5 (reduction), 8 (the
 * dual algorithm) and 9 (module generators); the step names (D1)-(D8) below
 * are those of [BI] and of Section 8.2 of the notes.
 *
 * Definitions. The units of M are the points u with -u also in M; they form
 * the lattice U of points of the largest linear subspace in C. A point of M
 * that is not a unit is irreducible if it is not the sum of two non-units of
 * M. The Hilbert basis H of M is a set of representatives of the irreducible
 * points modulo U; it is finite and generates M modulo the units:
 *
 *   M = {h_1 + ... + h_k + u : k >= 0, h_i in H, u in U}.
 *
 * If C contains no line then U = {0} and H is unique.
 *
 * The algorithm starts with the cone R^d, whose monoid L has U = L and
 * H = {}, and cuts it with one halfspace a(x) >= 0 at a time, keeping H and a
 * basis of U up to date:
 *
 * - (D1)-(D2): if a does not vanish on U, U shrinks to {u in U : a(u) = 0},
 *   and the complement h of LatticeBasis::intersectWithKernel, with
 *   a(h) = g > 0, stops being a unit.
 * - (D3)-(D5): each element x of H is reduced modulo h so that |a(x)| < g,
 *   and h and -h join the candidates.
 * - (D6)-(D8): the candidates are split by the sign of a into positive,
 *   negative and neutral ones. Repeatedly, every sum p + n of a positive and
 *   a negative candidate is formed, and kept if no candidate of its side
 *   and no neutral candidate reduces it, until no new candidate is kept.
 *   Then the positive and the neutral candidates are the Hilbert basis of
 *   the cut monoid.
 *
 * Reduction. A candidate y reduces a candidate x of the same side if x - y
 * is in that side's monoid, i.e. if b(y) <= b(x) for every form b cut so
 * far, where the current form a counts with its absolute value. Then x is
 * either reducible or x and y differ by a unit, and x is dropped. Every
 * candidate stores its value vector (b_1(x), ..., b_k(x), |a(x)|) so this
 * test is a componentwise comparison; the sum of the values is its degree,
 * and a reducer always has a degree no larger than that of the point it
 * reduces.
 *
 * Truncation. Given a level form l that is nonnegative on C, the algorithm
 * can instead compute only the Hilbert basis elements of level l(x) <= 1:
 * the form l is cut first, and sums of level 2 or more are never formed.
 * This is how the lattice points of a polyhedron are computed, see
 * IntegerPolyhedron.
 *
 * Example ([BI] Figure 5, and Section 8.7 of the notes, EX-CONE-INEQ):
 * C = {(x, y) : -x + 2y >= 0, 3x - y >= 0} and L = Z^2.
 * - Cut with a = (-1, 2). The units Z^2 shrink to Z (2, 1), the complement
 *   is h = (-1, 0) with a(h) = 1, and H = {(-1, 0)}: the halfplane is
 *   Z>=0 (-1, 0) + Z (2, 1).
 * - Cut with a = (3, -1). It does not vanish on (2, 1), so U becomes {0} and
 *   h = (2, 1) with a(h) = 5. The candidates are the positive (2, 1) and the
 *   negative (-1, 0) and (-2, -1). The sums of positive and negative
 *   candidates that survive reduction are (1, 1) in the first round, (0, 1)
 *   in the second, (1, 2) in the third and the neutral (1, 3) in the fourth,
 *   after which no new sum survives.
 * The result is H = {(2, 1), (1, 1), (1, 2), (1, 3)}, which is what Normaliz
 * reports for this cone (2cone_ineq.out).
 *
 * [BI] W. Bruns, B. Ichim. Normaliz: algorithms for affine monoids and
 *      rational cones. J. Algebra 324 (2010). arXiv:0910.2845.
 */
class DualHilbertBasis
{
 public:
  /**
   * @param dimension the dimension d of the ambient space Z^d
   * @param equations the linear forms e defining L by e(x) = 0
   * @param inequalities the linear forms a defining C by a(x) >= 0
   * @param levelForm a linear form l that is nonnegative on C, or the empty
   * vector. If given, only the Hilbert basis elements x with l(x) <= 1 are
   * computed.
   */
  DualHilbertBasis(size_t dimension,
                   const std::vector<IntegerVector>& equations,
                   const std::vector<IntegerVector>& inequalities,
                   const IntegerVector& levelForm = IntegerVector());

  /**
   * Run the algorithm. With a level form, it stops as soon as no element of
   * level 1 is left, since cutting further cannot create one; then
   * hasLevelOneElements() is false and the Hilbert basis is not computed.
   */
  void compute();

  /**
   * @return the Hilbert basis of M modulo the units, truncated at level 1 if
   * a level form was given
   */
  std::vector<IntegerVector> getHilbertBasis() const;

  /** @return a basis of the unit group U of M */
  const LatticeBasis& getUnits() const { return d_units; }

  /**
   * @return whether M has an element of level 1. Only meaningful with a
   * level form, after compute().
   */
  bool hasLevelOneElements() const { return d_hasLevelOneElements; }

  /**
   * @return the number of sums p + n formed by compute(), a measure of its
   * work
   */
  size_t getNumSums() const { return d_numSums; }

 private:
  /** A Hilbert basis candidate. */
  struct Candidate
  {
    /** The lattice point x. */
    IntegerVector d_point;
    /**
     * The values (b_1(x), ..., b_k(x)) of the forms cut so far. While the
     * form b_k is being cut, the last entry is |b_k(x)|.
     */
    std::vector<Integer> d_values;
    /** The sum of d_values. */
    Integer d_degree;
    /** The level l(x), or zero if there is no level form. */
    Integer d_level;
    /**
     * Whether x was added in the last round of the current cut, so that its
     * sums with the other candidates have not been formed yet.
     */
    bool d_isNew;
  };

  /** Steps (D1)-(D8): cut the current monoid with the halfspace a(x) >= 0. */
  void cut(const IntegerVector& a);

  /**
   * Make the candidate for a point that is a unit of the monoid before the
   * current cut, i.e. that has value 0 at every form cut before.
   *
   * @param point the point
   * @param value the absolute value of the current form at the point
   */
  Candidate makeUnitCandidate(const IntegerVector& point,
                              const Integer& value) const;

  /**
   * Compute the value vector and the degree of the sum p + n of a positive
   * and a negative candidate: the sum of their value vectors, except that the
   * entry of the current (last) form is |p_k - n_k|.
   *
   * @param p a positive candidate
   * @param n a negative candidate
   * @param values set to the value vector of p + n
   * @param degree set to the degree of p + n
   */
  static void sumValues(const Candidate& p,
                        const Candidate& n,
                        std::vector<Integer>& values,
                        Integer& degree);

  /** @return whether x has a smaller degree than y */
  static bool lessByDegree(const Candidate& x, const Candidate& y);

  /**
   * Merge the candidates `added` into `list`, keeping it sorted by degree.
   * Both lists must be sorted by degree.
   */
  static void mergeByDegree(std::vector<Candidate>& list,
                            std::vector<Candidate>& added);

  /**
   * @return whether some candidate y of `list` reduces a point with the
   * given values and degree, i.e. whether every value of y is at most the
   * corresponding value. The list must be sorted by degree.
   */
  static bool isReducible(const std::vector<Candidate>& list,
                          const std::vector<Integer>& values,
                          const Integer& degree);

  /**
   * Auto-reduce the candidates `list`: remove every candidate that another
   * candidate of `list` or of `reducers` reduces, keeping one candidate of
   * each value vector. Afterwards `list` is sorted by degree; `reducers`
   * must be sorted by degree.
   */
  static void autoReduce(std::vector<Candidate>& list,
                         const std::vector<Candidate>& reducers);

  /**
   * Remove every candidate of `list` that a candidate of `reducers` reduces.
   * The order of `list` is kept; `reducers` must be sorted by degree.
   */
  static void removeReducible(std::vector<Candidate>& list,
                              const std::vector<Candidate>& reducers);

  /** The equations defining L. */
  std::vector<IntegerVector> d_equations;
  /** The forms to cut with, in order; the level form (if any) comes first. */
  std::vector<IntegerVector> d_forms;
  /** The level form, or the empty vector. */
  IntegerVector d_levelForm;
  /** Whether a level form was given. */
  bool d_truncate;
  /** A basis of the unit group of the current monoid. */
  LatticeBasis d_units;
  /** The Hilbert basis of the current monoid modulo the units. */
  std::vector<Candidate> d_basis;
  /** The number of forms cut so far. */
  size_t d_numCuts;
  /** Whether the monoid has an element of level 1. */
  bool d_hasLevelOneElements;
  /** The number of sums p + n formed so far. */
  size_t d_numSums;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__DUAL_HILBERT_BASIS_H */

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

#include <cstdint>
#include <exception>
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
 *   and h and -h join the candidates. After this reduction the elements of
 *   H remain irreducible on their side of the cut.
 * - (D6)-(D8): the candidates are split by the sign of a into positive,
 *   negative and neutral ones. In rounds, the sums p + n of a positive and
 *   a negative candidate are formed and kept if no candidate of its side
 *   and no neutral candidate reduces it, until no new candidate is kept.
 *   Then the positive and the neutral candidates are the Hilbert basis of
 *   the cut monoid.
 *
 * Avoiding work. As in Normaliz ([BI], Remarks 6 and 16), these techniques
 * keep the number of sums and of reduction tests down; see
 * DualHilbertBasisComputation:
 * - Generations (16(a)): a round only forms the sums with at least one
 *   summand that is new since the previous round.
 * - Promotion (16(b)-(c)): a new sum waits in a depot and only becomes a
 *   candidate, and so a summand of further sums, once its degree with respect
 *   to the forms cut before shows that no later sum can reduce it. Candidates
 *   are therefore final and never removed.
 * - Prediction (16(d)): a sum is not formed at all if its summands' parents
 *   show that it is reducible.
 * - Reducer order (6(a)): the candidates are tried as reducers starting with
 *   those that reduced a sum most recently.
 * With truncation, the pairs of two candidates of level 1 are never visited,
 * and two more shortcuts apply when the candidates of level 0 do not allow
 * new sums of level at most 1.
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
 * Precision. Like the Normaliz program, the computation first stores the
 * values in 64-bit integers, which is much faster, and is repeated with
 * arbitrary precision if a value does not fit; the points are always exact.
 * See DualHilbertBasisComputation and DualArithmetic.
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
 *   negative (-1, 0) and (-2, -1). The rounds form the sums (1, 1), (0, 1),
 *   (1, 2) and the neutral (1, 3), one per round, each of which is promoted
 *   to a candidate; three other sums, such as (1, 1) + (-2, -1) = (-1, 0),
 *   are predicted to be reducible and not formed.
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
   * Run the algorithm, with 64-bit values first and with arbitrary precision
   * if they overflow. With a level form, it stops as soon as no element of
   * level 1 is left, since cutting further cannot create one; then
   * hasLevelOneElements() is false and the Hilbert basis is not computed.
   */
  void compute();

  /**
   * @return the Hilbert basis of M modulo the units, truncated at level 1 if
   * a level form was given
   */
  const std::vector<IntegerVector>& getHilbertBasis() const
  {
    return d_hilbertBasis;
  }

  /** @return a basis of the unit group U of M */
  const LatticeBasis& getUnits() const { return d_units; }

  /**
   * @return whether M has an element of level 1. Only meaningful with a
   * level form, after compute().
   */
  bool hasLevelOneElements() const { return d_hasLevelOneElements; }

  /**
   * @return the number of sums p + n formed by compute(), including those of
   * a 64-bit computation that overflowed; a measure of its work
   */
  size_t getNumSums() const { return d_numSums; }

  /** @return whether compute() needed arbitrary precision values */
  bool usedArbitraryPrecision() const { return d_usedArbitraryPrecision; }

 private:
  /** Run the computation with values of type T and store its results. */
  template <typename T>
  void run();

  /**
   * @return the restriction of the linear form a to L, i.e. its values at
   * the basis of L in Hermite normal form, divided by their gcd
   */
  IntegerVector getRestriction(const IntegerVector& a) const;

  /** A basis of the lattice L, in Hermite normal form. */
  LatticeBasis d_lattice;
  /** The forms to cut with, in order; the level form (if any) comes first. */
  std::vector<IntegerVector> d_forms;
  /** The level form, or the empty vector. */
  IntegerVector d_levelForm;
  /** The Hilbert basis computed. */
  std::vector<IntegerVector> d_hilbertBasis;
  /** A basis of the unit group of M. */
  LatticeBasis d_units;
  /** Whether M has an element of level 1. */
  bool d_hasLevelOneElements;
  /** The number of sums formed. */
  size_t d_numSums;
  /** Whether arbitrary precision values were needed. */
  bool d_usedArbitraryPrecision;
};

/**
 * Thrown by DualArithmetic<int64_t> when a value does not fit into 64 bits.
 * DualHilbertBasis::compute then repeats the computation with Integer
 * values.
 */
class DualOverflow : public std::exception
{
 public:
  const char* what() const noexcept override
  {
    return "64-bit overflow in the dual Hilbert basis algorithm";
  }
};

/**
 * The arithmetic on the values of DualHilbertBasisComputation<T> that can
 * overflow, for T = int64_t (checked, throws DualOverflow) and T = Integer
 * (exact). Comparisons, and subtractions of a value from a larger one, use
 * the operators of T.
 */
template <typename T>
class DualArithmetic
{
 public:
  /** @return x as a T */
  static T fromInteger(const Integer& x);
  /** Set a to a + b. */
  static void addTo(T& a, const T& b);
};

/**
 * One run of the dual algorithm of DualHilbertBasis (see there), with the
 * values of the linear forms at the candidates stored as T, which is int64_t
 * or Integer. The points are always exact.
 */
template <typename T>
class DualHilbertBasisComputation
{
 public:
  /**
   * @param units a basis of the lattice L
   * @param forms the linear forms to cut with, in this order
   * @param levelForm the level form, which must be the first of `forms`, or
   * the empty vector
   */
  DualHilbertBasisComputation(const LatticeBasis& units,
                              const std::vector<IntegerVector>& forms,
                              const IntegerVector& levelForm);

  /** Run the algorithm, see DualHilbertBasis::compute. */
  void compute();

  /** @return the Hilbert basis computed */
  std::vector<IntegerVector> getHilbertBasis() const;
  /** @return a basis of the unit group */
  const LatticeBasis& getUnits() const { return d_units; }
  /** @return whether the monoid has an element of level 1 */
  bool hasLevelOneElements() const { return d_hasLevelOneElements; }
  /** @return the number of sums formed */
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
    std::vector<T> d_values;
    /** The sum of d_values, the degree of x. */
    T d_degree;
    /**
     * The degree of x before the current cut, i.e. the sum of all values but
     * the last one. It is additive on sums, and 0 exactly for the old units.
     */
    T d_oldDegree;
    /** The level l(x), or zero if there is no level form. */
    T d_level;
    /**
     * For a sum x = p + n of the current cut: the absolute value of the
     * current form at the summand on the side of x, i.e. at p if x is
     * positive and at n if x is negative ("mother" in [BI], Remark 16(d)).
     * It is 0 for the other candidates, and for neutral sums.
     */
    T d_mother;
  };

  /**
   * The candidates of one side of a cut, and the order in which they are
   * tried as reducers. A candidate that reduces a sum moves to the front,
   * since the next sums are often reducible by it as well (the
   * "darwinistic" order of [BI], Remark 6(a), and Normaliz's
   * CandidateTable). Candidates are only appended during a cut.
   */
  struct Side
  {
    /** The candidates. */
    std::vector<Candidate> d_candidates;
    /** The indices of the candidates, in the order to try them. */
    std::vector<size_t> d_order;
    /**
     * The index of the first candidate added in the last round. The sums of
     * the candidates before it with those of the other side were formed in
     * earlier rounds ([BI], Remark 16(a)).
     */
    size_t d_firstNew = 0;
  };

  /**
   * The state of one cut: the candidates on the three sides, which are
   * Hilbert basis elements of their side, and the depots of the sums formed
   * but not yet promoted to candidates.
   */
  struct CutState
  {
    /** The positive candidates. */
    Side d_positive;
    /** The negative candidates. */
    Side d_negative;
    /** The neutral candidates. */
    Side d_neutral;
    /** The positive sums not yet promoted. */
    std::vector<Candidate> d_positiveDepot;
    /** The negative sums not yet promoted. */
    std::vector<Candidate> d_negativeDepot;
    /** The neutral sums not yet promoted. */
    std::vector<Candidate> d_neutralDepot;
    /** The smallest old degree of a candidate at the start of the cut. */
    T d_minOldDegree = T(0);
    /**
     * Whether sums must be checked for reducibility. Under truncation, if no
     * positive or neutral candidate has level 0, a sum of level at most 1 is
     * a positive candidate of level 1 plus a negative one of level 0, which
     * no candidate but a duplicate can reduce, and negative sums are not
     * needed at all.
     */
    bool d_doReduction;
  };

  /** The sums formed in one round, and buffers for forming them. */
  struct Round
  {
    /** The positive sums. */
    std::vector<Candidate> d_positive;
    /** The negative sums. */
    std::vector<Candidate> d_negative;
    /** The neutral sums. */
    std::vector<Candidate> d_neutral;
    /** The value vector of the current sum. */
    std::vector<T> d_values;
    /** The degree of the current sum. */
    T d_degree = T(0);
    /** The level of the current sum. */
    T d_level = T(0);
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
  /** @return the level of the point, or 0 if there is no level form */
  T getLevel(const IntegerVector& point) const;

  /**
   * Step (D6) for one round: form the sums p + n of a positive and a
   * negative candidate, at least one of them new, that are neither truncated
   * nor predicted to be reducible, and put those that no candidate reduces
   * into the depots. Afterwards no candidate is new.
   *
   * The pairs are visited in blocks of old and new candidates and, under
   * truncation, of candidates of level 0 and 1, so that the pairs of two old
   * candidates and of two candidates of level 1 are not even looked at.
   */
  void formSums(CutState& state);

  /**
   * Whether the sum p + n of a positive candidate p and a negative candidate
   * n is reducible by the prediction of [BI], Remark 16(d). Let p = p1 + p2
   * be a sum of the cut with mother pm = a(p1), and n = n1 + n2 one with
   * mother nm = |a(n2)|, and write pv = a(p), nv = |a(n)|. If p + n is
   * positive (pv > nv), it is reducible if
   * - nm <= pv: then p + n2 is in the positive halfspace, and
   *   p + n = (p + n2) + n1 with the positive n1, or
   * - nm <= pm and pm - nm <= pv - nv: then p1 + n2 and p2 + n1 are in the
   *   positive halfspace, and p + n is their sum.
   * The negative case is symmetric, and a neutral p + n is reducible if
   * pm = nm, as the sum of the neutral p1 + n2 and p2 + n1. A mother 0 means
   * that the candidate is not such a sum.
   */
  static bool isPredictedReducible(const Candidate& p, const Candidate& n);

  /**
   * Form the sum p + n of a positive and a negative candidate and add it to
   * the sums of the round, unless it is truncated, predicted to be
   * reducible, a unit, or reduced by a candidate (see formSums).
   */
  void formSum(CutState& state,
               const Candidate& p,
               const Candidate& n,
               Round& round);

  /**
   * Steps (D7)-(D8): promote the sums in the depots that are known to be
   * irreducible to candidates, and remove the sums that they reduce from
   * the depots.
   *
   * Every sum formed later has a new candidate as a summand and so an old
   * degree of at least m = d_minOldDegree + (the smallest old degree in the
   * positive and negative depots). If a sum x is reducible, it is reducible
   * by a Hilbert basis element of its side of at most half its old degree,
   * which therefore is already known if the old degree of x is at most
   * 2m - 1. Such sums are promoted after removing those that another one
   * reduces ([BI], Remark 16(b)-(c)).
   *
   * @return false if the cut is complete, i.e. if the positive and the
   * negative depots are empty, in which case the neutral depot is
   * auto-reduced and promoted
   */
  bool promote(CutState& state);

  /**
   * Move the sums of `depot` with an old degree of at most `maxOldDegree`
   * to `promoted`, and auto-reduce them unless `reduce` is false.
   */
  static void takePromoted(std::vector<Candidate>& depot,
                           const T& maxOldDegree,
                           bool reduce,
                           std::vector<Candidate>& promoted);

  /**
   * Add the sums `added` to `depot`, keeping one sum of each value vector,
   * namely one with the smallest mother.
   */
  static void addToDepot(std::vector<Candidate>& depot,
                         std::vector<Candidate>& added);

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
                        std::vector<T>& values,
                        T& degree);

  /** @return whether x has a smaller degree than y */
  static bool lessByDegree(const Candidate& x, const Candidate& y);

  /** Append the candidates `added` to `side`, last in its order. */
  static void append(Side& side, std::vector<Candidate>& added);

  /**
   * @return whether some candidate of `side` reduces a point with the given
   * values and degree; if so, the reducer moves to the front of the order
   */
  static bool isReducibleBy(Side& side,
                            const std::vector<T>& values,
                            const T& degree);

  /** Remove every candidate of `list` that a candidate of `side` reduces. */
  static void removeReducibleBy(std::vector<Candidate>& list, Side& side);

  /**
   * @return whether some candidate y of `list` reduces a point with the
   * given values and degree, i.e. whether every value of y is at most the
   * corresponding value. The list must be sorted by degree.
   */
  static bool isReducible(const std::vector<Candidate>& list,
                          const std::vector<T>& values,
                          const T& degree);

  /**
   * Auto-reduce the candidates `list`: remove every candidate that another
   * candidate of `list` reduces, keeping one candidate of each value vector.
   * Afterwards `list` is sorted by degree.
   */
  static void autoReduce(std::vector<Candidate>& list);

  /**
   * Remove every candidate of `list` that a candidate of `reducers` reduces.
   * The order of `list` is kept; `reducers` must be sorted by degree.
   */
  static void removeReducible(std::vector<Candidate>& list,
                              const std::vector<Candidate>& reducers);

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

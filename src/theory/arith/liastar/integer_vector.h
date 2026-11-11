/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Integer vectors and the arithmetic on them used by the lattice algorithms
 * of the liastar extension.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__INTEGER_VECTOR_H
#define CVC5__THEORY__ARITH__LIASTAR__INTEGER_VECTOR_H

#include <string>
#include <vector>

#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * A vector of arbitrary-precision integers. It is used both for points of
 * the lattice Z^d and for the coefficients (a_1, ..., a_d) of a linear form
 * a(x) = a_1 x_1 + ... + a_d x_d; IntegerVectorUtils::dot evaluates a form at
 * a point.
 */
using IntegerVector = std::vector<Integer>;

/**
 * Arithmetic on integer vectors. All methods are static; vectors passed
 * together must have the same size.
 */
class IntegerVectorUtils
{
 public:
  /** @return the zero vector of the given size */
  static IntegerVector zero(size_t size);
  /** @return the i-th unit vector of the given size, e.g. (0, 1, 0) */
  static IntegerVector unit(size_t size, size_t i);
  /** @return true if every entry of a is zero */
  static bool isZero(const IntegerVector& a);
  /**
   * @return the dot product a_1 b_1 + ... + a_d b_d, i.e. the value of the
   * linear form a at the point b. For example dot((2, 3), (1, -1)) = -1.
   */
  static Integer dot(const IntegerVector& a, const IntegerVector& b);
  /** @return a + b */
  static IntegerVector add(const IntegerVector& a, const IntegerVector& b);
  /** @return -a */
  static IntegerVector negate(const IntegerVector& a);
  /** Set a to a + c * b. */
  static void addMultiple(IntegerVector& a,
                          const Integer& c,
                          const IntegerVector& b);
  /**
   * Divide a by the gcd of its entries, e.g. (2, -4, 6) becomes (1, -2, 3).
   * The zero vector is left unchanged.
   */
  static void makePrimitive(IntegerVector& a);
  /** @return the sum of the absolute values of the entries of a */
  static Integer l1Norm(const IntegerVector& a);
  /**
   * The order Normaliz uses for sorting linear forms and results: by L1 norm
   * first and lexicographically second. For example
   * (0, 1) < (1, 0) < (1, 1) < (2, 0).
   *
   * @return true if a comes strictly before b
   */
  static bool lessByNorm(const IntegerVector& a, const IntegerVector& b);
  /** @return a as a string, e.g. "(1, -2, 0)" */
  static std::string toString(const IntegerVector& a);
  /** @return the vectors as a string, e.g. "{(1, 0), (0, 1)}" */
  static std::string toString(const std::vector<IntegerVector>& vectors);
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__INTEGER_VECTOR_H */

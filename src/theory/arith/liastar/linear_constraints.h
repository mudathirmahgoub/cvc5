/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A conjunction of linear constraints over integer variables, as integer
 * matrices.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__LINEAR_CONSTRAINTS_H
#define CVC5__THEORY__ARITH__LIASTAR__LINEAR_CONSTRAINTS_H

#include <map>
#include <string>
#include <vector>

#include "expr/node.h"
#include "theory/arith/liastar/integer_vector.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * A conjunction of linear equations and inequalities over integer variables
 * x_1, ..., x_n. Each constraint is stored as an integer row
 * (a_1, ..., a_n, b) of length n + 1, standing for the affine form
 * a_1 x_1 + ... + a_n x_n + b, and is either an equation (the form is 0) or
 * an inequality (the form is nonnegative).
 *
 * Writing b as b * x_{n+1} turns the rows into linear forms on Z^{n+1}
 * ("homogenization"), whose points of level x_{n+1} = 1 are the solutions,
 * see IntegerPolyhedron. This replaces the Normaliz input format
 * ("constraints ... symbolic") previously used by the liastar extension.
 *
 * Only integer solutions matter, so the constraints are normalized:
 * - rational coefficients are scaled to integers,
 * - a < b and a > b become the inequalities b - a - 1 >= 0 and
 *   a - b - 1 >= 0, which have the same integer solutions,
 * - a <= b and a >= b become b - a >= 0 and a - b >= 0, and
 * - every row is divided by the gcd of its entries.
 *
 * Example: over the variables (x y), the conjunction
 *   (and (>= (+ x y) 2) (< x 5) (= x (* 2 y)) (>= y 1/2))
 * where 1/2 is a rational constant, is stored as
 *   inequalities (1, 1, -2), (-1, 0, 4), (0, 2, -1)
 *   equations    (1, -2, 0)
 * i.e. x + y - 2 >= 0, -x + 4 >= 0, 2y - 1 >= 0 and x - 2y = 0.
 */
class LinearConstraints
{
 public:
  /** The empty conjunction (true) over n variables. */
  explicit LinearConstraints(size_t numVariables);
  /**
   * Convert a conjunction of linear constraints over the given variables.
   *
   * @param variables a node of kind BOUND_VAR_LIST, the variables
   * x_1, ..., x_n in this order
   * @param conjunction a Boolean constant, an atom (= a b), (>= a b),
   * (> a b), (<= a b) or (< a b) where a and b are linear integer terms over
   * the variables, or a (possibly nested) conjunction of these. Linear terms
   * are built from integer and rational constants, the variables, +, -, and
   * multiplication by constants.
   */
  LinearConstraints(Node variables, Node conjunction);

  /** @return the number n of variables */
  size_t getNumVariables() const { return d_numVariables; }
  /** @return the rows (a_1, ..., a_n, b) of the equations */
  const std::vector<IntegerVector>& getEquations() const { return d_equations; }
  /** @return the rows (a_1, ..., a_n, b) of the inequalities */
  const std::vector<IntegerVector>& getInequalities() const
  {
    return d_inequalities;
  }

  /** Add the equation a_1 x_1 + ... + a_n x_n + b = 0 given by its row. */
  void addEquation(IntegerVector row);
  /** Add the inequality a_1 x_1 + ... + a_n x_n + b >= 0 given by its row. */
  void addInequality(IntegerVector row);
  /** Add the inequalities x_i >= 0 for every variable x_i. */
  void addNonnegativity();
  /**
   * Add a constraint without solutions. It is the equation 1 = 0, i.e. the
   * row (0, ..., 0, 1).
   */
  void addFalse();

  /**
   * @return the constraints as a string, equations first, e.g.
   * "x - 2*y = 0, x + y - 2 >= 0", using the variable names if they are known
   * and x1, ..., xn otherwise
   */
  std::string toString() const;

 private:
  /** Add the constraints of a conjunction, see the constructor. */
  void addConjunction(Node conjunction);
  /**
   * Add factor * term to the affine form `form`, whose entries are the
   * coefficients of x_1, ..., x_n followed by the constant.
   */
  void addTerm(Node term,
               const Rational& factor,
               std::vector<Rational>& form) const;
  /**
   * @return the affine form a - b as an integer row, scaled by the least
   * common multiple of the denominators of its coefficients
   */
  IntegerVector getDifference(Node a, Node b) const;
  /** @return the row as an affine form, e.g. "x - 2*y + 3" */
  std::string rowToString(const IntegerVector& row) const;

  /** The number n of variables. */
  size_t d_numVariables;
  /** The variables, if known. */
  std::vector<Node> d_variables;
  /** The index of each variable. */
  std::map<Node, size_t> d_indices;
  /** The equations. */
  std::vector<IntegerVector> d_equations;
  /** The inequalities. */
  std::vector<IntegerVector> d_inequalities;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__LINEAR_CONSTRAINTS_H */

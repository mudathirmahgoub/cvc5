/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for the lia* (LIA star) arithmetic extension.
 */

#ifdef CVC5_USE_NORMALIZ

#ifndef CVC5__THEORY__LIASTAR__UTILS_H
#define CVC5__THEORY__LIASTAR__UTILS_H

#include "expr/node.h"
#include "libnormaliz/libnormaliz.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "theory/arith/linear/normal_form.h"
#include "util/result.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/** Arbitrary-precision integers (the integer type handed to Normaliz). */
typedef mpz_class Integer;

/**
 * Stateless helpers used by `LiaStarExtension` (see liastar_extension.cpp for
 * the overall decision procedure). They fall into three groups:
 *
 * 1. Predicate normalization (`removeItesAndNots`, `toDNF` and their private
 *    workers): turn the arbitrary QF_LIA body of a star lambda into a flat
 *    disjunction of conjunctions of positive linear (in)equalities -- the only
 *    shape that can be rendered as polyhedral cones.
 *
 * 2. The Normaliz bridge (`getMatrix`, `getMatrices`, `buildCone`,
 *    `isEmptyCone`, `getGeneratorBody`): render conjunctions as Normaliz
 *    "symbolic" constraint strings, compute cones (Hilbert basis and module
 *    generators), and encode a module generator back into arithmetic.
 *
 * 3. Model extraction for the lazy strategy (`getDisjunct`): read a model from
 *    an incremental subsolver and distil the convex cell of the predicate
 *    containing it.
 */
class LiaStarUtils
{
 public:
  /**
   * Decompose a STAR_CONTAINS literal into its "vector predicate" and the
   * non-negativity condition on its vector.
   *
   * @param n a node (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p)
   *   y_1 ... y_n)
   * @param nm the node manager
   * @return the pair
   *   < p[y_1/x_1, ..., y_n/x_n], (and true (>= y_1 0) ... (>= y_n 0)) > :
   *   the statement that the vector itself satisfies p (and is hence a
   *   single-summand member of the star set), and the necessary condition
   *   that the vector lies in the non-negative orthant.
   */
  static std::pair<Node, Node> getVectorPredicate(Node n, NodeManager* nm);

  /**
   * Eliminate if-then-elses and negations from a QF_LIA predicate.
   *
   * If-then-elses are removed by case splitting (`removeItes`, no new
   * variables); negations are pushed to the leaves and folded into the
   * comparisons they negate (`removeNot`), with a disequality
   * `(not (= a b))` becoming `(or (> a b) (< a b))`.
   *
   * @param n a QF_LIA predicate (boolean combination of linear comparisons,
   *   possibly with integer or boolean ites)
   * @param e the environment
   * @return an equivalent ite-free, negation-free predicate whose atoms are
   *   positive linear comparisons
   */
  static Node removeItesAndNots(Node n, Env* e);

  /**
   * Normalize a QF_LIA predicate into flat disjunctive normal form: first
   * `removeItesAndNots`, then distribute AND over OR (`distribute`), then
   * flatten nested AND/OR (`recursiveFlatten`). Each disjunct of the result is
   * a flat conjunction of positive linear comparisons, i.e. one convex
   * polyhedron (one cone).
   *
   * @param n a QF_LIA predicate
   * @param e the environment
   * @return an equivalent predicate in flat DNF
   */
  static Node toDNF(Node n, Env* e);

  /**
   * Distribute AND over OR to reach disjunctive normal form (a step of
   * `toDNF`; public for white-box unit testing). Conjunctions found
   * unsatisfiable (via `areAssertionsUnsat`) are pruned eagerly, which avoids
   * building cones for empty cells.
   */
  static Node distribute(Node n, Env* e);

  /**
   * Collapse nested associative operators one level deep, e.g.
   * (or a (or b c)) -> (or a b c) and likewise inside each disjunct, so a DNF
   * is exactly two levels: a flat OR of flat ANDs. (A step of `toDNF`; public
   * for white-box unit testing.)
   */
  static Node recursiveFlatten(NodeManager* nm, Node n);

  /**
   * Check the satisfiability of `assertion` (conjoined with the
   * non-negativity of all variables in `freeVariables`) using a fresh cvc5
   * subsolver. Genuine bound variables are existentially quantified; free
   * constants are left in place, since checking a formula with free constants
   * is equivalent to checking its existential closure. (Used by
   * `areAssertionsUnsat`; public for white-box unit testing.)
   */
  static Result cvc5CheckSat(const std::vector<Node>& freeVariables,
                             Node assertion,
                             Env* e);

  /**
   * Render a single convex cell into Normaliz "symbolic" constraint strings.
   *
   * @param variables the lambda's variables (a BOUND_VAR_LIST); the i-th
   *   variable is printed as the Normaliz placeholder "x[i+1]"
   * @param n one DNF disjunct: a linear comparison, a flat conjunction of
   *   comparisons, or a boolean constant (encoded as the trivially true row
   *   "x[1] = x[1];" or the infeasible row "1 = 0;")
   * @return the constraint rows (one string per comparison, e.g.
   *   "x[1] + 2x[2] >= 3;") paired with `n` itself
   */
  static std::pair<std::vector<std::string>, Node> getMatrix(Node variables,
                                                             Node n);

  /**
   * Render a predicate in flat DNF into one constraint matrix per disjunct
   * (one cone each), by applying `getMatrix` to every disjunct.
   *
   * @param variables the lambda's variables (a BOUND_VAR_LIST)
   * @param n a predicate in flat DNF (as produced by `toDNF`)
   * @return one (constraint rows, disjunct) pair per disjunct of `n`
   */
  static std::vector<std::pair<std::vector<std::string>, Node>> getMatrices(
      Node variables, Node n);

  /**
   * Build the Normaliz cone of a single convex polyhedron and compute its
   * Hilbert basis and module generators.
   *
   * This is the one place that talks to libnormaliz. The constraint strings
   * are in Normaliz "symbolic" form, as produced by `getMatrix`/`getMatrices`.
   * The cone is restricted to the non-negative orthant and uses exact
   * (infinite-precision) integer arithmetic.
   *
   * @param dimension the ambient dimension (the number of star variables; the
   *   Normaliz "amb_space")
   * @param constraints the rows of the cone, one symbolic constraint each
   * @return the computed cone (Hilbert basis and module generators available)
   */
  static libnormaliz::Cone<Integer> buildCone(
      size_t dimension, const std::vector<std::string>& constraints);

  /**
   * @param cone a cone computed by `buildCone`
   * @return true if `cone` is empty, i.e. its (inhomogeneous) constraint
   *   system is infeasible. For an inhomogeneous cone Normaliz reports an
   *   affine dimension of -1 in that case. Takes `cone` by non-const reference
   *   because querying the affine dimension may trigger its computation.
   */
  static bool isEmptyCone(libnormaliz::Cone<Integer>& cone);

  /**
   * Checks the incremental subsolver `smte` (which must already have the
   * membership predicate, and the negations of any previously discovered
   * cone-disjuncts, asserted) and reads its model to build one disjunct (cell)
   * of the predicate's satisfying region: a conjunction that fixes every atom
   * of `assertion` to its model truth value (splitting a false integer
   * equality into the strict inequality the model satisfies).
   *
   * @param assertion the (skolem-space) predicate, used only to enumerate the
   *   atoms read from the model; it is not asserted here.
   * @param from the lambda's bound variables and @param to the skolem
   *   constants substituted for them; the returned disjunct is mapped back
   *   from `to` to `from` (bound-variable space).
   * @param e the environment
   * @param smte the incremental subsolver to check
   * @return the disjunct, `false` if `smte` is unsat (the predicate is fully
   *   covered), or `true` if it has no atoms.
   */
  static Node getDisjunct(Node assertion,
                          const std::vector<Node>& from,
                          const std::vector<Node>& to,
                          Env* e,
                          SolverEngine* smte);

  /**
   * Builds the encoding of one module generator of a cone in terms of fresh
   * variables. The body is shared between the membership encoding
   * (`LiaStarExtension::getMembershipDisjuncts`, which existentially binds
   * `vars`) and the star encoding (`LiaStarExtension::getCones` /
   * `getStarConstraints`, which assert the constraints at the top level).
   *
   * @param dimension the ambient dimension of the cone
   * @param generator a module generator of the cone (a lattice point)
   * @param hilbertBasis the Hilbert basis of the cone (its rays)
   * @param star whether to build the star encoding (introduce a multiplier
   *   `mu` for `generator` and couple the rays to it) or the plain membership
   *   encoding (use `generator` as a fixed offset, with multiplier 1)
   * @param useSkolems whether the introduced variables are skolems (asserted
   *   at the top level) or bound variables (to be existentially bound)
   * @param nm the node manager
   * @param vars output: the fresh variables introduced (the multiplier `mu`
   *   and the ray multipliers `l_j`)
   * @param constraints output: the side constraints over `vars`
   *   (non-negativity and, for the star encoding, the coupling constraints)
   * @param point output: the point `mu * generator` (star) or `generator`
   * @param rays output: the rays `l_j * basis_j`, one per Hilbert basis
   *   element
   */
  static void getGeneratorBody(
      size_t dimension,
      const std::vector<Integer>& generator,
      const std::vector<std::vector<Integer>>& hilbertBasis,
      bool star,
      bool useSkolems,
      NodeManager* nm,
      std::vector<Node>& vars,
      std::vector<Node>& constraints,
      std::vector<Node>& point,
      std::vector<std::vector<Node>>& rays);

  /**
   * Emit, on the "liastar-ext-smt" trace channel, a push/pop-enclosed
   * (check-sat) query asserting that `a` and `b` are distinct. When the trace
   * is replayed with a separate solver the expected answer is unsat, which
   * validates that the transformation from `a` to `b` preserved equivalence.
   * Does nothing if that trace channel is off.
   *
   * @param label echoed before the query to identify it in the output
   * @param a the formula before the transformation
   * @param b the formula after the transformation
   */
  static void traceDistinctQuery(const std::string& label, Node a, Node b);

 private:
  /**
   * Eliminate if-then-elses from a QF_LIA predicate by case splitting, without
   * introducing new variables. A boolean ite `(ite c t e)` becomes
   * `(or (and c t) (and (not c) e))`; integer ites nested inside a comparison
   * are lifted out via `removeIntegerItes` and recombined into a disjunction
   * of guarded comparisons.
   */
  static Node removeItes(Node n, Env* e);

  /**
   * Lift integer if-then-elses out of an integer term. Each returned pair is
   * (condition, ite-free term): the term is the value of `n` when the
   * condition holds, and the conditions are mutually exclusive and exhaustive.
   * A term without ites yields the single pair (true, n).
   */
  static std::vector<std::pair<Node, Node>> removeIntegerItes(Node n, Env* e);

  /**
   * Convert an ite-free predicate to negation normal form and fold every
   * remaining negation into the comparison it negates, e.g. `(not (< a b))`
   * becomes `(>= a b)` and the disequality `(not (= a b))` becomes
   * `(or (> a b) (< a b))`. The result contains no NOT nodes.
   */
  static Node removeNot(Node n, Env* e);

  /**
   * Decide whether a conjunction of literals is unsatisfiable; used by
   * `distribute` to prune dead DNF branches. Depending on the
   * arithLiaStarNormalizAsSubSolver option this dispatches to
   * `normalizCheckSat` or `cvc5CheckSat`. Returns an unknown Result when the
   * arithLiaStarSubSolver option is off (the caller then keeps the conjunct).
   */
  static Result areAssertionsUnsat(const std::vector<Node>& assertions,
                                   Env* e);

  /**
   * Use Normaliz as a satisfiability oracle for a single conjunction of
   * linear constraints: the conjunction is satisfiable over the non-negative
   * integers iff its cone is non-empty. Only the UNSAT verdict is meaningful;
   * a non-empty cone yields an unknown Result.
   */
  static Result normalizCheckSat(Node variables, Node assertion);

  /**
   * Collect the atomic predicates (leaves of the boolean structure) of `n`
   * into `atoms`, in deterministic traversal order, using `visited` to avoid
   * duplicates.
   */
  static void collectAtoms(Node n,
                           std::vector<Node>& atoms,
                           std::unordered_set<Node>& visited);

  /**
   * Print a linear polynomial in Normaliz syntax, mapping the i-th variable
   * of `variables` (a BOUND_VAR_LIST) to the placeholder "x[i+1]" (Normaliz
   * indexes from 1). For example, with variables (a b), the polynomial
   * 2a - b + 3 prints as "2x[1] - x[2] + 3".
   */
  static std::string getString(Node variables, linear::Polynomial& p);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */

#endif /* CVC5_USE_NORMALIZ */

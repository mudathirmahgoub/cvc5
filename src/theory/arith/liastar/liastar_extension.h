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
 * Extension to the theory of arithmetic for the LIA* predicate
 * int.star-contains.
 */

#ifdef CVC5_USE_NORMALIZ

#ifndef CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H
#define CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "libnormaliz/libnormaliz.h"
#include "smt/env_obj.h"
#include "smt/solver_engine.h"
#include "theory/arith/liastar/liastar_stats.h"
#include "theory/decision_strategy.h"
#include "theory/ext_theory.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;
class TheoryArith;

namespace liastar {

/**
 * The integer type used by Normaliz, as in liastar_utils.h. Note this shadows
 * cvc5::internal::Integer within namespace liastar.
 */
typedef mpz_class Integer;
/** A row of arithmetic terms, e.g. the monomials of one cone contribution. */
typedef std::vector<Node> Vector;

/**
 * Decision strategy carrying an endgame hint (see
 * `LiaStarExtension::tryEndgame`): while a hint is active, it hands the SAT
 * solver the hint's guard and then each pinned equality as the next
 * decisions, so the witness assignment is built directly instead of hoping
 * the solver's own heuristics stumble onto it (a phase preference alone is
 * useless here: with hundreds of pinned variables, some are always already
 * bound differently on the trail, so the guard would just be propagated
 * false).
 */
class LiaStarHintStrategy : public DecisionStrategy
{
 public:
  LiaStarHintStrategy(Env& env, Valuation valuation)
      : DecisionStrategy(env), d_valuation(valuation)
  {
  }
  void initialize() override {}
  Node getNextDecisionRequest() override
  {
    for (const Node& literal : d_literals)
    {
      if (!d_valuation.hasSatValue(literal))
      {
        return literal;
      }
    }
    return Node::null();
  }
  std::string identify() const override { return "LiaStarHint"; }
  /** Replace the decisions with a new hint (guard first, then equalities). */
  void setHint(const std::vector<Node>& literals) { d_literals = literals; }

 private:
  /** The valuation, for skipping already-assigned literals. */
  Valuation d_valuation;
  /** The hint literals, in decision order. */
  std::vector<Node> d_literals;
};

/**
 * The LIA* extension, for literals of the form
 *   (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) y_1 ... y_n)
 * which state that y = (y_1, ..., y_n) is a sum of finitely many vectors of
 * S = {x | p(x)}, i.e. y is in the star S* of S (the empty sum is 0).
 *
 * Such a literal is reduced to linear integer arithmetic by a lemma:
 * 1. p is split into convex cells D_1, ..., D_m (the disjuncts of its DNF),
 *    so S is the union of the integer points of the polyhedra
 *    P_i = {x | D_i(x)}.
 * 2. Normaliz describes the integer points of each P_i as a finite union of
 *    linear sets g + H_i*N + M_i*Z, one per module generator g of P_i, where
 *    H_i is the Hilbert basis of the recession cone of P_i and M_i is a
 *    basis of its maximal subspace, which is empty unless P_i contains a
 *    line.
 * 3. The star of a linear set g + H*N + M*Z is
 *    {mu*g + H*l + M*m | mu >= 0, l >= 0, mu = 0 => (l = 0 and m = 0)}, and
 *    the star of a union is the sum of the stars. Fresh integer skolems for
 *    mu, l and m thus express y in S* in linear arithmetic.
 *
 * For example, S = {(x, y) | x >= 2 and y = 1} has the module generator
 * (2, 1) and the Hilbert basis {(1, 0)}, so the literal
 *   L = (int.star-contains (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
 *                          a b)
 * is reduced by the lemma
 *   (= L (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *             (= a (+ (* 2 mu) l)) (= b mu)))
 * Here the implication excludes (1, 0) = 0*(2, 1) + 1*(1, 0), which is not a
 * sum of vectors of S. See the file comment of liastar_extension.cpp for the
 * full picture, and
 * - Levatich, M., Bjorner, N., Piskac, R., Shoham, S. (2020).
 *   Solving LIA* Using Approximations.
 *   VMCAI 2020.
 *   https://doi.org/10.1007/978-3-030-39322-9_17
 *
 * Two strategies compute the cells (option arith-liastar-lazy):
 * - eager (`eagerCheckStar`): convert p to DNF, build a cone for every
 *   disjunct up front and send the exact equivalence (= L star) in one shot;
 * - lazy (`lazyCheckStar`, the default): the DNF can blow up, so instead a
 *   persistent incremental subsolver seeded with p enumerates the cells one
 *   refinement round at a time. The star built from the cells found so far
 *   under-approximates S*, so the equivalence is asserted only tentatively
 *   under a fresh boolean guard until the subsolver is unsat, i.e. every
 *   cell is covered, at which point the exact equivalence is sent. With
 *   arith-liastar-main-solver the cells of a positive literal are enumerated
 *   in the main solver instead (`mainSolverCheckStar`).
 *
 * The skolems witness y in S* when L holds, but when L is false the lemma
 * only says that this one choice of them is not a witness. A negated L is
 * therefore also reduced, once the equivalence is exact, by the lemma
 *   (or L (forall ((mu Int) (l Int))
 *           (not (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *                     (= a (+ (* 2 mu) l)) (= b mu)))))
 * which the quantifier instantiation for linear arithmetic handles. For
 * example, (not L) with a = 5 and b = 2 is unsat, since (5, 2) is
 * (2, 1) + (3, 1). In the lazy strategy a negative literal discovers one cell
 * per round, without the shortcuts of the positive case, until the
 * enumeration is complete; an under-approximation of S* cannot certify that
 * y is outside S*.
 *
 * The reduction requires p to be a Boolean combination of linear integer
 * constraints over x_1, ..., x_n. It throws a LogicException otherwise, e.g.
 * for (lambda ((x Int)) (= x (* 2 c))) with a constant c, whose set
 * depends on c.
 *
 * TheoryArith preregisters terms with preRegisterTerm, notifies the
 * extension of asserted literals with notifyAssertion, calls checkFullEffort
 * at full effort, once the linear solver has a model, and collectModelValues
 * when building the model.
 */
class LiaStarExtension : EnvObj
{
 public:
  /**
   * @param env the environment
   * @param containing the theory of arithmetic, whose facts are checked and
   * whose inference manager sends the lemmas
   */
  LiaStarExtension(Env& env, TheoryArith& containing);
  ~LiaStarExtension();

  /**
   * Register n with the extended theory if it is an int.star-contains term.
   *
   * @param n a term preregistered with the theory of arithmetic
   */
  void preRegisterTerm(TNode n);

  /**
   * Check the int.star-contains literals asserted to arithmetic, of either
   * polarity, and send lemmas for them. For a literal whose atom L has
   * lambda (lambda ((x_1 Int) ... (x_n Int)) p) and vector
   * y = (y_1, ..., y_n), where p(y) is p with x replaced by y, this
   * 1. with --arith-liastar-assume-nonnegative, sends
   *    (=> L (and (>= y_1 0) ... (>= y_n 0))),
   * 2. sends the split lemma (or p(y) (not p(y))), so the SAT solver decides
   *    p(y). If this call has sent any lemma so far, e.g. this one, the
   *    literal is left for a later call,
   * 3. with --arith-liastar-model-value (the default), stops for a positive
   *    literal if p(y), or the last star under-approximation computed for L
   *    by the lazy strategy, is true in arithModel, since then y is in S*,
   * 4. if the exact reduction of L was sent already, sends for a negative
   *    literal the lemma (or L (forall ...)) of the class documentation, once
   *    per atom, and stops,
   * 5. otherwise reduces L with the eager or the lazy strategy, see the class
   *    documentation.
   *
   * @param arithModel the model of the linear solver, which maps arithmetic
   * variables to constants, e.g. {a -> 3, b -> 1}
   * @param termSet the terms of the model, only traced
   */
  void checkFullEffort(std::map<Node, Node>& arithModel,
                       const std::set<Node>& termSet);

  /**
   * Notify the extension that a literal of the form (int.star-contains ...)
   * or (not (int.star-contains ...)) was asserted to arithmetic.
   */
  void notifyAssertion() { d_hasAssertions = true; }

  /**
   * Whether a literal of the form (int.star-contains ...) or
   * (not (int.star-contains ...)) was asserted in this context. Otherwise
   * TheoryArith calls neither checkFullEffort nor collectModelValues, so a
   * problem without such literals does not compute the model of the linear
   * solver for the extension.
   */
  bool hasAssertions() const { return d_hasAssertions; }

  /**
   * Assert each asserted int.star-contains literal to the model. The model
   * cannot evaluate an atom whose vector is in S* but not in S, e.g.
   *   (int.star-contains (lambda ((x Int)) (= x 2)) a)
   * with a = 4, so it takes the value of the literal, which the lemmas of
   * checkFullEffort guarantee.
   *
   * @param m the model
   * @return false if a literal could not be asserted to m
   */
  bool collectModelValues(TheoryModel* m);

 private:
  /**
   * Collect the facts asserted to arithmetic of the form
   * (int.star-contains ...) or (not (int.star-contains ...)).
   *
   * @param assertions the vector the literals are appended to
   */
  void getAssertions(std::vector<Node>& assertions);

  /**
   * Convert the body p of a lambda into one Normaliz constraint system per
   * disjunct of its DNF, see LiaStarUtils::toDNF and LiaStarUtils::getMatrices.
   * For example, the lambda
   *   (lambda ((x Int) (y Int)) (or (and (>= x 2) (= y 1)) (>= y 3)))
   * yields the pairs
   *   {"x[1] >= 2;", "x[2] = 1;"} with (and (>= x 2) (= y 1))
   *   {"x[2] >= 3;"} with (>= y 3)
   *
   * @param n a lambda (lambda ((x_1 Int) ... (x_n Int)) p) with p in LIA
   * @return one pair per disjunct: its constraints over the Normaliz
   * coordinates x[1]..x[n], together with the disjunct itself
   * @throws LogicException if p is not a Boolean combination of linear
   * integer constraints over x_1, ..., x_n, e.g. if it captures a constant,
   * see LiaStarUtils::getMatrices
   */
  const std::vector<std::pair<std::vector<std::string>, Node>>
  convertQFLIAToMatrices(Node n);

  /**
   * Eager path: build a Normaliz cone for every DNF disjunct of the predicate
   * and accumulate the star constraints over all of them, see steps 2 and 3
   * of the class documentation. Empty (infeasible) cones are skipped.
   *
   * @param n the int.star-contains atom; its children after the lambda are
   *   the vector y
   * @param pairs one (constraint rows, disjunct node) pair per disjunct, as
   *   returned by `convertQFLIAToMatrices`
   * @param skolems the vector the fresh multiplier skolems are appended to
   * @return the non-empty cones, each paired with the disjunct it came from
   *   (used by `getMembershipDisjuncts` for the debug trace), and the star
   *   constraints: the side constraints of the fresh multipliers plus the
   *   sum constraints tying y to the cones' contributions. Their conjunction
   *   is equivalent to `y in S*`.
   */
  std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
            std::vector<Node>>
  getCones(Node n,
           const std::vector<std::pair<std::vector<std::string>, Node>>& pairs,
           std::vector<Node>& skolems);

  /**
   * Lazy path: build the cone for a single disjunct and append it to the list
   * of cones for `lambda` stored in `d_lazyCones`. If the cone is empty (the
   * disjunct is infeasible) it is not added.
   *
   * @param lambda the lambda of the int.star-contains atom
   * @param pair the disjunct's constraint rows and node, as returned by
   *   `LiaStarUtils::getMatrix`
   */
  void addCone(Node lambda,
               const std::pair<std::vector<std::string>, Node>& pair);

  /**
   * Lazy path: return the star constraints of `atom` over all cones
   * accumulated so far in `d_lazyCones[lambda]` (the cones added by previous
   * calls to `addCone`).
   *
   * The per-cone constraints (and their fresh skolems) are computed only for
   * cones that have not been processed in a previous call and are accumulated
   * in `d_starConstraints[atom]`, so the skolems stay stable across
   * refinement rounds; the sum constraints, which span all cones, are rebuilt
   * from the accumulated `d_lambdas[atom]` on each call. The skolems are
   * recorded in `d_literalSkolems[atom]`.
   */
  std::vector<Node> getStarConstraints(Node atom, Node lambda);

  /**
   * Debug helper, used only for the "liastar-ext-smt" trace. Builds the
   * *membership* encoding `y in S`: one existentially quantified formula per
   * (cone, module generator) stating that y is the single element
   * `g + sum_j l_j h_j` of that cone. The disjunction of all returned
   * formulas is equivalent to the predicate itself, which the emitted trace
   * queries let an external solver verify.
   *
   * @param n the lambda
   * @param cones the cones with their originating disjuncts, as returned by
   *   `getCones`
   * @return each membership formula paired with the disjunct it encodes
   */
  std::vector<std::pair<Node, Node>> getMembershipDisjuncts(
      Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones);

  /**
   * Performs the eager Hilbert-basis reduction for a single int.star-contains
   * atom: sends the exact reduction lemma (= atom star), with star the
   * conjunction of the star constraints derived from the cones of `lambda`,
   * and records it with `recordReduction`.
   *
   * @param atom the int.star-contains atom
   * @param lambda the lambda of `atom`, see uf::FunctionConst::getDefinition
   * @param polarity whether the literal asserting `atom` is positive
   */
  void eagerCheckStar(Node atom, Node lambda, bool polarity);

  /**
   * Performs one round of the lazy Hilbert-basis reduction for a single
   * int.star-contains atom: refines the lambda's subsolver with the negations
   * of the cone-disjuncts discovered since the previous round, then delegates
   * to `lazyHilbert`. If the enumeration of the lambda's cells is complete
   * already (through an earlier round, possibly of another literal or in
   * another user context) the exact reduction is sent right away.
   *
   * For a positive literal the round may instead run the endgame check, or
   * be skipped by the patient option; the cell search is biased toward the
   * candidate model with the guided option. A negative literal takes none of
   * these shortcuts: it only needs the enumeration to complete.
   *
   * @param atom the int.star-contains atom
   * @param lambda the lambda of `atom`
   * @param polarity whether the literal asserting `atom` is positive
   * @param arithModel the model of the linear solver
   */
  void lazyCheckStar(Node atom,
                     Node lambda,
                     bool polarity,
                     const std::map<Node, Node>& arithModel);

  /**
   * A persistent, incremental subsolver dedicated to one lambda (one
   * int.star-contains predicate). It is used to enumerate the convex cells of
   * the predicate's satisfying region: it is seeded once with the
   * (nonnegative) predicate at the base user level and then refined across
   * rounds with the negations of the discovered cone-disjuncts, either one
   * assertion per disjunct (the default) or as a single cumulative refined
   * formula under push/pop (option arith-liastar-push-pop); see
   * `lazyCheckStar`.
   */
  struct Subsolver
  {
    /** the incremental QF_LIA subsolver. */
    std::unique_ptr<SolverEngine> engine;
    /** the lambda's bound variables ... */
    std::vector<Node> from;
    /** ... and the fresh skolem constants substituted for them, since a
     * subsolver cannot be given a formula with free (bound) variables. */
    std::vector<Node> to;
    /**
     * The (nonnegative) predicate in skolem space. It is already asserted in
     * `engine` at the base user level (so it survives every pop); it is kept
     * only to read off the predicate's atoms when building a disjunct from
     * the model.
     */
    Node base;
    /**
     * Push/pop strategy only: the union (disjunction), in skolem space, of
     * the cone-disjuncts discovered so far. Its negation is the refined
     * formula currently asserted in `engine`.
     */
    Node covered;
    /** Push/pop strategy only: whether a refined formula is currently
     * asserted, i.e. whether `engine` has a pushed frame to pop before
     * asserting the next refined formula. */
    bool pushed = false;
    /** number of cones in `d_lazyCones[lambda]` already negated in `engine`
     * (or, for the push/pop strategy, folded into `covered`). */
    size_t negated = 0;
    /**
     * Semantic generalization only: the probe subsolver, seeded with the
     * negation of `base`, used as the entailment oracle by
     * `LiaStarUtils::semanticGeneralize`. Created lazily by `getProbe`.
     */
    std::unique_ptr<SolverEngine> probe;
    /**
     * Cut synthesis only: the validity oracle, with `base` asserted. A
     * candidate inequality c*y >= 0 is valid for every point of the
     * predicate iff checking `c*y <= -1` as an assumption answers unsat;
     * a sat answer yields a counterexample point for the CEGIS loop.
     */
    std::unique_ptr<SolverEngine> validity;
  };

  /**
   * Returns the subsolver for `lambda`, creating and seeding it (with the
   * nonnegative predicate) on first use.
   */
  Subsolver& getSubsolver(Node lambda);

  /**
   * One lazy refinement round for `atom`: ask the subsolver for a model in
   * a region of the predicate not yet covered by a cone, read off the convex
   * cell containing it (`LiaStarUtils::getDisjunct`), and hand it to
   * `processDisjunct`.
   */
  void lazyHilbert(Node atom,
                   Node lambda,
                   Subsolver& sub,
                   bool polarity,
                   const std::vector<Node>& bias = {});

  /**
   * Shared tail of one lazy refinement round (used by both the subsolver and
   * the main-solver enumeration): turn `disjunct` -- a freshly discovered
   * cell of the predicate, in bound-variable space -- into a cone, rebuild
   * the star constraints over all cones found so far, and emit the reduction
   * lemma: guarded by a fresh boolean while the star is still an
   * under-approximation (`complete` false), unconditional once every cell is
   * covered (`complete` true, `disjunct` is then the false constraint). In
   * the latter case the exact reduction is recorded with `recordReduction`.
   */
  void processDisjunct(
      Node atom, Node lambda, Node disjunct, bool complete, bool polarity);

  /**
   * State for enumerating the convex cells of one lambda's predicate in the
   * main solver (option arith-liastar-main-solver), replacing the dedicated
   * subsolver. The lambda's bound variables are replaced by fresh skolems
   * (`from` -> `to`) that live in the main solver, constrained through a
   * chain of stage guards: h_0 => base, and for every discovered
   * cone-disjunct D_k a fresh h_k with h_k => h_{k-1} and h_k => not(D_k)
   * (two constant-size lemmas per stage, accumulate style). The current
   * stage guard h_k therefore activates `base and not(D_1) ... and not(D_k)`,
   * i.e. it places the skolems in a cell not yet covered by a cone; the cell
   * is then read off the main solver's candidate arithmetic model.
   *
   * The enumeration is driven by the literal itself: each stage emits the
   * (satisfiability-preserving) driver lemma
   *     literal => (p[v] or star_k or h_k),
   * so a model that claims the literal without certifying it must activate
   * h_k and thereby exhibit a fresh cell; once every cell is covered the h_k
   * branch closes by conflict and the driver leaves exactly the certified
   * branches. Completeness is additionally detected when the SAT solver
   * fixes the stage guard false at level 0 (`Valuation::isFixed`), at which
   * point the exact reduction is emitted. Only positive literals drive the
   * enumeration this way; a negative literal of the same lambda uses the
   * subsolver, see `lazyCheckStar`, and the two share the discovered cones.
   */
  struct MainEnum
  {
    /** the lambda's bound variables ... */
    std::vector<Node> from;
    /** ... and the fresh skolems substituted for them in the main solver. */
    std::vector<Node> to;
    /** The (nonnegative) predicate in skolem space. It is asserted under the
     * first stage guard; it is also used to read off the predicate's atoms
     * when building a disjunct from the model. */
    Node base;
    /** The current stage guard h_k (a decision variable, biased true). */
    Node guard;
    /** The first stage guard h_0 (kept to re-register the split's proof). */
    Node firstGuard;
    /** The split lemma on the first stage guard. */
    Node split;
    /**
     * Every enumeration lemma emitted for this lambda (the guarded predicate
     * and the per-stage implications). They are re-queued every round: the
     * inference manager's user-context lemma cache drops the duplicates for
     * free, and after a user pop (which retracts the lemmas but not this
     * non-context state) they are re-sent, so the enumeration constraints
     * stay in force in every user context.
     */
    std::vector<Node> lemmas;
    /** number of cones in `d_lazyCones[lambda]` already negated via stage
     * guards. */
    size_t negated = 0;
    /**
     * Semantic generalization only: the probe subsolver, seeded with the
     * negation of `base`, used as the entailment oracle by
     * `LiaStarUtils::semanticGeneralize`. Created lazily by `getProbe`.
     */
    std::unique_ptr<SolverEngine> probe;
    /**
     * Cut synthesis only: the validity oracle, with `base` asserted. A
     * candidate inequality c*y >= 0 is valid for every point of the
     * predicate iff checking `c*y <= -1` as an assumption answers unsat;
     * a sat answer yields a counterexample point for the CEGIS loop.
     */
    std::unique_ptr<SolverEngine> validity;
  };

  /**
   * Returns the main-solver enumeration state for `lambda`, creating it (and
   * queueing its seed lemmas: the guard split and `guard => base`) on first
   * use.
   */
  MainEnum& getMainEnum(Node lambda);

  /**
   * One refinement round of the main-solver lazy strategy for a positive
   * literal of `atom`: depending on the guard's value in the current SAT
   * assignment, read a fresh cell from the candidate model (guard true),
   * conclude completeness (guard fixed false), or bias the guard and wait
   * (otherwise). See `MainEnum`.
   */
  void mainSolverCheckStar(Node atom,
                           Node lambda,
                           const std::map<Node, Node>& arithModel);

  /**
   * Read the cell of `en.base` containing the current candidate arithmetic
   * model: fix the truth value of every atom of `en.base` under `arithModel`
   * (consulting `TheoryArith::getCandidateModelValue` for skolems missing
   * from the map) and return the conjunction in bound-variable space.
   * Returns the null node if some atom cannot be evaluated to a constant.
   */
  Node getModelDisjunct(MainEnum& en, const std::map<Node, Node>& arithModel);

  /**
   * Queue a main-solver enumeration lemma (InferenceId ARITH_LIA_STAR_ENUM),
   * skipping lemmas that rewrite to a constant.
   */
  void addEnumLemma(Node lemma);

  /**
   * Return the probe subsolver for semantic cell generalization (option
   * arith-liastar-generalize-semantic), creating it and asserting the
   * negation of `base` on first use; returns nullptr when the option is off.
   * `base` must be in the same skolem space as the literals later probed.
   */
  SolverEngine* getProbe(std::unique_ptr<SolverEngine>& probe, Node base);

  /**
   * Over-approximation cut synthesis state, per lambda (see
   * `synthesizeCuts`).
   */
  struct CutState
  {
    /** the cuts emitted so far, over the literal's vector terms */
    std::vector<Node> cuts;
    /** sample points of the predicate (module generators of discovered
     * cones, plus CEGIS counterexamples), as constant vectors */
    std::vector<std::vector<Node>> points;
    /** recession directions (Hilbert basis vectors of discovered cones) */
    std::vector<std::vector<Node>> rays;
    /** number of cones in `d_lazyCones` already sampled */
    size_t sampled = 0;
    /** consecutive failed synthesis attempts; give up after two */
    uint32_t failures = 0;
  };

  /**
   * Over-approximation cut synthesis (option arith-liastar-cuts), called
   * when the endgame check finds `facts and star_k` unsatisfiable. Any
   * homogeneous inequality `c * y >= 0` that is valid for every point of
   * the predicate is preserved under addition, so it holds for every point
   * of the star set and can be asserted for the vector wherever the literal
   * holds. The synthesis is a CEGIS loop: pick a target vector v* consistent
   * with the input facts and the cuts so far; solve for bounded integer
   * coefficients c with `c * p >= 0` for every known sample point and
   * recession direction of the predicate and `c * v* <= -1`; check validity
   * against the predicate (the `Subsolver::validity` oracle); counterexample
   * points are added as samples and the search repeats. Valid cuts are
   * emitted as lemmas (=> atom cut); once the cuts refute the input facts,
   * the main solver derives unsat by itself, without completing the cell
   * enumeration.
   */
  void synthesizeCuts(Node atom, Node lambda, const std::vector<Node>& facts);

  /**
   * One CEGIS cut search for `synthesizeCuts`: returns a valid cut
   * `c * v >= 0` separating `target` (the candidate vector's values) from
   * the star set's over-approximation, or null if none is found within the
   * iteration and coefficient bounds.
   */
  Node synthesizeOneCut(Node atom,
                        Subsolver& sub,
                        CutState& cs,
                        const std::vector<Node>& target,
                        const std::vector<bool>& zeroCoordinate,
                        uint64_t coefficientBound);

  /**
   * Decoupled endgame check (option arith-liastar-endgame=N): every N newly
   * discovered cones, solve the current arithmetic facts (excluding the
   * star literals themselves and any fact over liastar-created skolems)
   * together with the star under-approximation for `atom` in a *fresh*
   * subsolver -- a clean search for the integer multipliers, unencumbered by
   * the main search's stale guards, frozen phases, and lemma churn. If it
   * answers sat, the witness (values of the star formula's variables) is fed
   * back as a guarded hint lemma `d => (x_1 = c_1 and ...)` with `d` a fresh
   * decision variable biased true: sound unconditionally (`d` is fresh), and
   * it steers the main solver directly onto the verified model, after which
   * the model-value shortcut accepts.
   *
   * @return true if a hint was emitted (the round is then complete)
   */
  bool tryEndgame(Node atom, Node lambda);

  /**
   * Open a new enumeration stage for `en`: a fresh guard that activates the
   * previous stage's constraints plus the negation of the newly covered
   * cell `skolemDisjunct` (in skolem space).
   */
  void advanceStage(MainEnum& en, Node skolemDisjunct);

  /**
   * Emit, once per (atom, stage), the driver lemma
   * `atom => (p[v] or star or guard)`, where `star` is the star
   * under-approximation of `atom` over every cone discovered for `lambda`
   * so far (`v = 0`, the empty sum, before any cone has been discovered);
   * see `MainEnum`. Duplicates are dropped by the inference manager's
   * user-context lemma cache.
   */
  void emitDriverLemma(Node atom, Node lambda, MainEnum& en);

  /**
   * Record that the exact reduction lemma (= atom star) was sent in this user
   * context, and send the lemma for the negated atom if the literal is
   * negative, see sendNegatedReduction. The formula
   * (forall ((mu Int) ...) (not star)) that holds when the atom is false is
   * built by replacing `skolems` in `star` with bound variables; it is null,
   * and the negated lemma is not needed, if `star` has no skolems, as the
   * reduction is then exact on its own.
   *
   * @param atom the int.star-contains atom
   * @param star the constraints the atom was equated with, including, for the
   * partial-sums encoding, the definitional lemmas of its skolems
   * @param skolems the skolems of `star`
   * @param polarity whether the literal asserting `atom` is positive
   */
  void recordReduction(Node atom,
                       Node star,
                       const std::vector<Node>& skolems,
                       bool polarity);

  /**
   * Send the reduction lemma (or atom (forall ((mu Int) ...) (not C))) of a
   * negated atom, stored in d_negatedReductions, see recordReduction. Does
   * nothing if C has no skolems, as the reduction lemma (= atom C) is then
   * exact.
   *
   * @param atom an int.star-contains atom that is asserted false
   * @throws LogicException if the lemma is needed but the logic has no
   * quantifiers
   */
  void sendNegatedReduction(Node atom);

  /** node manager */
  NodeManager* d_nm;
  /** commonly used terms */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  /** The theory of arithmetic, whose asserted facts getAssertions reads */
  TheoryArith& d_arith;
  /** A reference to the arithmetic state object, for its valuation. */
  TheoryState& d_astate;
  /** The inference manager of TheoryArith, used to send lemmas. */
  InferenceManager& d_im;
  /** Callback for the extended theory below. */
  ExtTheoryCallback d_extTheoryCb;
  /** Extended theory, with which the int.star-contains terms are registered */
  ExtTheory d_extTheory;
  /** Whether an int.star-contains literal was asserted in this context */
  context::CDO<bool> d_hasAssertions;
  /**
   * Maps each atom whose exact reduction lemma was sent to the formula
   * (forall ((mu Int) ...) (not C)) that holds when the atom is false, or to
   * null if C has no skolems, see recordReduction. User-context dependent,
   * like the lemmas: after a user pop the exact reduction is sent again. No
   * further lazy refinement rounds run for these atoms.
   */
  context::CDHashMap<Node, Node> d_negatedReductions;
  /** The atoms whose negated reduction lemma was sent, user-context dependent
   */
  context::CDHashSet<Node> d_negatedReductionsSent;
  /** Statistics for the liastar extension */
  LiaStarStatistics d_stats;

  /**
   * The cones accumulated so far during the lazy Hilbert-basis reduction,
   * keyed by lambda. Each call to `addCone` appends the cone for the current
   * disjunct, and `getStarConstraints` computes the starLia constraints for
   * the newly added cones, accumulating them across calls. The cones depend
   * only on the predicate, so like the state below they are not
   * context-dependent: they stay valid in every user context.
   */
  std::map<Node, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>>
      d_lazyCones;

  /**
   * The lambdas whose cell enumeration is complete: every cell of the
   * predicate has a cone in `d_lazyCones`, so the star constraints over
   * these cones are exact.
   */
  std::unordered_set<Node> d_completeLambdas;

  /**
   * The per-cone starLia constraints computed so far for each
   * int.star-contains atom (the atom, not its lambda: atoms over one lambda
   * share the cone list but must not share the multiplier skolems, or their
   * sum constraints would force their vectors equal).
   * `getStarConstraints` only generates the skolems and constraints
   * for cones in `d_lazyCones` that have not been processed yet, appending
   * them here, so previously computed constraints (and their skolems) are
   * reused across refinement rounds. These are the constraints that are
   * independent of the other cones (the (>= mu 0), (>= l 0), and
   * (=> (= mu 0) (= l 0)) constraints); the sum constraints span all cones
   * and are rebuilt each call.
   */
  std::map<Node, std::vector<Node>> d_starConstraints;
  /**
   * The (point, rays) contributions computed so far for each atom,
   * kept in step with `d_starConstraints`. They are used to rebuild the sum
   * constraints over all cones on each call to `getStarConstraints`.
   */
  std::map<Node, std::vector<std::pair<Vector, std::vector<Vector>>>> d_lambdas;
  /** The number of cones in `d_lazyCones[lambda]` already processed, per
   * atom: each atom builds its own multipliers over the shared list. */
  std::map<Node, size_t> d_processedCones;
  /**
   * The skolems created for the star constraints of each atom (multipliers,
   * partial sums), in creation order. They are the bound variables of the
   * negated reduction lemma, see recordReduction.
   */
  std::map<Node, std::vector<Node>> d_literalSkolems;

  /**
   * Every skolem created for star constraints (multipliers, partial sums),
   * used by `tryEndgame` to exclude main-search facts over these skolems
   * from the endgame query (their trail polarities reflect the failing
   * search, not the input).
   */
  std::unordered_set<Node> d_starSkolems;

  /** The cone count at the last endgame check, per atom. */
  std::map<Node, size_t> d_lastEndgameCones;

  /** The guard of the last (still active) endgame hint, per atom;
   * deactivated when a newer witness replaces it. */
  std::map<Node, Node> d_lastHint;

  /** The cut synthesis state, per lambda. */
  std::map<Node, CutState> d_cutStates;

  /** The decision strategy carrying the active endgame hint; allocated and
   * registered with the decision manager on the first hint. */
  std::unique_ptr<LiaStarHintStrategy> d_hintStrategy;

  /**
   * Partial-sums encoding (option arith-liastar-partial-sums): the current
   * partial-sum skolems P_k for each atom, one per coordinate of the star
   * vector. P_k[i] equals the sum of every discovered cone's contribution to
   * coordinate i, via the definitions in `d_partialSumDefs`, so the star
   * formula is just `v = P_k`.
   */
  std::map<Node, std::vector<Node>> d_partialSums;

  /**
   * Partial-sums encoding: every definitional lemma for each atom -- the
   * per-cone multiplier constraints and the partial-sum definitions
   * `P_k[i] = P_{k-1}[i] + contribution_k[i]`. Emitted unguarded by
   * `processDisjunct` and re-queued each round (the user-context lemma cache
   * deduplicates and re-sends them after a pop).
   */
  std::map<Node, std::vector<Node>> d_partialSumDefs;

  /**
   * The last starLia under-approximation (`star`) computed for each
   * int.star-contains atom by `processDisjunct`. The model-value check in
   * `checkFullEffort` uses it to skip refinement when the current model
   * already satisfies the predicate or this under-approximation.
   */
  std::map<Node, Node> d_lastStarLia;

  /**
   * The fresh boolean guard of the last (still active) tentative reduction
   * `g => (atom = star)` emitted for each int.star-contains atom by
   * `processDisjunct`, or null once the exact reduction was sent. When a
   * later round produces a larger under-approximation, the previous guard is
   * deactivated (we assert `(not g)`), so at most one tentative reduction is
   * active per atom. User-context dependent, like the tentative lemma: the
   * patient option of `lazyCheckStar` trusts a guard that is asserted true
   * only while its lemma is in force.
   */
  context::CDHashMap<Node, Node> d_lastGuard;

  /**
   * The incremental subsolver for each lambda (int.star-contains predicate).
   * Each is created lazily and persists for the lifetime of the extension, so
   * the predicate's cells are enumerated incrementally across refinement
   * rounds.
   */
  std::map<Node, Subsolver> d_subsolvers;

  /**
   * The main-solver enumeration state for each lambda (option
   * arith-liastar-main-solver). Created lazily, like `d_subsolvers`.
   */
  std::map<Node, MainEnum> d_mainEnums;
}; /* class LiaStarExtension */

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H */

#endif /* CVC5_USE_NORMALIZ */

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
 * Extension to the theory of arithmetic handling the lia* (LIA star) operator.
 *
 * --------------------------------------------------------------------------
 * What the lia* operator means
 * --------------------------------------------------------------------------
 * A literal
 *     (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) v_1 ... v_n)
 * asserts that the vector v = (v_1, ..., v_n) belongs to the *star* (additive
 * closure) of the set
 *     S = { x in Z^n : p(x) and x >= 0 }.
 * The star of S is
 *     S* = { the sum of finitely many (>= 0) elements of S },
 * with the empty sum giving the zero vector. So v in S* iff v can be written as
 * a finite sum of vectors each of which satisfies the predicate p (and is
 * non-negative). This is the integer analogue of Kleene star in the monoid
 * (Z^n, +); the sets S* are exactly the (non-negative) semilinear sets.
 *
 * --------------------------------------------------------------------------
 * The decision procedure (Levatich, Bjorner, Piskac, Shoham, VMCAI 2020,
 * "Solving LIA* Using Approximations")
 * --------------------------------------------------------------------------
 * 1. Put p into disjunctive normal form, p <=> D_1 or ... or D_m, where each
 *    D_j is a conjunction of linear (in)equalities, i.e. a convex polyhedron.
 *    Then S = S_1 union ... union S_m, with S_j the integer points of D_j (in
 *    the non-negative orthant). (See liastar_utils.cpp for the normalization.)
 *
 * 2. The additive closure distributes over the union as a Minkowski sum:
 *        S* = S_1* + ... + S_m*,
 *    because any sum of elements of S can be grouped by the polyhedron each
 *    summand came from. So a vector is in S* iff it is the sum of one
 *    contribution from each cone's semigroup S_j* (each including 0).
 *
 * 3. For each polyhedron Normaliz computes a Hilbert basis and module
 *    generators. The integer points of D_j are
 *        { g + sum_k l_k h_k : g a module generator, l_k >= 0 },
 *    where the h_k are the Hilbert basis of the recession cone (its rays). The
 *    semigroup S_j* is then captured by giving each module generator g a
 *    non-negative multiplier mu_g (how many copies of g are taken) and each ray
 *    a multiplier l_k, coupled by `mu_g = 0 => l_k = 0` (a ray of g is only
 *    available when g itself is used). See `LiaStarUtils::getGeneratorBody`.
 *
 * 4. Summing these contributions over all cones gives the *star constraints*: a
 *    system of linear constraints over fresh non-negative integers whose
 *    satisfiability is equivalent to `v in S*`. The extension then emits the
 *    reduction lemma `literal = star`.
 *
 * --------------------------------------------------------------------------
 * Two strategies
 * --------------------------------------------------------------------------
 * Eager (`eagerCheckStar`): compute the full DNF, build every cone up front and
 *   emit the exact equivalence `literal = star` in one shot.
 *
 * Lazy (`lazyCheckStar` / `lazyHilbert`): the DNF can blow up, so instead keep a
 *   persistent incremental QF_LIA subsolver seeded with p (and x >= 0). Each
 *   round it produces a model in a region of p not yet covered by a cone; the
 *   convex cell containing that model is read off (`LiaStarUtils::getDisjunct`),
 *   turned into a cone, and added to the accumulated set. The star built from
 *   the cones found so far is an *under-approximation*, so the equivalence is
 *   asserted only tentatively under a fresh boolean guard `g` (`g => (literal =
 *   star)`), biased true, until the subsolver becomes unsat -- meaning every
 *   cell of p is covered and the encoding is exact, at which point the
 *   unconditional equivalence is emitted.
 *
 * --------------------------------------------------------------------------
 * Where lemmas come from
 * --------------------------------------------------------------------------
 * `checkFullEffort` is the entry point. For each STAR_CONTAINS assertion it
 * emits:
 *   - a non-negativity lemma (the vector lives in the non-negative orthant);
 *   - a split on the substituted predicate `p[v]` (if v itself satisfies p it
 *     is a single-summand member of S*);
 *   - and then, unless the current model already satisfies the literal, the
 *     star reduction via the eager or lazy strategy.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

#include <algorithm>

#include "expr/node_algorithm.h"
#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/inference_manager.h"
#include "theory/decision_manager.h"
#include "theory/arith/theory_arith.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

using namespace libnormaliz;

using libnormaliz::operator<<;

template <typename T>
std::string toString(const std::vector<T>& l)
{
  std::stringstream ss;
  for (const auto& i : l)
  {
    ss << i << " ";
  }
  ss << std::endl;
  return ss.str();
}

namespace {

/**
 * Build the "sum constraints" that tie the star vector to the cone
 * contributions: for each coordinate i,
 *     vec[i] = sum over all generators of (point[i] + sum over rays of ray[i]).
 * `lambdas` holds one (point, rays) contribution per module generator across
 * all cones (as produced by `LiaStarUtils::getGeneratorBody`); `vec` is the
 * star vector (the v_1 ... v_n). Returns the n equalities.
 */
std::vector<Node> buildSumConstraints(
    NodeManager* nm,
    Node zero,
    const std::vector<Node>& vec,
    const std::vector<std::pair<Vector, std::vector<Vector>>>& lambdas)
{
  size_t dimension = vec.size();
  Vector sums(dimension, zero);
  for (const std::pair<Vector, std::vector<Vector>>& lambda : lambdas)
  {
    for (size_t i = 0; i < dimension; i++)
    {
      sums[i] = nm->mkNode(Kind::ADD, sums[i], lambda.first[i]);
      for (const Vector& ray : lambda.second)
      {
        sums[i] = nm->mkNode(Kind::ADD, sums[i], ray[i]);
      }
    }
  }
  std::vector<Node> result;
  for (size_t i = 0; i < dimension; i++)
  {
    result.push_back(vec[i].eqNode(sums[i]));
  }
  return result;
}

/**
 * Trace the cone's Hilbert basis and return its module generators -- the base
 * lattice points g of the decomposition { g + sum_j l_j h_j } of the cone's
 * integer points. A purely homogeneous cone has no module generators; its
 * single base point is then the origin, so the zero vector is returned
 * instead.
 */
std::vector<std::vector<Integer>> getConeGenerators(
    libnormaliz::Cone<Integer>& cone, size_t dimension)
{
  Trace("liastar-ext") << "Hilbert basis:" << std::endl;
  for (const auto& basis : cone.getHilbertBasis())
  {
    Trace("liastar-ext") << toString(basis) << std::endl;
  }
  Trace("liastar-ext") << "Module generators:" << std::endl;
  if (!cone.getModuleGenerators().empty())
  {
    return cone.getModuleGenerators();
  }
  return {std::vector<Integer>(dimension, Integer(0))};
}

/**
 * Emit the preamble of a self-contained SMT-LIB script on the
 * "liastar-ext-smt" channel: solver options plus a declaration and a
 * non-negativity assertion for every star variable in `variables`. The
 * queries later emitted on the same channel (see
 * `LiaStarUtils::traceDistinctQuery`) then form a replayable soundness check
 * of the reduction: every (check-sat) must answer unsat.
 */
void traceSmtPreamble(Node variables)
{
  // `!TraceIsOn(...)` does not compile in non-tracing builds, so guard
  // positively.
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(set-logic ALL)" << std::endl;
    Trace("liastar-ext-smt") << "(set-option :incremental true)" << std::endl;
    Trace("liastar-ext-smt") << "(set-option :produce-models true)" << std::endl;
    for (Node var : variables)
    {
      Trace("liastar-ext-smt") << "(declare-const " << var << " Int)"
                               << std::endl;
    }
    for (Node var : variables)
    {
      Trace("liastar-ext-smt") << "(assert (>= " << var << " 0))" << std::endl;
    }
  }
}

/**
 * Emit, on the "liastar-ext-smt" channel, the queries validating the
 * membership encoding: one query per disjunct asserting it differs from the
 * predicate cell it encodes, and a final query asserting the whole predicate
 * (lambda[1]) differs from the disjunction of all membership formulas. All of
 * them must be unsat when the trace is replayed.
 */
void traceMembershipValidation(NodeManager* nm,
                               Node lambda,
                               const std::vector<std::pair<Node, Node>>& lia)
{
  for (size_t i = 0; i < lia.size(); i++)
  {
    LiaStarUtils::traceDistinctQuery(
        std::to_string(i), lia[i].first, lia[i].second);
  }
  std::vector<Node> disjunctions;
  std::transform(
      lia.begin(), lia.end(), std::back_inserter(disjunctions), [](auto& p) {
        return p.second;
      });
  Node liaFormula;
  if (disjunctions.size() == 0)
  {
    liaFormula = nm->mkConst(false);
  }
  else if (disjunctions.size() == 1)
  {
    liaFormula = disjunctions[0];
  }
  else
  {
    liaFormula = nm->mkNode(Kind::OR, disjunctions);
  }
  LiaStarUtils::traceDistinctQuery("lia formula: ", lambda[1], liaFormula);
}

}  // namespace

LiaStarExtension::LiaStarExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_nm(nodeManager()),
      d_arith(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_checkCounter(0),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasLiaStarTerms(context(), false)
{
  d_extTheory.addFunctionKind(Kind::STAR_CONTAINS);
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
  // Proofs are produced lazily; allocate the generator only when needed.
  if (env.isTheoryProofProducing())
  {
    d_proofGen.reset(new LiaStarProofGenerator(env, env.getUserContext()));
  }
}

LiaStarExtension::~LiaStarExtension() {}

void LiaStarExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-dependent simplification.
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_hasLiaStarTerms = true;
    d_extTheory.registerTerm(n);
  }
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
  // Collect the STAR_CONTAINS atoms among the arithmetic facts. Both polarities
  // are reduced to the positive atom: a negated `(not (star-contains ...))` is
  // handled by the same reduction lemma `literal = star` (the surrounding SAT
  // solver applies the negation).
  Trace("liastar-ext") << "Getting assertions..." << std::endl;
  Trace("liastar-ext") << "---------------------" << std::endl;
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-ext") << lit << std::endl;
    Node atom;
    if (lit.getKind() == Kind::STAR_CONTAINS)
    {
      // positive polarity of star-contains
      atom = lit;
    }
    else if (lit.getKind() == Kind::NOT
             && lit[0].getKind() == Kind::STAR_CONTAINS)
    {
      // negative polarity of star-contains (the same reduction lemma applies)
      atom = lit[0];
    }
    else
    {
      continue;
    }
    // The predicate argument is normally a LAMBDA, but a *constant* lambda is
    // rewritten into a FUNCTION_ARRAY_CONST (no children). Rebuild the atom
    // with the lambda form so every structural access below (lambda[0],
    // lambda[1], ...) is well-defined. The rebuilt atom rewrites back to the
    // original, so the reduction lemma still attaches to the asserted literal.
    if (atom[0].getKind() != Kind::LAMBDA)
    {
      std::vector<Node> children;
      children.push_back(uf::FunctionConst::toLambda(atom[0]));
      children.insert(children.end(), atom.begin() + 1, atom.end());
      atom = d_nm->mkNode(Kind::STAR_CONTAINS, children);
    }
    assertions.push_back(atom);
  }
  Trace("liastar-ext") << "---------------------" << std::endl;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  // Last-call effort check: for each STAR_CONTAINS assertion emit the necessary
  // lemmas and, if the current model does not already satisfy the literal,
  // refine via the eager or lazy star reduction.
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    Node lambda = literal[0];
    Assert(literal.getKind() == Kind::STAR_CONTAINS);
    // vectorPredicate = p[v] (v satisfies p) and nonnegative = (and (>= v_i 0)).
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(literal, nm);

    // (1) Membership in S* requires v to be in the non-negative orthant.
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerNonnegative(nonnegative, literal);
    }
    d_im.addPendingLemma(
        nonnegative, InferenceId::ARITH_LIA_STAR_NONNEGATIVE, d_proofGen.get());

    // (2) Split on whether v itself satisfies p: if so, v is a single-summand
    // member of S* and the literal holds directly.
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerSplit(split, vectorPredicate);
    }
    d_im.addPendingLemma(
        split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    if (options().arith.arithLiaStarModelValue)
    {
      // Model-value shortcut: if the current arithmetic model already satisfies
      // the predicate p[v] (or the last computed star under-approximation),
      // then the literal holds in this model and no further refinement is
      // needed this round.
      std::vector<Node> keys;
      std::vector<Node> values;

      for (const auto& [key, value] : arithModel)
      {
        keys.push_back(key);
        values.push_back(value);
      }

      // F: the membership predicate. Additionally consider the last computed
      // starLia under-approximation, if any: if the model already satisfies
      // F or that under-approximation, the literal already holds and no further
      // refinement is needed.
      Node f = vectorPredicate;
      auto starIt = d_lastStarLia.find(literal);
      Node check = starIt != d_lastStarLia.end() ? f.orNode(starIt->second) : f;

      Node value = check.substitute(
          keys.begin(), keys.end(), values.begin(), values.end());
      value = rewrite(value);

      Trace("liastar-ext-debug") << "value: " << value << std::endl;

      if (value == d_true)
      {
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        Trace("liastar-ext-debug")
            << literal << " is satisfied in the current model" << std::endl;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        return;
      }
    }
    // (3) Refine: reduce the star literal to its cone/Hilbert-basis encoding.
    if (options().arith.arithLiaStarLazy)
    {
      if (options().arith.arithLiaStarMainSolver)
      {
        mainSolverCheckStar(literal, lambda, arithModel);
      }
      else
      {
        lazyCheckStar(literal, lambda, arithModel);
      }
    }
    else
    {
      eagerCheckStar(literal, lambda);
    }
  }
}

void LiaStarExtension::eagerCheckStar(Node literal, Node lambda)
{
  // Eager reduction: compute every cone of p up front and emit the exact
  // equivalence `literal = star`. Each literal is reduced at most once.
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }
  // Normalize p to DNF and render each disjunct as a Normaliz constraint matrix.
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      convertQFLIAToMatrices(lambda);

  // Build the cones and the star constraints over all of them.
  auto [cones, starConstraints] = getCones(literal, pairs);

  if (TraceIsOn("liastar-ext-smt"))
  {
    // Debug only: build the per-cone membership encoding (v in S, a single
    // element) and emit (check-sat) queries asserting it is equivalent to the
    // predicate, so a separate solver run can validate the cone decomposition.
    // The actual lemma below uses `starConstraints`, not `lia`.
    std::vector<std::pair<Node, Node>> lia =
        getMembershipDisjuncts(lambda, cones);
    Trace("liastar-ext") << "lia constraint: " << std::endl;
    traceMembershipValidation(d_nm, lambda, lia);
  }
  Node star = d_nm->mkNode(Kind::AND, starConstraints);
  Trace("liastar-ext") << "starConstraints: " << std::endl
                       << toString(starConstraints) << std::endl;
  star = rewrite(star);
  Node lemma = literal.eqNode(star);
  Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerContainsReduce(lemma, literal, star);
  }
  d_im.addPendingLemma(
      lemma, InferenceId::ARITH_LIA_STAR_EXISTS, d_proofGen.get());
  d_processedStarTerms.push_back(literal);
  d_im.doPendingLemmas();
}

LiaStarExtension::Subsolver& LiaStarExtension::getSubsolver(Node lambda)
{
  // Return the persistent incremental subsolver for `lambda`, creating and
  // seeding it on first use. It is used by the lazy strategy to enumerate the
  // convex cells of the predicate's satisfying region.
  auto it = d_subsolvers.find(lambda);
  if (it != d_subsolvers.end())
  {
    return it->second;
  }
  Subsolver& sub = d_subsolvers[lambda];

  Options subOptions;
  // we read the model below to construct the disjunct.
  subOptions.write_smt().produceModels = true;
  sub.engine = std::make_unique<SolverEngine>(d_nm, &subOptions);
  sub.engine->setIsInternalSubsolver();
  LogicInfo info("QF_LIA");
  sub.engine->setLogic(info);
  sub.engine->setOption("incremental", "true");

  // The base assertion is the membership predicate (with ites and negations
  // eliminated) conjoined with the non-negativity of the lambda's variables.
  Node base = LiaStarUtils::removeItesAndNots(lambda[1], &d_env);
  std::vector<Node> conjuncts{base};
  for (Node var : lambda[0])
  {
    conjuncts.push_back(d_nm->mkNode(Kind::GEQ, var, d_zero));
  }
  base =
      conjuncts.size() == 1 ? conjuncts[0] : d_nm->mkNode(Kind::AND, conjuncts);

  // The lambda's bound variables appear free in `base`. A formula with free
  // (bound) variables cannot be asserted to a subsolver, so we replace them
  // with fresh free constants and remember the mapping so the disjunct built
  // from the model can be substituted back into bound-variable space.
  for (Node var : lambda[0])
  {
    if (var.getKind() == Kind::BOUND_VARIABLE)
    {
      sub.from.push_back(var);
      sub.to.push_back(d_nm->mkDummySkolem("liastar", var.getType()));
    }
  }
  if (!sub.from.empty())
  {
    base = base.substitute(
        sub.from.begin(), sub.from.end(), sub.to.begin(), sub.to.end());
  }
  sub.base = base;
  sub.engine->assertFormula(base);
  return sub;
}

void LiaStarExtension::synthesizeCuts(Node literal,
                                      Node lambda,
                                      const std::vector<Node>& facts)
{
  // Over-approximation cuts: called when the endgame found the star
  // under-approximation insufficient for the input facts. See the header for
  // the algorithm; the short version: valid homogeneous inequalities of the
  // predicate survive addition, so they bound the star set from above and
  // can refute unsatisfiable instances without completing the enumeration.
  if (!options().arith.arithLiaStarCuts)
  {
    return;
  }
  CutState& cs = d_cutStates[lambda];
  if (cs.failures >= 2)
  {
    return;
  }
  Subsolver& sub = getSubsolver(lambda);
  size_t dimension = literal.getNumChildren() - 1;
  if (sub.to.size() != dimension)
  {
    // coordinate mapping would be ambiguous; bail out
    return;
  }
  // Coordinates where the vector is the constant zero: every summand of a
  // nonnegative decomposition is zero there too, so cuts only need to be
  // valid on that restriction of the predicate -- a strictly larger space of
  // valid cuts.
  std::vector<bool> zeroCoordinate(dimension, false);
  for (size_t i = 0; i < dimension; i++)
  {
    zeroCoordinate[i] = literal[i + 1] == d_zero;
  }

  // Refresh the sample points and recession directions from the cones
  // discovered since the last call: their module generators are concrete
  // points of the predicate, and their Hilbert bases are its recession
  // directions, so a valid cut must be nonnegative on all of them.
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[lambda];
  if (cs.sampled < cones.size())
  {
    // new cones bring new sample points: give the synthesis another chance
    cs.failures = 0;
  }
  for (; cs.sampled < cones.size(); cs.sampled++)
  {
    Cone<Integer>& cone = cones[cs.sampled].second;
    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      std::vector<Node> point;
      for (const auto& entry : generator)
      {
        point.push_back(d_nm->mkConstInt(Rational(entry)));
      }
      cs.points.push_back(point);
    }
    for (const auto& basis : cone.getHilbertBasis())
    {
      std::vector<Node> ray;
      for (const auto& entry : basis)
      {
        ray.push_back(d_nm->mkConstInt(Rational(entry)));
      }
      cs.rays.push_back(ray);
    }
  }

  // The validity oracle: the predicate asserted once; candidate cuts are
  // checked as assumptions.
  if (sub.validity == nullptr)
  {
    Options validityOptions;
    validityOptions.write_smt().produceModels = true;
    sub.validity = std::make_unique<SolverEngine>(d_nm, &validityOptions);
    sub.validity->setIsInternalSubsolver();
    LogicInfo info("QF_LIA");
    sub.validity->setLogic(info);
    sub.validity->assertFormula(sub.base);
  }

  bool emitted = false;
  for (size_t round = 0; round < 8; round++)
  {
    // (1) a target vector consistent with the input facts and the cuts so
    // far; once none exists, the emitted cut lemmas refute the facts and the
    // main solver concludes unsat by itself
    Options targetOptions;
    targetOptions.write_smt().produceModels = true;
    SolverEngine target(d_nm, &targetOptions);
    target.setIsInternalSubsolver();
    LogicInfo targetInfo("QF_LIA");
    target.setLogic(targetInfo);
    for (const Node& fact : facts)
    {
      target.assertFormula(fact);
    }
    for (const Node& cut : cs.cuts)
    {
      target.assertFormula(cut);
    }
    Result result = target.checkSat();
    Trace("liastar-cuts") << "cuts target check: " << result << std::endl;
    if (result.getStatus() == Result::Status::UNSAT)
    {
      break;
    }
    if (result.getStatus() != Result::Status::SAT)
    {
      break;
    }
    std::vector<Node> targetValues;
    bool known = true;
    for (size_t i = 0; i < dimension; i++)
    {
      Node value = target.getValue(literal[i + 1]);
      if (value.isNull() || !value.isConst())
      {
        known = false;
        break;
      }
      targetValues.push_back(value);
    }
    if (!known)
    {
      break;
    }

    // (2) search for a valid cut separating the target. The L1 budget on
    // the coefficients keeps the candidates sparse, which both matches the
    // cuts that exist in practice and makes the counterexample-guided search
    // converge: an unconstrained box admits arbitrary dense candidates that
    // the validity oracle rejects one by one.
    Node cut;
    for (uint64_t budget : {4, 9, 16, 30})
    {
      cut = synthesizeOneCut(
          literal, sub, cs, targetValues, zeroCoordinate, budget);
      if (!cut.isNull())
      {
        break;
      }
    }
    if (cut.isNull())
    {
      cs.failures++;
      break;
    }
    cs.failures = 0;
    cs.cuts.push_back(cut);
    Trace("liastar-cuts") << "cut: " << cut << std::endl;
    if (!rewrite(cut).isConst())
    {
      d_im.addPendingLemma(cut, InferenceId::ARITH_LIA_STAR_CUT);
      emitted = true;
    }
  }
  if (emitted)
  {
    d_im.doPendingLemmas();
  }
}

Node LiaStarExtension::synthesizeOneCut(Node literal,
                                        Subsolver& sub,
                                        CutState& cs,
                                        const std::vector<Node>& target,
                                        const std::vector<bool>& zeroCoordinate,
                                        uint64_t coefficientBound)
{
  // a sample participates only if it lies in the zero-forced restriction
  auto restricted = [&](const std::vector<Node>& vec) {
    for (size_t i = 0; i < vec.size(); i++)
    {
      if (zeroCoordinate[i] && vec[i] != d_zero
          && !(vec[i].isConst()
               && vec[i].getConst<Rational>().sgn() == 0))
      {
        return false;
      }
    }
    return true;
  };
  // CEGIS for bounded integer coefficients c with c*p >= 0 on every sample
  // point and recession direction, and c*target <= -1. Each candidate is
  // checked against the whole predicate via the validity oracle;
  // counterexamples become new sample points.
  size_t dimension = target.size();
  Node zero = d_zero;
  Node minusOne = d_nm->mkConstInt(Rational(-1));
  Node budget = d_nm->mkConstInt(Rational(coefficientBound));

  Options searchOptions;
  searchOptions.write_smt().produceModels = true;
  SolverEngine search(d_nm, &searchOptions);
  search.setIsInternalSubsolver();
  LogicInfo info("QF_LIA");
  search.setLogic(info);
  search.setOption("incremental", "true");

  // coefficients with |c_1| + ... + |c_d| <= budget (sparsity)
  std::vector<Node> coefficients;
  std::vector<Node> magnitudes;
  for (size_t i = 0; i < dimension; i++)
  {
    Node c = d_nm->mkDummySkolem("liastarCutCoeff", d_nm->integerType());
    Node a = d_nm->mkDummySkolem("liastarCutAbs", d_nm->integerType());
    coefficients.push_back(c);
    magnitudes.push_back(a);
    search.assertFormula(d_nm->mkNode(Kind::GEQ, a, c));
    search.assertFormula(
        d_nm->mkNode(Kind::GEQ, a, d_nm->mkNode(Kind::NEG, c)));
  }
  Node l1 = zero;
  for (const Node& a : magnitudes)
  {
    l1 = d_nm->mkNode(Kind::ADD, l1, a);
  }
  search.assertFormula(d_nm->mkNode(Kind::LEQ, l1, budget));
  auto dot = [&](const std::vector<Node>& vec) {
    Node sum = zero;
    for (size_t i = 0; i < dimension; i++)
    {
      sum = d_nm->mkNode(
          Kind::ADD, sum, d_nm->mkNode(Kind::MULT, coefficients[i], vec[i]));
    }
    return sum;
  };
  for (const std::vector<Node>& point : cs.points)
  {
    // Only points inside the zero-forced restriction constrain the search: a
    // point of the predicate with zeros on the restricted coordinates lies in
    // the restricted region itself. Rays are deliberately NOT used: a ray of
    // an unrestricted cell has zeros on the pinned coordinates yet describes
    // a direction outside the restriction, and requiring nonnegativity on it
    // would exclude valid conditional cuts; the counterexample loop below
    // discovers genuinely violating directions soundly instead.
    if (restricted(point))
    {
      search.assertFormula(d_nm->mkNode(Kind::GEQ, dot(point), zero));
    }
  }
  search.assertFormula(d_nm->mkNode(Kind::LEQ, dot(target), minusOne));

  for (size_t iteration = 0; iteration < 60; iteration++)
  {
    Result result = search.checkSat();
    if (result.getStatus() != Result::Status::SAT)
    {
      return Node();
    }
    std::vector<Node> values;
    for (size_t i = 0; i < dimension; i++)
    {
      Node value = search.getValue(coefficients[i]);
      if (value.isNull() || !value.isConst())
      {
        return Node();
      }
      values.push_back(value);
    }
    // validity: does c*y >= 0 hold for every point of the predicate?
    Node candidate = zero;
    for (size_t i = 0; i < dimension; i++)
    {
      candidate = d_nm->mkNode(
          Kind::ADD,
          candidate,
          d_nm->mkNode(Kind::MULT, values[i], sub.to[i]));
    }
    std::vector<Node> assumptions{
        d_nm->mkNode(Kind::LEQ, candidate, minusOne)};
    for (size_t i = 0; i < dimension; i++)
    {
      if (zeroCoordinate[i])
      {
        assumptions.push_back(sub.to[i].eqNode(d_zero));
      }
    }
    Result validity = sub.validity->checkSat(assumptions);
    if (validity.getStatus() == Result::Status::UNSAT)
    {
      // valid for the whole predicate: build the cut over the vector terms
      Node lhs = zero;
      for (size_t i = 0; i < dimension; i++)
      {
        lhs = d_nm->mkNode(
            Kind::ADD,
            lhs,
            d_nm->mkNode(Kind::MULT, values[i], literal[i + 1]));
      }
      return d_nm->mkNode(Kind::GEQ, lhs, zero);
    }
    if (validity.getStatus() != Result::Status::SAT)
    {
      return Node();
    }
    // counterexample: a predicate point with c*y < 0; add it as a sample
    std::vector<Node> counterexample;
    for (size_t i = 0; i < dimension; i++)
    {
      Node value = sub.validity->getValue(sub.to[i]);
      if (value.isNull() || !value.isConst())
      {
        return Node();
      }
      counterexample.push_back(value);
    }
    cs.points.push_back(counterexample);
    search.assertFormula(d_nm->mkNode(Kind::GEQ, dot(counterexample), zero));
  }
  return Node();
}

bool LiaStarExtension::tryEndgame(Node literal, Node lambda)
{
  uint64_t period = options().arith.arithLiaStarEndgame;
  if (period == 0)
  {
    return false;
  }
  size_t cones = d_lazyCones[lambda].size();
  size_t& last = d_lastEndgameCones[literal];
  if (cones < last + period)
  {
    return false;
  }
  last = cones;

  // The arithmetic facts entailed by the input (fixed at decision level 0):
  // facts decided or propagated under the current branch would pin the
  // vector to the failing search's region and poison the query. Also
  // excluded: the star literals themselves (they cannot be asserted to a
  // plain QF_LIA subsolver) and any fact over liastar-created star skolems.
  std::vector<Node> facts;
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node fact = (*it).d_assertion;
    Node atom = fact.getKind() == Kind::NOT ? fact[0] : fact;
    if (atom.getKind() == Kind::STAR_CONTAINS)
    {
      continue;
    }
    if (!d_astate.getValuation().isFixed(fact))
    {
      continue;
    }
    std::unordered_set<Node> symbols;
    expr::getSymbols(atom, symbols);
    bool overStarSkolems = false;
    for (const Node& symbol : symbols)
    {
      if (d_starSkolems.count(symbol) > 0)
      {
        overStarSkolems = true;
        break;
      }
    }
    if (!overStarSkolems)
    {
      facts.push_back(fact);
    }
  }

  std::vector<Node> star = getStarConstraints(literal);

  // A fresh subsolver: a clean search for the integer multipliers,
  // unencumbered by the main search's stale guards and frozen phases.
  Options endgameOptions;
  endgameOptions.write_smt().produceModels = true;
  endgameOptions.write_smt().unsatAssumptions = true;
  SolverEngine endgame(d_nm, &endgameOptions);
  endgame.setIsInternalSubsolver();
  LogicInfo info("QF_LIA");
  endgame.setLogic(info);
  for (const Node& constraint : star)
  {
    endgame.assertFormula(constraint);
  }
  // the facts go in as assumptions, so an unsat answer exposes which of them
  // conflict with the star via the unsat-assumptions core
  Result result = endgame.checkSat(facts);
  Trace("liastar-ext") << "endgame at " << cones
                       << " cones: " << result << std::endl;
  if (TraceIsOn("liastar-endgame"))
  {
    Trace("liastar-endgame") << "endgame query at " << cones << " cones, "
                             << facts.size() << " facts, " << star.size()
                             << " star constraints; result " << result
                             << std::endl;
    for (const Node& fact : facts)
    {
      Trace("liastar-endgame") << "  fact: " << fact << std::endl;
    }
    if (result.getStatus() == Result::Status::UNSAT)
    {
      for (const Node& core : endgame.getUnsatAssumptions())
      {
        Trace("liastar-endgame") << "  core: " << core << std::endl;
      }
    }
  }
  if (TraceIsOn("liastar-endgame-smt"))
  {
    // dump the whole query as a replayable script
    std::unordered_set<Node> symbols;
    for (const Node& constraint : star)
    {
      expr::getSymbols(constraint, symbols);
    }
    for (const Node& fact : facts)
    {
      expr::getSymbols(fact, symbols);
    }
    Trace("liastar-endgame-smt") << "(set-logic QF_LIA)" << std::endl;
    for (const Node& symbol : symbols)
    {
      Trace("liastar-endgame-smt")
          << "(declare-const |" << symbol << "| " << symbol.getType() << ")"
          << std::endl;
    }
    for (const Node& constraint : star)
    {
      Trace("liastar-endgame-smt")
          << "(assert " << constraint << ")" << std::endl;
    }
    for (const Node& fact : facts)
    {
      Trace("liastar-endgame-smt") << "(assert " << fact << ")" << std::endl;
    }
    Trace("liastar-endgame-smt") << "(check-sat)" << std::endl;
  }
  if (result.getStatus() != Result::Status::SAT)
  {
    if (result.getStatus() == Result::Status::UNSAT)
    {
      // The under-approximation cannot justify the literal yet; try the
      // over-approximation side: synthesize valid cuts that may refute the
      // input facts outright.
      synthesizeCuts(literal, lambda, facts);
    }
    return false;
  }

  // The star is satisfiable together with the input facts: read the witness
  // over the star formula's variables and feed it back as a guarded hint, so
  // the main solver is steered onto the verified model (sound regardless of
  // the endgame answer, since the guard is fresh).
  std::unordered_set<Node> variables;
  for (const Node& constraint : star)
  {
    expr::getSymbols(constraint, variables);
  }
  std::vector<Node> equalities;
  for (const Node& variable : variables)
  {
    Node value = endgame.getValue(variable);
    if (!value.isNull() && value.isConst()
        && value.getType() == variable.getType())
    {
      equalities.push_back(variable.eqNode(value));
    }
  }
  if (equalities.empty())
  {
    return false;
  }
  Node hint = equalities.size() == 1 ? equalities[0]
                                     : d_nm->mkNode(Kind::AND, equalities);
  // At most one hint is active per literal: witnesses from different endgame
  // rounds pin the same variables to different values, so competing
  // (phase-preferred) hints would fight each other. Sound because the guards
  // are fresh.
  auto hintIt = d_lastHint.find(literal);
  if (hintIt != d_lastHint.end())
  {
    Node deactivate = hintIt->second.notNode();
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerGuardDeactivate(deactivate);
    }
    d_im.addPendingLemma(
        deactivate, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
  }
  Node d = d_nm->mkDummySkolem("liastarHint", d_nm->booleanType());
  d = d_astate.getValuation().ensureLiteral(d);
  d_im.preferPhase(d, true);
  d_lastHint[literal] = d;
  Node split = d.orNode(d.notNode());
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerSplit(split, d);
  }
  d_im.addPendingLemma(
      split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
  d_im.addPendingLemma(d.impNode(hint), InferenceId::ARITH_LIA_STAR_HINT);
  d_im.doPendingLemmas();
  // Hand the witness to the SAT solver as forced decisions (guard first,
  // then each equality): a phase preference alone never engages, since some
  // of the pinned variables are always already bound differently.
  if (d_hintStrategy == nullptr)
  {
    d_hintStrategy = std::make_unique<LiaStarHintStrategy>(
        d_env, d_astate.getValuation());
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_ARITH_LIA_STAR_HINT,
        d_hintStrategy.get(),
        DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
  }
  std::vector<Node> decisions{d};
  for (const Node& equality : equalities)
  {
    Node ensured = d_astate.getValuation().ensureLiteral(equality);
    if (!ensured.isNull())
    {
      decisions.push_back(ensured);
    }
  }
  d_hintStrategy->setHint(decisions);
  Trace("liastar-endgame") << "hint emitted with " << equalities.size()
                           << " equalities" << std::endl;
  return true;
}

void LiaStarExtension::lazyCheckStar(Node literal,
                                     Node lambda,
                                     const std::map<Node, Node>& arithModel)
{
  // Lazy reduction: drive one refinement round for `literal`. Stop refining
  // once the literal has been fully reduced (its term marked processed).
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }

  if (TraceIsOn("liastar-endgame"))
  {
    auto hintIt = d_lastHint.find(literal);
    if (hintIt != d_lastHint.end())
    {
      bool value = false;
      bool assigned =
          d_astate.getValuation().hasSatValue(hintIt->second, value);
      Trace("liastar-endgame")
          << "hint guard: "
          << (assigned ? (value ? "true" : "false") : "unassigned")
          << std::endl;
    }
  }

  // Decoupled endgame: periodically try to finish the search for the star
  // multipliers in a fresh subsolver and feed the witness back as a hint.
  if (tryEndgame(literal, lambda))
  {
    return;
  }

  // If the solver is still committed to the current tentative reduction (the
  // last guard is asserted true in the candidate assignment), optionally skip
  // refinement: the model failed the shortcut only because the star
  // multipliers are not yet integral -- integer branching runs after this
  // check -- and harvesting another cone every round grows the problem under
  // the solver's feet, starving that search. Sound: if the model were fully
  // integral with the guard true, the star would have evaluated to true and
  // the model-value shortcut would have accepted; returning without lemmas
  // defers to integer branching. Refinement resumes as soon as the solver
  // gives the guard up (asserts it false).
  if (options().arith.arithLiaStarPatient)
  {
    auto guardIt = d_lastGuard.find(literal);
    if (guardIt != d_lastGuard.end())
    {
      bool guardValue = false;
      if (d_astate.getValuation().hasSatValue(guardIt->second, guardValue)
          && guardValue)
      {
        return;
      }
    }
  }

  // The persistent incremental subsolver for this lambda. On first use it is
  // seeded with the (nonnegative) predicate.
  Subsolver& sub = getSubsolver(lambda);

  // Refine the subsolver with the cone-disjuncts discovered since the previous
  // round. The disjuncts are stored in bound-variable space, so map them to
  // skolem space first. Two strategies (option arith-liastar-push-pop):
  // - accumulate (default): assert the negation of each new disjunct, one
  //   assertFormula per disjunct, so each disjunct is asserted exactly once
  //   and the subsolver keeps everything it learned about covered regions;
  // - push/pop: the refined formula -- the negated union of every disjunct
  //   found so far -- subsumes the previous round's, so pop the previous
  //   refined formula and assert the new one in a fresh frame: the subsolver
  //   always holds just the base predicate (at the base user level) plus a
  //   single refined formula, keeping the number of live assertions (and the
  //   formulas cached per assertion) constant across rounds.
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& pairs =
      d_lazyCones[lambda];
  if (sub.negated < pairs.size())
  {
    bool pushPop = options().arith.arithLiaStarPushPop;
    for (size_t i = sub.negated; i < pairs.size(); i++)
    {
      Node disjunct = pairs[i].first;
      if (!sub.from.empty())
      {
        disjunct = disjunct.substitute(
            sub.from.begin(), sub.from.end(), sub.to.begin(), sub.to.end());
      }
      if (pushPop)
      {
        sub.covered = sub.covered.isNull()
                          ? disjunct
                          : d_nm->mkNode(Kind::OR, sub.covered, disjunct);
      }
      else
      {
        sub.engine->assertFormula(disjunct.notNode());
      }
    }
    sub.negated = pairs.size();
    if (pushPop)
    {
      if (sub.pushed)
      {
        sub.engine->pop();
      }
      sub.engine->push();
      sub.engine->assertFormula(sub.covered.notNode());
      sub.pushed = true;
    }
  }

  // Optionally bias the cell search toward useful summands: any summand of
  // a nonnegative decomposition of the vector v is bounded componentwise by
  // v, so bound each enumeration skolem by the candidate model's value of
  // the corresponding vector element. The bounds are used as assumptions
  // with an unbiased fallback (see `getDisjunct`), so completeness is
  // unaffected.
  std::vector<Node> bias;
  if (options().arith.arithLiaStarGuided)
  {
    std::vector<Node> keys;
    std::vector<Node> values;
    for (const auto& [key, value] : arithModel)
    {
      keys.push_back(key);
      values.push_back(value);
    }
    size_t k = 0;
    for (size_t i = 0, n = lambda[0].getNumChildren();
         i < n && k < sub.to.size();
         i++)
    {
      if (lambda[0][i].getKind() != Kind::BOUND_VARIABLE)
      {
        continue;
      }
      Node element = literal[i + 1];
      Node value = rewrite(element.substitute(
          keys.begin(), keys.end(), values.begin(), values.end()));
      if (value.isConst() && value.getConst<Rational>().sgn() >= 0)
      {
        bias.push_back(d_nm->mkNode(Kind::LEQ, sub.to[k], value));
      }
      k++;
    }
  }

  lazyHilbert(literal, sub, bias);
}

std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
          std::vector<Node>>
LiaStarExtension::getCones(
    Node n, const std::vector<std::pair<std::vector<std::string>, Node>>& pairs)
{
  // Eager path: build a cone for every DNF disjunct (`pairs`) and accumulate
  // the star constraints over all of them. Returns (cones, starConstraints):
  // the cones (paired with their predicate node) are used to build the
  // membership encoding for the debug trace, and starConstraints is the star
  // encoding that becomes the reduction lemma.
  std::vector<std::pair<Node, Cone<Integer>>> cones;
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;

  for (size_t i = 0; i < pairs.size(); i++)
  {
    const std::pair<std::vector<std::string>, Node>& pair = pairs[i];
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << i << std::endl
                         << pair.second << std::endl;

    Cone<Integer> cone = LiaStarUtils::buildCone(dimension, pair.first);
    if (LiaStarUtils::isEmptyCone(cone))
    {
      // an infeasible disjunct contributes nothing to the star
      Trace("liastar-ext") << "empty cone" << std::endl;
      continue;
    }

    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      // Build the star encoding of this generator over fresh skolems (the
      // constraints are asserted at the top level, not under a quantifier) and
      // accumulate its side constraints and its (point, rays) contribution.
      std::vector<Node> vars, constraints;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone.getHilbertBasis(),
                                     /*star=*/true,
                                     /*useSkolems=*/true,
                                     d_nm,
                                     vars,
                                     constraints,
                                     point,
                                     rays);
      starConstraints.insert(
          starConstraints.end(), constraints.begin(), constraints.end());
      lambdas.push_back({point, rays});
    }
    cones.push_back({pair.second, cone});
  }

  // The star vector equals the sum of every cone's contribution.
  std::vector<Node> sums = buildSumConstraints(d_nm, d_zero, vec, lambdas);
  starConstraints.insert(starConstraints.end(), sums.begin(), sums.end());

  return std::make_pair(cones, starConstraints);
}

void LiaStarExtension::addCone(
    Node n, const std::pair<std::vector<std::string>, Node>& pair)
{
  // Lazy path: build the cone for a single disjunct `pair` and append it to the
  // cones accumulated so far for this lambda (n[0]). An empty (infeasible) cone
  // is dropped.
  size_t dimension = n.getNumChildren() - 1;
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[n[0]];

  Trace("liastar-ext") << "---------------------------" << std::endl;
  Trace("liastar-ext") << "Cone for node " << std::endl
                       << pair.second << std::endl;

  Cone<Integer> cone = LiaStarUtils::buildCone(dimension, pair.first);
  if (LiaStarUtils::isEmptyCone(cone))
  {
    Trace("liastar-ext") << "empty cone" << std::endl;
    return;
  }
  cones.push_back({pair.second, cone});
}

std::vector<Node> LiaStarExtension::getStarConstraints(Node n)
{
  // Lazy path: return the star constraints over all cones accumulated so far in
  // `d_lazyCones[n[0]]`. The per-cone constraints (and their fresh skolems) are
  // computed only once per cone (so the skolems are stable across refinement
  // rounds). Two encodings (option arith-liastar-partial-sums):
  // - default: the per-cone constraints are cached in
  //   `d_starConstraints`/`d_lambdas` and folded into every star formula, and
  //   the sum constraints, which span all cones, are rebuilt on each call --
  //   the formula grows with the number of cones;
  // - partial sums: the per-cone constraints and the running partial-sum
  //   definitions `P_k = P_{k-1} + contribution_k` are accumulated in
  //   `d_partialSumDefs` (emitted as unguarded definitional lemmas by
  //   `processDisjunct`), and the returned star formula is just `v = P_k` --
  //   constant size, however many cones have been found.
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();

  // the cones accumulated so far for this lambda (n[0])
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[n[0]];

  // The per-cone constraints and lambdas computed in previous calls. We only
  // compute new constraints (and fresh skolems) for cones that have not been
  // processed yet, and append them here.
  std::vector<Node>& starConstraints = d_starConstraints[n[0]];
  std::vector<std::pair<Vector, std::vector<Vector>>>& lambdas =
      d_lambdas[n[0]];
  size_t& processed = d_processedCones[n[0]];
  bool partialSums = options().arith.arithLiaStarPartialSums;
  bool newCones = processed < cones.size();
  // the contribution of the newly processed cones to each coordinate
  Vector contribution(dimension, d_zero);

  for (; processed < cones.size(); processed++)
  {
    Cone<Integer>& cone = cones[processed].second;
    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      // Build the generator's star encoding directly over skolems: the star
      // constraints are asserted at the top level (not under a quantifier).
      std::vector<Node> vars, constraints;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone.getHilbertBasis(),
                                     /*star=*/true,
                                     /*useSkolems=*/true,
                                     d_nm,
                                     vars,
                                     constraints,
                                     point,
                                     rays);
      d_starSkolems.insert(vars.begin(), vars.end());
      if (partialSums)
      {
        // The per-cone constraints become definitional lemmas, emitted once;
        // the generator's terms are folded into the running contribution.
        std::vector<Node>& defs = d_partialSumDefs[n[0]];
        defs.insert(defs.end(), constraints.begin(), constraints.end());
        for (size_t i = 0; i < dimension; i++)
        {
          contribution[i] =
              d_nm->mkNode(Kind::ADD, contribution[i], point[i]);
          for (const Vector& ray : rays)
          {
            contribution[i] =
                d_nm->mkNode(Kind::ADD, contribution[i], ray[i]);
          }
        }
      }
      else
      {
        starConstraints.insert(
            starConstraints.end(), constraints.begin(), constraints.end());
        lambdas.push_back({point, rays});
      }
    }
  }

  if (!partialSums)
  {
    // The sum constraints span the lambdas of all cones, so they are rebuilt
    // from the accumulated lambdas on each call. Start from the persisted
    // per-cone constraints and append the freshly built sum constraints,
    // leaving `d_starConstraints` holding only the per-cone constraints.
    std::vector<Node> result = starConstraints;
    std::vector<Node> sums = buildSumConstraints(d_nm, d_zero, vec, lambdas);
    result.insert(result.end(), sums.begin(), sums.end());
    return result;
  }

  // Advance the partial sums by the new cones' contribution: fresh skolems
  // P_k with the definitions P_k[i] = P_{k-1}[i] + contribution[i] (just
  // contribution[i] for the first cones).
  std::vector<Node>& sums = d_partialSums[n[0]];
  if (newCones)
  {
    std::vector<Node>& defs = d_partialSumDefs[n[0]];
    std::vector<Node> next;
    for (size_t i = 0; i < dimension; i++)
    {
      Node p =
          d_nm->mkDummySkolem("liastarPartialSum", d_nm->integerType());
      d_starSkolems.insert(p);
      Node rhs = sums.empty()
                     ? contribution[i]
                     : d_nm->mkNode(Kind::ADD, sums[i], contribution[i]);
      defs.push_back(p.eqNode(rhs));
      next.push_back(p);
    }
    sums = next;
  }

  // The star formula is the constant-size `v = P_k` (`v = 0` while no cone
  // has been discovered: the star of the empty set is the empty sum).
  std::vector<Node> result;
  for (size_t i = 0; i < dimension; i++)
  {
    result.push_back(vec[i].eqNode(sums.empty() ? d_zero : sums[i]));
  }
  return result;
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getMembershipDisjuncts(
    Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones)
{
  // Build the *membership* encoding (used only for the liastar-ext-smt debug
  // trace): one disjunct per (cone, module generator) stating that the vector
  // is a single element `g + sum_k l_k h_k` of that cone, with the multipliers
  // existentially bound. The disjunction over all of these is equivalent to
  // `v in S` (single membership, not the star). Returns each disjunct paired
  // with the predicate node it came from.
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;

  for (auto& pair : cones)
  {
    Node node = pair.first;
    libnormaliz::Cone<Integer>& cone = pair.second;
    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      // Build the generator's membership encoding in terms of bound variables
      // and existentially bind them.
      std::vector<Node> boundVariables, conjunctions;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone.getHilbertBasis(),
                                     /*star=*/false,
                                     /*useSkolems=*/false,
                                     d_nm,
                                     boundVariables,
                                     conjunctions,
                                     point,
                                     rays);

      // the vector equals this single element: vec[i] = point[i] + sum rays
      Vector sums(dimension, d_zero);
      for (size_t i = 0; i < dimension; i++)
      {
        sums[i] = rewrite(d_nm->mkNode(Kind::ADD, sums[i], point[i]));
        for (const auto& ray : rays)
        {
          sums[i] = rewrite(d_nm->mkNode(Kind::ADD, sums[i], ray[i]));
        }
      }

      for (size_t i = 0; i < dimension; i++)
      {
        conjunctions.push_back(vec[i].eqNode(sums[i]));
      }
      Node conjunction = d_nm->mkNode(Kind::AND, conjunctions);
      if (boundVariables.size() > 0)
      {
        Node variables = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVariables);
        conjunction = d_nm->mkNode(Kind::EXISTS, variables, conjunction);
      }
      disjunctions.push_back({node, conjunction});
    }
  }

  return disjunctions;
}

const std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  // Normalize the lambda body `p` to DNF and render each disjunct as a Normaliz
  // constraint matrix (one cone per disjunct). `n` is the lambda
  // (lambda ((x_1 Int) ... (x_n Int)) p).
  Assert(n.getKind() == Kind::LAMBDA);

  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

  traceSmtPreamble(variables);

  Node dnf = LiaStarUtils::toDNF(predicate, &d_env);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      LiaStarUtils::getMatrices(variables, dnf);
  return pairs;
}

LiaStarExtension::MainEnum& LiaStarExtension::getMainEnum(Node lambda)
{
  // Return the main-solver enumeration state for `lambda`, creating it and
  // queueing its seed lemmas on first use. The construction of the base
  // predicate and the skolems mirrors `getSubsolver`.
  auto it = d_mainEnums.find(lambda);
  if (it != d_mainEnums.end())
  {
    return it->second;
  }
  MainEnum& en = d_mainEnums[lambda];

  // The base is the membership predicate (with ites and negations eliminated)
  // conjoined with the non-negativity of the lambda's variables.
  Node base = LiaStarUtils::removeItesAndNots(lambda[1], &d_env);
  std::vector<Node> conjuncts{base};
  for (Node var : lambda[0])
  {
    conjuncts.push_back(d_nm->mkNode(Kind::GEQ, var, d_zero));
  }
  base =
      conjuncts.size() == 1 ? conjuncts[0] : d_nm->mkNode(Kind::AND, conjuncts);

  // The lambda's bound variables appear free in `base`. A lemma with free
  // (bound) variables cannot be sent to the main solver, so we replace them
  // with fresh skolems and remember the mapping so the disjunct built from
  // the model can be substituted back into bound-variable space.
  for (Node var : lambda[0])
  {
    if (var.getKind() == Kind::BOUND_VARIABLE)
    {
      en.from.push_back(var);
      en.to.push_back(d_nm->mkDummySkolem("liastarEnum", var.getType()));
    }
  }
  if (!en.from.empty())
  {
    base = base.substitute(
        en.from.begin(), en.from.end(), en.to.begin(), en.to.end());
  }
  en.base = base;

  // The first stage guard of the enumeration: a decision variable biased to
  // true, like the guard of the tentative reduction in `processDisjunct`.
  // While a cell of the predicate is still uncovered, the solver can satisfy
  // the current stage guard and its model places the skolems in such a cell;
  // once every cell is covered, the guarded lemmas force it false.
  Node g = d_nm->mkDummySkolem("liastarEnumGuard", d_nm->booleanType());
  g = d_astate.getValuation().ensureLiteral(g);
  d_im.preferPhase(g, true);
  en.guard = g;
  en.firstGuard = g;
  en.split = g.orNode(g.notNode());
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerSplit(en.split, g);
  }
  d_im.addPendingLemma(
      en.split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
  // the guarded predicate: guard => base
  Node seed = g.impNode(base);
  en.lemmas.push_back(seed);
  addEnumLemma(seed);
  return en;
}

SolverEngine* LiaStarExtension::getProbe(std::unique_ptr<SolverEngine>& probe,
                                         Node base)
{
  // The probe subsolver for semantic cell generalization: it holds the
  // negation of the base predicate, so a set of cell literals implies the
  // predicate iff checking them as assumptions answers unsat. It is
  // persistent and incremental, so the (large) negated predicate is
  // converted once and the solver's learning amortizes over all probes.
  if (!options().arith.arithLiaStarGeneralizeSemantic)
  {
    return nullptr;
  }
  if (probe == nullptr)
  {
    Options probeOptions;
    probe = std::make_unique<SolverEngine>(d_nm, &probeOptions);
    probe->setIsInternalSubsolver();
    LogicInfo info("QF_LIA");
    probe->setLogic(info);
    probe->setOption("incremental", "true");
    probe->setOption("produce-unsat-assumptions", "true");
    probe->assertFormula(base.notNode());
  }
  return probe.get();
}

void LiaStarExtension::addEnumLemma(Node lemma)
{
  // Queue a main-solver enumeration lemma. A lemma that rewrites to a
  // constant carries no information and is rejected downstream
  // (TheoryInferenceManager asserts lemmas are not constant), so skip it.
  if (rewrite(lemma).isConst())
  {
    return;
  }
  d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_ENUM);
}

Node LiaStarExtension::getModelDisjunct(
    MainEnum& en, const std::map<Node, Node>& arithModel)
{
  // Build one disjunct of the satisfying region by fixing every atom of the
  // base predicate to its truth value in the candidate arithmetic model. This
  // mirrors `LiaStarUtils::getDisjunct`, with the subsolver's getValue
  // replaced by substitution with the main solver's model.
  std::vector<Node> keys;
  std::vector<Node> values;
  for (const auto& [key, value] : arithModel)
  {
    keys.push_back(key);
    values.push_back(value);
  }
  // The enumeration skolems may be missing from the arithmetic model map
  // (e.g. when their atoms were not asserted to the theory this round); fall
  // back to the linear solver's candidate model value for them.
  for (const Node& sk : en.to)
  {
    if (arithModel.find(sk) == arithModel.end())
    {
      // The fallback can produce a non-integral (real-typed) value for an
      // integer skolem (e.g. a delta-rational assignment); substituting it
      // would build ill-typed nodes, so bail out for this round instead.
      Node value = d_arith.getCandidateModelValue(sk);
      if (value.isNull() || !value.isConst()
          || value.getType() != sk.getType())
      {
        return Node();
      }
      keys.push_back(sk);
      values.push_back(value);
    }
  }
  auto evaluate = [&](Node n) {
    return rewrite(
        n.substitute(keys.begin(), keys.end(), values.begin(), values.end()));
  };

  std::vector<Node> atoms;
  std::unordered_set<Node> visited;
  LiaStarUtils::collectAtoms(en.base, atoms, visited);
  std::vector<bool> atomValues;
  for (const Node& atom : atoms)
  {
    Node value = evaluate(atom);
    if (value == d_true)
    {
      atomValues.push_back(true);
    }
    else if (value == d_false)
    {
      atomValues.push_back(false);
    }
    else
    {
      // the atom has no determined value under the candidate model
      return Node();
    }
  }
  // Optionally generalize the cell: drop the atoms the predicate's truth
  // does not depend on, so the cell (and hence its cone) covers more of the
  // predicate per refinement round.
  std::vector<bool> keep(atoms.size(), true);
  if (options().arith.arithLiaStarGeneralize)
  {
    keep = LiaStarUtils::generalizeCell(en.base, atoms, atomValues);
  }
  std::vector<Node> literals;
  for (size_t i = 0; i < atoms.size(); i++)
  {
    if (!keep[i])
    {
      continue;
    }
    const Node& atom = atoms[i];
    Node literal;
    if (atomValues[i])
    {
      // the atom is true in the model: keep it as is
      literal = atom;
    }
    else if (atom.getKind() == Kind::EQUAL && atom[0].getType().isInteger())
    {
      // A disequality is not convex (it is the union of two half-spaces),
      // so it cannot be a single cone. Pick the strict inequality on the
      // side that the model satisfies.
      Node lhs = evaluate(atom[0]);
      Node rhs = evaluate(atom[1]);
      if (!lhs.isConst() || !rhs.isConst())
      {
        return Node();
      }
      Kind k = lhs.getConst<Rational>() > rhs.getConst<Rational>()
                   ? Kind::GT
                   : Kind::LT;
      literal = d_nm->mkNode(k, atom[0], atom[1]);
    }
    else
    {
      // the atom is false in the model: negate it
      literal = atom.notNode();
    }
    literals.push_back(literal);
  }
  // Optionally generalize the cell semantically, with the probe holding the
  // negated base predicate (same skolem space as the literals here).
  SolverEngine* probe = getProbe(en.probe, en.base);
  if (probe != nullptr)
  {
    LiaStarUtils::semanticGeneralize(probe, literals);
  }
  if (literals.empty())
  {
    return d_true;
  }
  Node disjunct =
      literals.size() == 1 ? literals[0] : d_nm->mkNode(Kind::AND, literals);
  if (!en.from.empty())
  {
    // substitute the fresh skolems back to the lambda's bound variables.
    disjunct = disjunct.substitute(
        en.to.begin(), en.to.end(), en.from.begin(), en.from.end());
  }
  return disjunct;
}

void LiaStarExtension::advanceStage(MainEnum& en, Node skolemDisjunct)
{
  // Open a new enumeration stage: a fresh guard that activates the previous
  // stage's constraints plus the negation of the newly covered cell, so the
  // current guard always activates `base and not(D_1) ... and not(D_k)` with
  // two constant-size lemmas per stage.
  Node g = d_nm->mkDummySkolem("liastarEnumGuard", d_nm->booleanType());
  g = d_astate.getValuation().ensureLiteral(g);
  d_im.preferPhase(g, true);
  Node prev = g.impNode(en.guard);
  Node negation = g.impNode(skolemDisjunct.notNode());
  en.lemmas.push_back(prev);
  en.lemmas.push_back(negation);
  addEnumLemma(prev);
  addEnumLemma(negation);
  en.guard = g;
}

void LiaStarExtension::emitDriverLemma(Node literal, MainEnum& en)
{
  // Emit, once per (literal, stage), the driver lemma
  //     literal => (p[v] or star or guard).
  // If the literal is asserted but the model certifies it neither via p[v]
  // nor via the star under-approximation, the driver forces the stage guard,
  // which places the enumeration skolems in a cell not covered by any cone --
  // the next round then reads that cell off the model. Once every cell is
  // covered the guard branch closes by conflict and only the certified
  // branches remain (with `star` then exact). The lemma is satisfiability
  // preserving: in any model where v is a *non-empty* sum outside the
  // discovered approximation, some cell of the predicate is still uncovered,
  // and the model extends to one placing the (fresh) skolems in it. The
  // empty sum (v = 0) is always in the star set but is covered by no cell,
  // so the star branch must always include it: before any cone is discovered
  // (`d_lastStarLia` has no entry yet) the branch is `v = 0` itself, and the
  // star built over any non-empty set of cones admits it by setting every
  // multiplier to zero.
  Node star;
  auto starIt = d_lastStarLia.find(literal);
  if (starIt != d_lastStarLia.end())
  {
    star = starIt->second;
  }
  else
  {
    std::vector<Node> zeros;
    for (size_t i = 1, n = literal.getNumChildren(); i < n; i++)
    {
      zeros.push_back(literal[i].eqNode(d_zero));
    }
    star = zeros.size() == 1 ? zeros[0] : d_nm->mkNode(Kind::AND, zeros);
  }
  Node pv = LiaStarUtils::getVectorPredicate(literal, d_nm).first;
  Node lemma =
      literal.impNode(d_nm->mkNode(Kind::OR, {pv, star, en.guard}));
  // The inference manager caches sent lemmas per user context, so re-queueing
  // the same driver is dropped for free (and re-sent after a user pop).
  addEnumLemma(lemma);
}

void LiaStarExtension::mainSolverCheckStar(
    Node literal, Node lambda, const std::map<Node, Node>& arithModel)
{
  // Main-solver lazy reduction: drive one refinement round for `literal`,
  // enumerating the predicate's cells in the main solver instead of a
  // dedicated subsolver. Stop refining once the literal has been fully
  // reduced.
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }

  bool seeded = d_mainEnums.find(lambda) != d_mainEnums.end();
  MainEnum& en = getMainEnum(lambda);

  // Catch up: open one stage per cone-disjunct discovered since the previous
  // round (e.g. through another literal with the same lambda). The disjuncts
  // are stored in bound-variable space, so map them to skolem space first.
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& pairs =
      d_lazyCones[lambda];
  for (size_t i = en.negated; i < pairs.size(); i++)
  {
    Node disjunct = pairs[i].first;
    if (!en.from.empty())
    {
      disjunct = disjunct.substitute(
          en.from.begin(), en.from.end(), en.to.begin(), en.to.end());
    }
    advanceStage(en, disjunct);
  }
  en.negated = pairs.size();

  if (!seeded)
  {
    // First round: the seed lemmas were only queued just now, so there is no
    // assignment of the guard or the skolems to read yet. The driver lemma
    // makes an unjustified literal activate the enumeration.
    emitDriverLemma(literal, en);
    d_im.doPendingLemmas();
    return;
  }

  // Keep the enumeration lemmas alive across user pops: re-queue them all;
  // within one user context the lemma cache drops the duplicates, and after
  // a pop (which retracts the lemmas but not this non-context state) they
  // are re-sent.
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerSplit(en.split, en.firstGuard);
  }
  d_im.addPendingLemma(
      en.split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
  for (const Node& lemma : en.lemmas)
  {
    addEnumLemma(lemma);
  }

  Valuation& val = d_astate.getValuation();
  bool guardValue = false;
  bool assigned = val.isSatLiteral(en.guard)
                  && val.hasSatValue(en.guard, guardValue);
  if (assigned && !guardValue && val.isFixed(en.guard))
  {
    // The negated stage guard is implied by the input assertions: the
    // predicate conjoined with the negated disjuncts is unsatisfiable, so
    // every cell of the predicate is covered by a cone and the encoding is
    // exact (this is the analogue of the subsolver answering unsat).
    processDisjunct(literal, d_false, /*complete=*/true);
    return;
  }
  if (!assigned || !guardValue)
  {
    // No cell can be read this round. (Re-)emit the driver for the current
    // stage: a model claiming the literal without certifying it cannot then
    // be accepted, since the driver forces the stage guard in any such
    // model, and the model-value shortcut in checkFullEffort accepts the
    // certified ones.
    emitDriverLemma(literal, en);
    d_im.doPendingLemmas();
    return;
  }

  // The stage guard is true: the skolems lie in a region of the predicate
  // not covered by any cone. Read off the cell containing them.
  Node disjunct = getModelDisjunct(en, arithModel);
  Trace("liastar-ext") << "main-solver disjunct: " << disjunct << std::endl;
  if (disjunct.isNull())
  {
    // some atom had no model value; try again next round
    emitDriverLemma(literal, en);
    d_im.doPendingLemmas();
    return;
  }
  // Normalize the cell like `processDisjunct` stores it in `d_lazyCones`
  // (negations folded into positive comparisons), so the re-harvest check
  // below compares like with like.
  disjunct = LiaStarUtils::removeItesAndNots(disjunct, &d_env);
  // Guard against re-harvesting a known cell (its negation lemma may not
  // have reached the solver before this model was produced).
  for (const auto& pair : pairs)
  {
    if (pair.first == disjunct)
    {
      emitDriverLemma(literal, en);
      d_im.doPendingLemmas();
      return;
    }
  }
  // Open the stage that excludes the new cell, so the continuing search
  // moves the skolems to another cell.
  Node skolemDisjunct = disjunct;
  if (!en.from.empty())
  {
    skolemDisjunct = skolemDisjunct.substitute(
        en.from.begin(), en.from.end(), en.to.begin(), en.to.end());
  }
  advanceStage(en, skolemDisjunct);
  // Turn the cell into a cone and emit the (tentative) reduction lemma.
  // `processDisjunct` appends the cone to `d_lazyCones[lambda]`, which the
  // stage above has already negated, and updates the star
  // under-approximation that the new driver lemma references.
  processDisjunct(literal, disjunct, /*complete=*/false);
  en.negated = pairs.size();
  emitDriverLemma(literal, en);
  d_im.doPendingLemmas();
}

void LiaStarExtension::lazyHilbert(Node literal,
                                   Subsolver& sub,
                                   const std::vector<Node>& bias)
{
  // One lazy refinement round for `literal`. Ask the subsolver for a model in a
  // region of p not yet covered by a cone, read off the convex cell containing
  // it, and hand it to `processDisjunct` for the cone and lemma generation.
  Node variables = literal[0][0];
  Trace("liastar-lazy") << "lazyHilbert::variables:" << variables << std::endl;

  traceSmtPreamble(variables);

  // Check the subsolver and read off the disjunct (the cell of the predicate)
  // containing the model. The subsolver already has the predicate and the
  // negations of all previously discovered cone-disjuncts asserted, so the
  // model lies in a region of the predicate not yet covered by any cone.
  Node disjunct = LiaStarUtils::getDisjunct(sub.base,
                                            sub.from,
                                            sub.to,
                                            &d_env,
                                            sub.engine.get(),
                                            getProbe(sub.probe, sub.base),
                                            bias);
  // `getDisjunct` returns false when no region of `formula` is left uncovered,
  // i.e. every disjunct of the predicate already has a cone. At that point the
  // cone encoding is exact and we can assert the full equivalence.
  bool complete = disjunct == d_false;
  processDisjunct(literal, disjunct, complete);
}

void LiaStarExtension::processDisjunct(Node literal,
                                       Node disjunct,
                                       bool complete)
{
  // Shared tail of one lazy refinement round: turn the freshly discovered
  // disjunct (a cell of the predicate, in bound-variable space) into a cone,
  // rebuild the star constraints over all cones found so far, and emit a
  // (tentative or final) reduction lemma.
  Node variables = literal[0][0];
  // The disjunct is a conjunction of arithmetic facts in the solver's normal
  // form, which can represent strict inequalities as negations (e.g.
  // (not (>= a b))). Normalize away the negations before building the matrix.
  disjunct = LiaStarUtils::removeItesAndNots(disjunct, &d_env);

  Trace("liastar-ext") << "disjunct: " << disjunct << std::endl;

  std::pair<std::vector<std::string>, Node> pair =
      LiaStarUtils::getMatrix(variables, disjunct);

  // Add the cone for the current disjunct to `d_lazyCones` and get the starLia
  // constraints over the whole list of cones so far. `getStarConstraints` only
  // computes the per-cone constraints (and fresh skolems) for cones not yet
  // processed, reusing the constraints computed in previous calls. When
  // `complete`, `disjunct` is the (infeasible) false constraint, so `addCone`
  // adds no new cone and `getStarConstraints` just rebuilds the sum constraints
  // over the cones found so far.
  addCone(literal, pair);
  std::vector<Node> starConstraints = getStarConstraints(literal);
  Trace("liastar-ext") << "starConstraints: " << std::endl
                       << toString(starConstraints) << std::endl;

  if (options().arith.arithLiaStarPartialSums)
  {
    // Queue the definitional lemmas (per-cone multiplier constraints and
    // partial-sum definitions) accumulated by `getStarConstraints`. They are
    // unguarded: they only constrain fresh skolems and are satisfiable by
    // setting every multiplier to zero. All of them are re-queued each
    // round: within one user context the lemma cache drops the duplicates,
    // and after a user pop they are re-sent, so the star formulas emitted
    // below never reference undefined partial-sum skolems.
    for (const Node& def : d_partialSumDefs[literal[0]])
    {
      if (!rewrite(def).isConst())
      {
        d_im.addPendingLemma(def, InferenceId::ARITH_LIA_STAR_DEFINITION);
      }
    }
  }

  Node star = d_nm->mkNode(Kind::AND, starConstraints);

  if (options().arith.arithLiaStarPatient)
  {
    // Commit the search to the tentative reduction: bias every star conjunct
    // to true, in addition to the guard below. Without this, the fresh sum
    // equalities get default phases, some are assigned false before the
    // guard is ever decided, the guard is propagated false through the
    // equivalence, and the solver never actually explores the star
    // assignment (so the patient gate in lazyCheckStar never fires).
    for (const Node& constraint : starConstraints)
    {
      if (!rewrite(constraint).isConst())
      {
        d_im.preferPhase(constraint, true);
      }
    }
  }

  Trace("liastar-ext") << d_lazyCones[literal[0]].size()
                       << " cones for lambda:  " << literal[0] << std::endl;

  star = rewrite(star);
  // Remember the last computed starLia under-approximation for `literal`; the
  // model-value check in checkFullEffort uses it to skip refinement when the
  // current model already satisfies it.
  d_lastStarLia[literal] = star;

  // Deactivate the guard from the previous refinement round for this literal:
  // its under-approximation is a subset of the current `star`, so the tentative
  // equivalence it guarded is subsumed. Asserting `(not g_old)` makes that
  // guarded lemma vacuous, so the solver does not have to satisfy several
  // (mutually constraining) guarded equivalences at once. Sound because `g_old`
  // is fresh.
  auto guardIt = d_lastGuard.find(literal);
  if (guardIt != d_lastGuard.end())
  {
    Node deactivate = guardIt->second.notNode();
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerGuardDeactivate(deactivate);
    }
    d_im.addPendingLemma(
        deactivate, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
    d_lastGuard.erase(guardIt);
  }

  Node lemma;
  if (complete)
  {
    // The encoding is complete, so `star` captures the star set exactly and the
    // full equivalence holds. This is what allows refuting a (positively
    // asserted) star-contains.
    lemma = literal.eqNode(star);
  }
  else
  {
    // While cones are still being discovered, `star` is an under-approximation
    // of the star set, so the equivalence `literal = star` is not yet sound. We
    // assert it only tentatively, implied by a fresh boolean guard `g`. The
    // split makes `g` a genuine decision literal and `preferPhase` biases it to
    // true, so the SAT solver tries the equivalence first. If assuming it leads
    // to a conflict (the literal actually holds via a not-yet-discovered cone),
    // the solver flips `g` to false, retracting the equivalence, and we refine.
    Node g = d_nm->mkDummySkolem("liastarGuard", d_nm->booleanType());
    g = d_astate.getValuation().ensureLiteral(g);
    d_im.preferPhase(g, true);
    Node split = g.orNode(g.notNode());
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerSplit(split, g);
    }
    d_im.addPendingLemma(
        split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());
    lemma = g.impNode(literal.eqNode(star));
    // Remember this guard so it can be deactivated once a later, larger
    // under-approximation subsumes it.
    d_lastGuard[literal] = g;
  }
  Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerContainsReduce(lemma, literal, star);
  }
  d_im.addPendingLemma(
      lemma, InferenceId::ARITH_LIA_STAR_EXISTS, d_proofGen.get());
  // Keep refining (do not mark the term processed) until every disjunct of the
  // predicate has been covered by a cone.
  if (complete)
  {
    d_processedStarTerms.push_back(literal);
  }
  d_im.doPendingLemmas();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */

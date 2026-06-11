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

#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/theory_arith.h"
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
    if (lit.getKind() == Kind::STAR_CONTAINS)
    {
      // positive polarity of star-contains
      assertions.push_back(lit);
    }
    if (lit.getKind() == Kind::NOT && lit[0].getKind() == Kind::STAR_CONTAINS)
    {
      // negative polarity of star-contains
      assertions.push_back(lit[0]);
    }
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
      lazyCheckStar(literal, lambda);
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

void LiaStarExtension::lazyCheckStar(Node literal, Node lambda)
{
  // Lazy reduction: drive one refinement round for `literal`. Stop refining
  // once the literal has been fully reduced (its term marked processed).
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }

  // The persistent incremental subsolver for this lambda. On first use it is
  // seeded with the (nonnegative) predicate.
  Subsolver& sub = getSubsolver(lambda);

  // Refine the subsolver with the cone-disjuncts discovered since the previous
  // round. The refined formula -- the negated union of every disjunct found so
  // far -- subsumes the previous round's, so instead of accumulating one
  // assertion per disjunct we pop the previous refined formula and assert the
  // new one in a fresh frame: the subsolver always holds just the base
  // predicate (at the base user level) plus a single refined formula. The
  // disjuncts are stored in bound-variable space, so map them to skolem space
  // first.
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& pairs =
      d_lazyCones[lambda];
  if (sub.negated < pairs.size())
  {
    for (size_t i = sub.negated; i < pairs.size(); i++)
    {
      Node disjunct = pairs[i].first;
      if (!sub.from.empty())
      {
        disjunct = disjunct.substitute(
            sub.from.begin(), sub.from.end(), sub.to.begin(), sub.to.end());
      }
      sub.covered = sub.covered.isNull()
                        ? disjunct
                        : d_nm->mkNode(Kind::OR, sub.covered, disjunct);
    }
    sub.negated = pairs.size();
    if (sub.pushed)
    {
      sub.engine->pop();
    }
    sub.engine->push();
    sub.engine->assertFormula(sub.covered.notNode());
    sub.pushed = true;
  }

  lazyHilbert(literal, sub);
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
  // computed only once per cone and cached in `d_starConstraints`/`d_lambdas`
  // (so the skolems are stable across refinement rounds); only the sum
  // constraints, which span all cones, are rebuilt on each call.
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
      starConstraints.insert(
          starConstraints.end(), constraints.begin(), constraints.end());
      lambdas.push_back({point, rays});
    }
  }

  // The sum constraints span the lambdas of all cones, so they are rebuilt from
  // the accumulated lambdas on each call. Start from the persisted per-cone
  // constraints and append the freshly built sum constraints, leaving
  // `d_starConstraints` holding only the per-cone constraints.
  std::vector<Node> result = starConstraints;
  std::vector<Node> sums = buildSumConstraints(d_nm, d_zero, vec, lambdas);
  result.insert(result.end(), sums.begin(), sums.end());

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

void LiaStarExtension::lazyHilbert(Node literal, Subsolver& sub)
{
  // One lazy refinement round for `literal`. Ask the subsolver for a model in a
  // region of p not yet covered by a cone, read off the convex cell containing
  // it, turn it into a cone, and emit a (tentative or final) reduction lemma.
  Node variables = literal[0][0];
  Trace("liastar-lazy") << "lazyHilbert::variables:" << variables << std::endl;

  traceSmtPreamble(variables);

  // Check the subsolver and read off the disjunct (the cell of the predicate)
  // containing the model. The subsolver already has the predicate and the
  // negations of all previously discovered cone-disjuncts asserted, so the
  // model lies in a region of the predicate not yet covered by any cone.
  Node disjunct = LiaStarUtils::getDisjunct(
      sub.base, sub.from, sub.to, &d_env, sub.engine.get());
  // `getDisjunct` returns false when no region of `formula` is left uncovered,
  // i.e. every disjunct of the predicate already has a cone. At that point the
  // cone encoding is exact and we can assert the full equivalence.
  bool complete = disjunct == d_false;
  // The disjunct is a conjunction of arithmetic facts in the subsolver's
  // normal form, which can represent strict inequalities as negations (e.g.
  // (not (>= a b))). Normalize away the negations before building the matrix.
  disjunct = LiaStarUtils::removeItesAndNots(disjunct, &d_env);

  Trace("liastar-ext") << "disjunct: " << disjunct << std::endl;

  std::pair<std::vector<std::string>, Node> pair =
      LiaStarUtils::getMatrix(variables, disjunct);

  Trace("liastar-ext") << "disjunct: " << disjunct << std::endl;

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

  Node star = d_nm->mkNode(Kind::AND, starConstraints);

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

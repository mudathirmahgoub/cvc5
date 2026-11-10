/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Extension to the theory of arithmetic handling lia star operator.
 */

#include "liastar_extension.h"

#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/evaluator.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/** Print the elements of l separated by spaces, for traces. */
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

LiaStarExtension::LiaStarExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_nm(nodeManager()),
      d_arith(containing),
      d_im(containing.getInferenceManager()),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasAssertions(context(), false),
      d_negatedReductions(userContext()),
      d_negatedReductionsSent(userContext()),
      d_stats(statisticsRegistry())
{
  d_extTheory.addFunctionKind(Kind::STAR_CONTAINS);
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
}

LiaStarExtension::~LiaStarExtension() {}

void LiaStarExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-dependent simplification. n is, e.g.,
  // (int.star-contains (lambda ((x Int)) (= x 2)) a).
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_extTheory.registerTerm(n);
  }
}

bool LiaStarExtension::collectModelValues(TheoryModel* m)
{
  std::vector<Node> assertions;
  getAssertions(assertions);
  for (const Node& lit : assertions)
  {
    bool polarity = lit.getKind() != Kind::NOT;
    Node atom = polarity ? lit : lit[0];
    if (!m->assertPredicate(atom, polarity))
    {
      return false;
    }
  }
  return true;
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("liastar-ext") << "Getting assertions..." << std::endl;
  Trace("liastar-ext") << "---------------------" << std::endl;
  // of the facts L, (>= b 2) and (not (= b 1)), for L of checkFullEffort,
  // only the first is collected
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-ext") << lit << std::endl;
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    if (atom.getKind() == Kind::STAR_CONTAINS)
    {
      assertions.push_back(lit);
    }
  }
  Trace("liastar-ext") << "---------------------" << std::endl;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  Assert(hasAssertions());
  d_stats.d_checkFullEffortTime.start();
  // The steps 1-4 below are those documented in liastar_extension.h. The
  // examples follow the literal of the class documentation
  //   L = (int.star-contains (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
  //                          a b)
  // of S = {(x, y) | x >= 2 and y = 1}, asserted together with (>= b 2).
  // The first call sends the split of step 2, the second, with arithModel
  // {a -> 2, b -> 2}, the reduction lemma of step 4, and later calls find
  // that L was reduced already.
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  ++d_stats.d_checkRuns;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);
  d_stats.d_starContainsLiterals += assertions.size();

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    // literal is L, or (not L) for a negative literal, and atom is L
    bool polarity = literal.getKind() != Kind::NOT;
    Node atom = polarity ? literal : literal[0];
    Assert(atom.getKind() == Kind::STAR_CONTAINS);
    // The first child is the lambda, unless the rewriter normalized a
    // constant lambda to a function array constant, or --no-uf-lazy-ll lifted
    // it to a skolem. getDefinition recovers the lambda in all three cases.
    Node lambda = uf::FunctionConst::getDefinition(atom[0]);
    Assert(!lambda.isNull())
        << "Expected a lambda as the first child of " << atom << std::endl;
    // vectorPredicate is p(y) = (and (>= a 2) (= b 1)), and nonnegative is
    // (and (and true (>= a 0)) (>= b 0))
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(atom, nm);

    // 1. y is nonnegative
    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      // assert that vector elements are non negative. The nonnegativity
      // only holds under the originating star-contains literal, so guard
      // the lemma with it: an unguarded lemma would be treated as valid
      // by the SAT solver, corrupting unsat cores and other contexts
      // where the literal does not hold.
      //   (=> L (and (and true (>= a 0)) (>= b 0)))
      // The lemma is an assumption rather than a valid fact, so like the
      // split and the reduction below it needs justification (see
      // RelevanceManager): the model must satisfy it.
      Node lemma = atom.impNode(nonnegative);
      d_im.addPendingLemma(lemma,
                           InferenceId::ARITH_LIA_STAR_NONNEGATIVE,
                           nullptr,
                           false,
                           LemmaProperty::NEEDS_JUSTIFY);
    }
    // 2. split on p(y):
    //   (or (and (>= a 2) (= b 1)) (not (and (>= a 2) (= b 1))))
    // The lemma cache holds rewritten lemmas, and the rewriter keeps
    // (or p(y) (not p(y))) as is, so the split is sent once per user
    // context. It only rewrites to the cached true when p(y) is a constant,
    // e.g. for a constant y, which leaves nothing to split.
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    // The asserted side of the split certifies step 3 below, which skips a
    // literal whose p(y) holds in the model, so the split needs justification
    // (see RelevanceManager): relevance filtering, e.g. --nl-rlv, must keep
    // p(y) in the nonlinear model check, or the model repair could change a
    // nonlinear coordinate of y after the literal was skipped.
    d_im.addPendingLemma(split,
                         InferenceId::ARITH_LIA_STAR_SPLIT,
                         nullptr,
                         false,
                         LemmaProperty::NEEDS_JUSTIFY);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    // 3. skip a positive literal if p(y) holds in the model, since then y is
    // in S*. A negative literal is then false, which step 4 refutes. The
    // model {a -> 2, b -> 2} gives (and (>= 2 2) (= 2 1)), which rewrites to
    // false, so L goes on to step 4. The model {a -> 3, b -> 1} would give
    // true, since (3, 1) is in S.
    if (polarity && options().arith.arithLiaStarModelValue)
    {
      d_stats.d_modelValueTime.start();
      ++d_stats.d_modelValueChecks;
      std::vector<Node> keys;
      std::vector<Node> values;

      for (const auto& [key, value] : arithModel)
      {
        keys.push_back(key);
        values.push_back(value);
      }

      Node value = vectorPredicate.substitute(
          keys.begin(), keys.end(), values.begin(), values.end());
      value = rewrite(value);

      Trace("liastar-ext-debug") << "value: " << value << std::endl;

      if (value == d_true)
      {
        ++d_stats.d_modelValueSolved;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        Trace("liastar-ext-debug")
            << atom << " is satisfied in the current model" << std::endl;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        d_stats.d_modelValueTime.stop();
        continue;
      }
      d_stats.d_modelValueTime.stop();
    }

    // 4. the reduction lemmas, each sent once per atom. An atom is in
    // d_negatedReductions once its lemma (= L ...) was sent, as in the
    // calls after the second. Its negative literal may still need the lemma
    // (or L (forall ...)), e.g. if L was asserted positively before.
    if (d_negatedReductions.find(atom) != d_negatedReductions.end())
    {
      if (!polarity && d_negatedReductionsSent.insert(atom))
      {
        sendNegatedReduction(atom);
        d_im.doPendingLemmas();
      }
      continue;
    }
    // one pair per disjunct of p, here the single pair of
    // {x - 2 >= 0, y - 1 = 0} and (and (>= x 2) (= y 1))
    std::vector<std::pair<LinearConstraints, Node>> pairs =
        convertQFLIAToMatrices(lambda);

    // IntegerPolyhedron finds the module generator (2 1) and the Hilbert
    // basis {(1 0)} for the disjunct, so cones has its one cone, skolems
    // becomes {mu, l} and starConstraints
    //   (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
    //   (= a (+ (+ 0 (* 2 mu)) (* 1 l))) (= b (+ (+ 0 (* 1 mu)) (* 0 l)))
    std::vector<Node> skolems;
    auto [cones, starConstraints] = getCones(atom, pairs, skolems);

    Trace("liastar-ext") << "lia constraint: " << std::endl;
    // print SMT-LIB queries comparing each linear set with its disjunct
    // (equivalent when the disjunct has one module generator) and p with the
    // union of all linear sets, see LiaStarUtils::traceEquivalenceCheck. Here
    // lia has the single pair of (and (>= x 2) (= y 1)) and
    //   (exists ((l1 Int)) (and (>= l1 0) (= x (+ 2 l1)) (= y 1)))
    if (TraceIsOn("liastar-ext-smt"))
    {
      std::vector<std::pair<Node, Node>> lia = getLia(lambda, cones);
      for (size_t i = 0; i < lia.size(); i++)
      {
        LiaStarUtils::traceEquivalenceCheck(
            std::to_string(i).c_str(), lia[i].first, lia[i].second);
      }
      std::vector<Node> disjunctions;
      std::transform(lia.begin(),
                     lia.end(),
                     std::back_inserter(disjunctions),
                     [](auto& p) { return p.second; });
      Node liaFormula;
      if (disjunctions.size() == 0)
      {
        liaFormula = d_false;
      }
      else if (disjunctions.size() == 1)
      {
        liaFormula = disjunctions[0];
      }
      else
      {
        liaFormula = d_nm->mkNode(Kind::OR, disjunctions);
      }
      LiaStarUtils::traceEquivalenceCheck("lia formula", lambda[1], liaFormula);
    }
    // starConstraints has a single element if S is empty and n is 1, e.g.
    // (= a 0) for (lambda ((x Int)) false), whose star S* is {0}. Here star
    // rewrites to
    //   (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
    //        (= a (+ (* 2 mu) l)) (= b mu))
    // and the lemma is (= L star)
    Node star = d_nm->mkAnd(starConstraints);
    Trace("liastar-ext") << "starConstraints: " << std::endl
                         << toString(starConstraints) << std::endl;
    star = rewrite(star);
    Node lemma = atom.eqNode(star);
    Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
    // With skolems the lemma skolemizes (= L (exists ((mu Int) (l Int)) star)),
    // so like other skolemization lemmas it needs justification (see
    // RelevanceManager): a model that makes L true must satisfy the
    // constraints on mu and l. Without skolems the lemma is exact, e.g.
    // (= L (= a 0)) for (lambda ((x Int)) false), but star is still the only
    // constraint that keeps y in S*, and L itself is not an arithmetic
    // constraint. So the lemma needs justification in both cases: otherwise
    // relevance filtering, e.g. --nl-rlv, could drop star and let the
    // nonlinear model repair move y out of S*.
    d_im.addPendingLemma(lemma,
                         InferenceId::ARITH_LIA_STAR_EXISTS,
                         nullptr,
                         false,
                         LemmaProperty::NEEDS_JUSTIFY);
    ++d_stats.d_starTermsReduced;
    // the lemma for a negated atom, see the class documentation. Without
    // skolems the lemma above is exact and it is not needed, e.g.
    // (= L (= a 0)) for (lambda ((x Int)) false). Here negation is star
    // negated, with bound variables u and v for mu and l:
    //   (forall ((u Int) (v Int))
    //     (not (and (>= u 0) (>= v 0) (=> (= u 0) (= v 0))
    //               (= a (+ (* 2 u) v)) (= b u))))
    Node negation;
    if (!skolems.empty())
    {
      std::vector<Node> boundVars;
      for (const Node& skolem : skolems)
      {
        boundVars.push_back(NodeManager::mkBoundVar(skolem.getType()));
      }
      Node notStar = star.notNode();
      Node body = notStar.substitute(
          skolems.begin(), skolems.end(), boundVars.begin(), boundVars.end());
      Node boundVarList = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVars);
      negation = d_nm->mkNode(Kind::FORALL, boundVarList, body);
    }
    d_negatedReductions.insert(atom, negation);
    if (!polarity)
    {
      d_negatedReductionsSent.insert(atom);
      sendNegatedReduction(atom);
    }
    d_im.doPendingLemmas();
  }
  d_stats.d_checkFullEffortTime.stop();
}

void LiaStarExtension::sendNegatedReduction(Node atom)
{
  Node negation = d_negatedReductions.find(atom)->second;
  if (negation.isNull())
  {
    return;
  }
  if (!logicInfo().isQuantified())
  {
    std::stringstream ss;
    ss << "A negated int.star-contains requires quantifiers in the background "
          "logic, found "
       << atom.notNode();
    throw LogicException(ss.str());
  }
  // (or L (forall ((u Int) (v Int)) (not (and (>= u 0) ...)))), see
  // checkFullEffort
  Node lemma = atom.orNode(negation);
  Trace("liastar-ext") << "negated star lemma: " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_NOT_EXISTS, nullptr);
}

std::pair<std::vector<std::pair<Node, IntegerPolyhedron>>, std::vector<Node>>
LiaStarExtension::getCones(
    Node n,
    const std::vector<std::pair<LinearConstraints, Node>>& pairs,
    std::vector<Node>& skolems)
{
  d_stats.d_getConesTime.start();
  // The examples follow n = L of checkFullEffort, for the lambda
  // (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1))).
  std::vector<std::pair<Node, IntegerPolyhedron>> cones;
  // the vector y = (a b), so dimension is 2 and zeroVector is (0 0)
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  d_stats.d_dimensionMax.maxAssign(dimension);
  IntegerVector zeroVector = IntegerVectorUtils::zero(dimension);
  // one pair per linear set: its module generator times mu, and each vector
  // of its Hilbert basis times its l, here the single pair of
  //   ((* 2 mu) (* 1 mu)) and {((* 1 l) (* 0 l))}
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;
  const bool assumeNonnegative = options().arith.arithLiaStarAssumeNonnegative;

  for (size_t i = 0; i < pairs.size(); i++)
  {
    // the constraints of a disjunct and the disjunct, here
    // {x - 2 >= 0, y - 1 = 0} and (and (>= x 2) (= y 1))
    LinearConstraints constraints = pairs[i].first;
    Node disjunct = pairs[i].second;
    if (assumeNonnegative)
    {
      constraints.addNonnegativity();
    }
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << i << std::endl
                         << disjunct << std::endl;
    Trace("liastar-ext") << "constraints: " << constraints.toString()
                         << std::endl;
    ++d_stats.d_hilbertBasisCalls;
    d_stats.d_hilbertBasisTime.start();
    IntegerPolyhedron polyhedron(constraints);
    d_stats.d_hilbertBasisTime.stop();
    d_stats.d_hilbertBasisSums += polyhedron.getNumSums();
    Trace("liastar-ext") << polyhedron.toString() << std::endl;

    // A polyhedron has integer points exactly when it has module generators,
    // e.g. the polyhedron of (and (= x (* 2 z)) (= x (+ (* 2 w) 1))) has
    // rational points but no integer points. The disjunct false is skipped
    // here too.
    if (polyhedron.isEmpty())
    {
      // the polyhedron has no integer points, skip it
      Trace("liastar-ext") << "empty cone" << std::endl;
      ++d_stats.d_conesEmpty;
      continue;
    }
    ++d_stats.d_conesNonempty;
    // the Hilbert basis comes first and takes nonnegative multipliers, the
    // maximal subspace follows and takes sign-unrestricted ones, see
    // IntegerPolyhedron::getRecessionMonoidGenerators. For
    // (and (>= x 2) (= y 1)) this is {(1 0)} with numPointed 1. For
    // (= (+ x y) 2), whose integer points are (1, 1) + (1, -1)*Z, it is
    // {(1 -1)} with numPointed 0.
    size_t numPointed = polyhedron.getHilbertBasis().size();
    const std::vector<IntegerVector> hilbertBasis =
        polyhedron.getRecessionMonoidGenerators();
    // here {(2 1)}. A cone has the single module generator 0, e.g.
    // (and (>= x y) (>= y 0)), whose Hilbert basis is {(1 0), (1 1)}.
    const std::vector<IntegerVector>& generators =
        polyhedron.getModuleGenerators();
    d_stats.d_hilbertBasisTotal += hilbertBasis.size();
    d_stats.d_hilbertBasisMax.maxAssign(hilbertBasis.size());
    d_stats.d_moduleGeneratorsTotal += generators.size();
    d_stats.d_moduleGeneratorsMax.maxAssign(generators.size());

    for (const IntegerVector& generator : generators)
    {
      // the star of 0 + H*N + M*Z is itself, so mu is 1 for the zero
      // generator, and a fresh skolem mu otherwise, e.g. for (2 1)
      Node mu = d_one;
      if (generator != zeroVector)
      {
        mu = d_nm->mkDummySkolem("mu", d_nm->integerType());
        skolems.push_back(mu);
      }

      // (>= mu 0), which rewrites to true for mu = 1
      starConstraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
      // the generator times mu: ((* 2 mu) (* 1 mu)) for (2 1)
      Vector point;
      for (const Integer& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        Node monomial = d_nm->mkNode(Kind::MULT, constant, mu);
        point.push_back(monomial);
      }
      std::vector<Vector> rays;
      for (size_t j = 0; j < hilbertBasis.size(); j++)
      {
        const IntegerVector& basis = hilbertBasis[j];
        // the multiplier l of basis, e.g. of (1 0)
        Node lambda = d_nm->mkDummySkolem("l", d_nm->integerType());
        skolems.push_back(lambda);
        if (j < numPointed)
        {
          // (>= l 0), except for a direction of the maximal subspace, which
          // has any sign, e.g. (1 -1) for (= (+ x y) 2)
          starConstraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }
        // (=> (= mu 0) (= l 0)), the rays of a linear set may only be used
        // together with its generator
        starConstraints.push_back(
            d_nm->mkNode(Kind::EQUAL, mu, d_zero)
                .impNode(d_nm->mkNode(Kind::EQUAL, lambda, d_zero)));

        // basis times l: ((* 1 l) (* 0 l)) for (1 0)
        Vector ray;
        for (const Integer& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = d_nm->mkNode(Kind::MULT, constant, lambda);
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }
      lambdas.push_back({point, rays});
    }
    cones.push_back({disjunct, polyhedron});
  }

  // y_i is the sum of the i-th coordinates of all points and rays, here
  //   (= a (+ (+ 0 (* 2 mu)) (* 1 l))) and (= b (+ (+ 0 (* 1 mu)) (* 0 l)))
  Vector sums(dimension, d_zero);
  for (const std::pair<Vector, std::vector<Vector>>& pair : lambdas)
  {
    for (size_t i = 0; i < dimension; i++)
    {
      sums[i] = d_nm->mkNode(Kind::ADD, sums[i], pair.first[i]);
      for (const auto& ray : pair.second)
      {
        sums[i] = d_nm->mkNode(Kind::ADD, sums[i], ray[i]);
      }
    }
  }

  for (size_t i = 0; i < dimension; i++)
  {
    starConstraints.push_back(vec[i].eqNode(sums[i]));
  }

  d_stats.d_getConesTime.stop();
  return std::make_pair(cones, starConstraints);
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getLia(
    Node n, const std::vector<std::pair<Node, IntegerPolyhedron>>& cones)
{
  d_stats.d_getLiaTime.start();
  // The examples follow the lambda n of checkFullEffort, whose variables vec
  // are (x y), and its disjunct (and (>= x 2) (= y 1)) with the module
  // generator (2 1) and the Hilbert basis {(1 0)}.
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;

  for (const auto& [node, polyhedron] : cones)
  {
    size_t numPointed = polyhedron.getHilbertBasis().size();
    const std::vector<IntegerVector> hilbertBasis =
        polyhedron.getRecessionMonoidGenerators();
    for (const IntegerVector& generator : polyhedron.getModuleGenerators())
    {
      std::vector<Node> conjunctions;
      // the generator as constants: (2 1)
      Vector point;
      for (const Integer& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        point.push_back(constant);
      }

      std::vector<Vector> rays;
      // the bound variables l1, ..., lk, here l1 for (1 0)
      std::vector<Node> boundVariables;
      for (size_t index = 0; index < hilbertBasis.size(); index++)
      {
        const IntegerVector& basis = hilbertBasis[index];
        std::string name = "l" + std::to_string(index + 1);
        Node lambda = d_nm->mkBoundVar(name, d_nm->integerType());
        boundVariables.push_back(lambda);
        if (index < numPointed)
        {
          // (>= l1 0), except for a direction of the maximal subspace, which
          // has any sign
          conjunctions.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }

        // basis times l1, rewritten: (l1 0) for (1 0)
        Vector ray;
        for (const Integer& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = rewrite(d_nm->mkNode(Kind::MULT, constant, lambda));
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }

      // x_i = g_i + h_1i * l1 + ... + h_ki * lk, here (+ 2 l1) for x and 1
      // for y
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
      // (and (>= l1 0) (= x (+ 2 l1)) (= y 1)), then
      // (exists ((l1 Int)) (and (>= l1 0) (= x (+ 2 l1)) (= y 1)))
      Node conjunction;
      if (conjunctions.size() == 1)
      {
        conjunction = conjunctions[0];
      }
      else
      {
        conjunction = d_nm->mkNode(Kind::AND, conjunctions);
      }
      if (boundVariables.size() > 0)
      {
        Node variables = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVariables);
        conjunction = d_nm->mkNode(Kind::EXISTS, variables, conjunction);
      }
      disjunctions.push_back({node, conjunction});
    }
  }

  d_stats.d_getLiaTime.stop();
  return disjunctions;
}

const std::vector<std::pair<LinearConstraints, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  Assert(n.getKind() == Kind::LAMBDA);

  // for n = (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1))), variables is
  // ((x Int) (y Int)) and predicate is (and (>= x 2) (= y 1))
  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

  // print the preamble of the liastar-ext-smt queries, which declares the
  // variables of the lambda. getCones only assumes them to be nonnegative
  // with --arith-liastar-assume-nonnegative, and so do the queries.
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(set-logic ALL)" << std::endl;
    Trace("liastar-ext-smt") << "(set-option :incremental true)" << std::endl;
    Trace("liastar-ext-smt")
        << "(set-option :produce-models true)" << std::endl;
    for (Node var : variables)
    {
      Trace("liastar-ext-smt")
          << "(declare-const " << var << " Int)" << std::endl;
    }
    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      for (Node var : variables)
      {
        Trace("liastar-ext-smt")
            << "(assert (>= " << var << " 0))" << std::endl;
      }
    }
  }

  // (and (>= x 2) (= y 1)) is in DNF already, while
  //   (and (>= x 2) (or (= y 1) (>= y 3)))
  //   --> (or (and (>= x 2) (= y 1)) (and (>= x 2) (>= y 3)))
  Node dnf = LiaStarUtils::toDNF(predicate, d_env, &d_stats);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  // the single pair of {x - 2 >= 0, y - 1 = 0} and the disjunct
  // (and (>= x 2) (= y 1))
  d_stats.d_getMatricesTime.start();
  std::vector<std::pair<LinearConstraints, Node>> pairs =
      LiaStarUtils::getMatrices(variables, dnf);
  d_stats.d_getMatricesTime.stop();
  ++d_stats.d_dnfCalls;
  d_stats.d_dnfDisjuncts += pairs.size();
  d_stats.d_dnfDisjunctsMax.maxAssign(pairs.size());
  return pairs;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

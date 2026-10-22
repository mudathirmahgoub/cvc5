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

#include "expr/skolem_manager.h"
#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/datatypes/tuple_utils.h"
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
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_checkCounter(0),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasLiaStarTerms(context(), false),
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
  // eliminated by context-dependent simplification.
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_hasLiaStarTerms = true;
    d_extTheory.registerTerm(n);
  }
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
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
  d_stats.d_checkFullEffortTime.start();
  // run a last call effort check
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  d_checkCounter++;
  ++d_stats.d_checkRuns;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);
  d_stats.d_starContainsLiterals += assertions.size();

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    Assert(literal.getKind() == Kind::STAR_CONTAINS);
    // The first child may have been purified into a skolem by lambda
    // lifting, and the rewriter may normalize a constant lambda to a
    // function array constant; recover the lambda from either form.
    Node lambda =
        uf::FunctionConst::toLambda(SkolemManager::getOriginalForm(literal[0]));
    Assert(!lambda.isNull() && lambda.getKind() == Kind::LAMBDA)
        << "Expected a lambda as the first child of " << literal << std::endl;
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(literal, nm);

    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      // assert that vector elements are non negative. The nonnegativity
      // only holds under the originating star-contains literal, so guard
      // the lemma with it: an unguarded lemma would be treated as valid
      // by the SAT solver, corrupting unsat cores and other contexts
      // where the literal does not hold.
      Node lemma = literal.impNode(nonnegative);
      d_im.addPendingLemma(
          lemma, InferenceId::ARITH_LIA_STAR_NONNEGATIVE, nullptr);
    }
    // add a spliting lemma for vector predicate
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR_SPLIT, nullptr);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    if (options().arith.arithLiaStarModelValue)
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
            << literal << " is satisfied in the current model" << std::endl;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        d_stats.d_modelValueTime.stop();
        continue;
      }
      d_stats.d_modelValueTime.stop();
    }

    if (std::find(
            d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
        != d_processedStarTerms.end())
    {
      continue;
    }
    // more work need to be done
    std::vector<std::pair<LinearConstraints, Node>> pairs =
        convertQFLIAToMatrices(lambda);

    auto [cones, starConstraints] = getCones(literal, pairs);
    std::vector<std::pair<Node, Node>> lia = getLia(lambda, cones);

    Trace("liastar-ext") << "lia constraint: " << std::endl;
    if (TraceIsOn("liastar-ext-smt"))
    {
      for (size_t i = 0; i < lia.size(); i++)
      {
        Trace("liastar-ext-smt") << "(push 1)" << std::endl;
        Trace("liastar-ext-smt") << "(echo \"" << i << "\")" << std::endl;
        Trace("liastar-ext-smt") << "(assert " << std::endl
                                 << "  (distinct" << std::endl
                                 << "    ";
        Trace("liastar-ext-smt") << lia[i].first << std::endl << "    ";
        Trace("liastar-ext-smt") << lia[i].second << std::endl
                                 << "  )" << std::endl
                                 << ")" << std::endl;
        Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
        Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
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
      Trace("liastar-ext-smt") << "(push 1)" << std::endl;
      Trace("liastar-ext-smt") << "(echo \"lia formula: \")" << std::endl;
      Trace("liastar-ext-smt") << "(assert " << std::endl
                               << "  (distinct" << std::endl
                               << "    ";
      Trace("liastar-ext-smt") << lambda[1] << std::endl << "    ";
      Trace("liastar-ext-smt") << liaFormula << std::endl
                               << "  )" << std::endl
                               << ")" << std::endl;
      Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
      Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
    }
    Node star = d_nm->mkNode(Kind::AND, starConstraints);
    Trace("liastar-ext") << "starConstraints: " << std::endl
                         << toString(starConstraints) << std::endl;
    star = rewrite(star);
    Node lemma = literal.eqNode(star);
    Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
    d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_EXISTS, nullptr);
    d_processedStarTerms.push_back(literal);
    ++d_stats.d_starTermsReduced;
    d_im.doPendingLemmas();
  }
  d_stats.d_checkFullEffortTime.stop();
}

std::pair<std::vector<std::pair<Node, IntegerPolyhedron>>, std::vector<Node>>
LiaStarExtension::getCones(
    Node n, const std::vector<std::pair<LinearConstraints, Node>>& pairs)
{
  d_stats.d_getConesTime.start();
  std::vector<std::pair<Node, IntegerPolyhedron>> cones;
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  d_stats.d_dimensionMax.maxAssign(dimension);
  IntegerVector zeroVector = IntegerVectorUtils::zero(dimension);
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;
  const bool assumeNonnegative = options().arith.arithLiaStarAssumeNonnegative;

  for (size_t i = 0; i < pairs.size(); i++)
  {
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

    if (polyhedron.isEmpty())
    {
      // the disjunct has no integer solutions, skip it
      Trace("liastar-ext") << "empty cone" << std::endl;
      ++d_stats.d_conesEmpty;
      continue;
    }
    ++d_stats.d_conesNonempty;
    // the Hilbert basis comes first and takes nonnegative multipliers, the
    // maximal subspace follows and takes sign-unrestricted ones
    size_t numPointed = polyhedron.getHilbertBasis().size();
    const std::vector<IntegerVector> hilbertBasis =
        polyhedron.getRecessionMonoidGenerators();
    const std::vector<IntegerVector>& generators =
        polyhedron.getModuleGenerators();
    d_stats.d_hilbertBasisTotal += hilbertBasis.size();
    d_stats.d_hilbertBasisMax.maxAssign(hilbertBasis.size());
    d_stats.d_moduleGeneratorsTotal += generators.size();
    d_stats.d_moduleGeneratorsMax.maxAssign(generators.size());

    for (const IntegerVector& generator : generators)
    {
      Node mu = d_one;
      if (generator != zeroVector)
      {
        mu = d_nm->mkDummySkolem("mu", d_nm->integerType());
      }

      starConstraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
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
        Node lambda = d_nm->mkDummySkolem("l", d_nm->integerType());
        if (j < numPointed)
        {
          // Coefficients for Hilbert bases are nonnegative
          starConstraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }
        // (=> (= mu 0) (= l 0))
        starConstraints.push_back(
            d_nm->mkNode(Kind::EQUAL, mu, d_zero)
                .impNode(d_nm->mkNode(Kind::EQUAL, lambda, d_zero)));

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

  // sum constraints
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
      Vector point;
      for (const Integer& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        point.push_back(constant);
      }

      std::vector<Vector> rays;
      std::vector<Node> boundVariables;
      for (size_t index = 0; index < hilbertBasis.size(); index++)
      {
        const IntegerVector& basis = hilbertBasis[index];
        std::string name = "l" + std::to_string(index + 1);
        Node lambda = d_nm->mkBoundVar(name, d_nm->integerType());
        boundVariables.push_back(lambda);
        if (index < numPointed)
        {
          // (>= l 0); a lineality direction is unrestricted in sign
          conjunctions.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }

        Vector ray;
        for (const Integer& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = rewrite(d_nm->mkNode(Kind::MULT, constant, lambda));
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }

      // sum constraints
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

Node LiaStarExtension::isNotZeroVector(Node v)
{
  std::vector<Node> elements = datatypes::TupleUtils::getTupleElements(v);
  Node notZero = d_false;
  for (Node element : elements)
  {
    notZero = notZero.orNode(element.eqNode(d_zero).notNode());
  }
  Trace("liastar-ext") << v << " is not zero: " << notZero << std::endl;
  return notZero;
}

const std::vector<std::pair<LinearConstraints, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  Assert(n.getKind() == Kind::LAMBDA);

  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

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
    for (Node var : variables)
    {
      Trace("liastar-ext-smt") << "(assert (>= " << var << " 0))" << std::endl;
    }
  }

  Node dnf = LiaStarUtils::toDNF(predicate, &d_env, &d_stats);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

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

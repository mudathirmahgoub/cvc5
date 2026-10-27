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

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "liastar_utils.h"
#include "libnormaliz/input.h"
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
    // a body with star-contains atoms of its own: those are eliminated by
    // flattenNestedStars below, and the splitting lemma and the model value
    // check are skipped, since the vector predicate would carry the inner
    // atoms over the sums
    const bool nested = hasNestedStar(lambda[1]);
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
    if (!nested)
    {
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
    }

    if (std::find(
            d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
        != d_processedStarTerms.end())
    {
      continue;
    }
    // more work need to be done
    Node flat = lambda;
    std::vector<Node> extraVars;
    if (nested)
    {
      flat = flattenNestedStars(lambda, extraVars);
      if (flat.isNull())
      {
        Trace("liastar-ext")
            << "nested star under a negation in " << literal << std::endl;
        d_im.setModelUnsound(IncompleteId::UNKNOWN);
        d_processedStarTerms.push_back(literal);
        continue;
      }
    }
    std::vector<std::pair<std::vector<std::string>, Node>> pairs =
        convertQFLIAToMatrices(flat);
    Node flatLiteral = literal;
    if (!extraVars.empty())
    {
      // the outer star gets a coordinate for each witness of the inner stars;
      // its sum over the rows is free
      std::vector<Node> children(literal.begin(), literal.end());
      children[0] = flat;
      for (size_t i = 0, ne = extraVars.size(); i < ne; i++)
      {
        children.push_back(
            d_nm->mkDummySkolem("liastar_nested_sum", d_nm->integerType()));
      }
      flatLiteral = d_nm->mkNode(Kind::STAR_CONTAINS, children);
    }

    auto [cones, starConstraints] = getCones(flatLiteral, pairs);
    std::vector<std::pair<Node, Node>> lia = getLia(flat, cones);

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

/**
 * Normaliz's `getHilbertBasis()` covers only the *pointed* part of a cone: for
 * a cone containing a line it is relative to the cone's maximal subspace (its
 * lineality space), so non-negative combinations of it miss lattice points. The
 * maximal subspace is appended to complete it, once per generator, with a
 * sign-unrestricted multiplier -- a lineality direction is available in both
 * directions. Appending `m` and `-m` instead would also be correct, but gives
 * every point infinitely many representations, which the arithmetic search then
 * has to enumerate.
 *
 * `numPointed` returns how many leading entries came from `getHilbertBasis()`
 * and so must keep a non-negative multiplier. For a pointed cone the maximal
 * subspace is empty and the result is exactly `getHilbertBasis()`.
 */
static std::vector<std::vector<Integer>> getHilbertBasisWithLineality(
    libnormaliz::Cone<Integer>& cone, size_t& numPointed)
{
  std::vector<std::vector<Integer>> basis = cone.getHilbertBasis();
  numPointed = basis.size();
  for (const std::vector<Integer>& generator : cone.getMaximalSubspace())
  {
    basis.push_back(generator);
  }
  return basis;
}

std::vector<LiaStarExtension::ConeData> LiaStarExtension::computeConeData(
    size_t dimension,
    const std::vector<std::pair<std::vector<std::string>, Node>>& pairs)
{
  d_stats.d_getConesTime.start();
  d_stats.d_dimensionMax.maxAssign(dimension);
  std::vector<Integer> zeroVector(dimension, Integer(0));
  std::vector<ConeData> cones;
  const bool assumeNonnegative = options().arith.arithLiaStarAssumeNonnegative;

  for (size_t i = 0; i < pairs.size(); i++)
  {
    const std::pair<std::vector<std::string>, Node>& pair = pairs[i];
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << i << std::endl
                         << pair.second << std::endl;

    libnormaliz::OptionsHandler options;

    std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
        poly_param_input;
    std::map<libnormaliz::NumParam::Param, long> num_param_input;
    std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

    libnormaliz::renf_class_ptr number_field_ref;

    std::stringstream ss;
    ss << "amb_space " << dimension << std::endl;
    ss << "constraints " << pair.first.size() << " symbolic" << std::endl;
    for (auto constraint : pair.first)
    {
      ss << constraint << std::endl;
    }
    if (assumeNonnegative)
    {
      ss << "nonnegative" << std::endl;
    }
    else
    {
      // nonnegativity is not assumed so declare every coordinate
      // sign-unrestricted
      // signs is a vector with entries in {−1, 0, 1}.
      // The entry 1 at the i-th component means x_i >= 0,
      // and entry -1 at the i-th component means x_i <= 0
      // The entry 0 does not impose an inequality.
      ss << "signs" << std::endl;
      for (size_t sj = 0; sj < dimension; sj++)
      {
        ss << (sj == 0 ? "" : " ") << "0";
      }
      ss << std::endl;
    }
    ss << "HilbertBasis" << std::endl;
    ss << "ModuleGenerators" << std::endl;
    Trace("liastar-ext") << "normaliz input:" << std::endl;
    Trace("liastar-ext") << ss.str() << std::endl;

    // here we use mpq_class instead of Integer (or mpz_class)
    // because libnormaliz.so only has implementation for
    // readNormalizInput<mpq_class>
    std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
    d_stats.d_normalizInputTime.start();
    input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                      options,
                                                      num_param_input,
                                                      bool_param_input,
                                                      poly_param_input,
                                                      number_field_ref);
    d_stats.d_normalizInputTime.stop();
    ++d_stats.d_normalizCalls;
    d_stats.d_normalizComputeTime.start();
    Cone<Integer> cone(input);
    if (assumeNonnegative)
    {
      cone.setNonnegative(true);
    }
    else
    {
      cone.setNonnegative(false);
    }
    // always use infinite precision for integers
    cone.deactivateChangeOfPrecision();
    cone.compute(ConeProperty::HilbertBasis);
    cone.compute(ConeProperty::ModuleGenerators);
    // completes the Hilbert basis for a non-pointed cone
    cone.compute(ConeProperty::MaximalSubspace);
    d_stats.d_normalizComputeTime.stop();

    if (cone.isInhomogeneous())
    {
      // AffineDim is only computed for inhomogeneous cones
      if (cone.getAffineDim() == -1)
      {
        // the cone is empty skip.
        Trace("liastar-ext") << "empty cone" << std::endl;
        ++d_stats.d_conesEmpty;
        continue;
      }
    }
    ++d_stats.d_conesNonempty;
    ConeData data;
    data.d_disjunct = pair.second;
    data.d_numPointed = 0;
    data.d_hilbertBasis = getHilbertBasisWithLineality(cone, data.d_numPointed);
    d_stats.d_hilbertBasisTotal += data.d_hilbertBasis.size();
    d_stats.d_hilbertBasisMax.maxAssign(data.d_hilbertBasis.size());
    d_stats.d_moduleGeneratorsTotal += cone.getModuleGenerators().size();
    d_stats.d_moduleGeneratorsMax.maxAssign(cone.getModuleGenerators().size());

    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : data.d_hilbertBasis)
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }
    Trace("liastar-ext") << "Module generators:" << std::endl;
    data.d_generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      data.d_generators = cone.getModuleGenerators();
    }
    for (const auto& generator : data.d_generators)
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
    }
    cones.push_back(data);
  }
  d_stats.d_getConesTime.stop();
  return cones;
}

Node LiaStarExtension::starFormula(const std::vector<Node>& vec,
                                   const std::vector<ConeData>& cones,
                                   std::vector<Node>& vars,
                                   bool asBoundVars)
{
  size_t dimension = vec.size();
  TypeNode intType = d_nm->integerType();
  auto fresh = [&](const std::string& name) {
    Node v = asBoundVars ? d_nm->mkBoundVar(name, intType)
                         : d_nm->mkDummySkolem(name, intType);
    vars.push_back(v);
    return v;
  };
  std::vector<Node> constraints;
  Vector sums(dimension, d_zero);
  for (const ConeData& data : cones)
  {
    for (const std::vector<Integer>& generator : data.d_generators)
    {
      bool isZero = true;
      for (const Integer& element : generator)
      {
        isZero = isZero && element == 0;
      }
      Node mu = d_one;
      if (!isZero)
      {
        mu = fresh("mu");
        constraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
      }
      for (size_t i = 0; i < dimension; i++)
      {
        Node constant = d_nm->mkConstInt(Rational(generator[i].get_str()));
        sums[i] = d_nm->mkNode(
            Kind::ADD, sums[i], d_nm->mkNode(Kind::MULT, constant, mu));
      }
      for (size_t j = 0, nb = data.d_hilbertBasis.size(); j < nb; j++)
      {
        const std::vector<Integer>& basis = data.d_hilbertBasis[j];
        Node lambda = fresh("l");
        if (j < data.d_numPointed)
        {
          // Coefficients for Hilbert bases are nonnegative
          constraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }
        if (!isZero)
        {
          // (=> (= mu 0) (= l 0)). Inside a star body it is written without
          // the implication, which the DNF conversion does not accept: mu is
          // nonnegative, so (or (>= mu 1) (= l 0)) says the same.
          constraints.push_back(
              asBoundVars ? d_nm->mkNode(Kind::OR,
                                         d_nm->mkNode(Kind::GEQ, mu, d_one),
                                         lambda.eqNode(d_zero))
                          : mu.eqNode(d_zero).impNode(lambda.eqNode(d_zero)));
        }
        for (size_t i = 0; i < dimension; i++)
        {
          Node constant = d_nm->mkConstInt(Rational(basis[i].get_str()));
          sums[i] = d_nm->mkNode(
              Kind::ADD, sums[i], d_nm->mkNode(Kind::MULT, constant, lambda));
        }
      }
    }
  }
  for (size_t i = 0; i < dimension; i++)
  {
    constraints.push_back(vec[i].eqNode(sums[i]));
  }
  Node formula = constraints.size() == 1 ? constraints[0]
                                         : d_nm->mkNode(Kind::AND, constraints);
  // inside a star body the atoms must be in the normal form the DNF
  // conversion reads, as the atoms of a bag translation are
  return asBoundVars ? rewrite(formula) : formula;
}

std::pair<std::vector<LiaStarExtension::ConeData>, std::vector<Node>>
LiaStarExtension::getCones(
    Node n, const std::vector<std::pair<std::vector<std::string>, Node>>& pairs)
{
  std::vector<Node> vec(n.begin() + 1, n.end());
  std::vector<ConeData> cones = computeConeData(vec.size(), pairs);
  std::vector<Node> skolems;
  Node formula = starFormula(vec, cones, skolems, false);
  std::vector<Node> starConstraints;
  if (formula.getKind() == Kind::AND)
  {
    starConstraints.insert(
        starConstraints.end(), formula.begin(), formula.end());
  }
  else
  {
    starConstraints.push_back(formula);
  }
  return std::make_pair(cones, starConstraints);
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getLia(
    Node n, const std::vector<ConeData>& cones)
{
  d_stats.d_getLiaTime.start();
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;

  for (const ConeData& data : cones)
  {
    for (const auto& generator : data.d_generators)
    {
      std::vector<Node> conjunctions;
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element.get_str()));
        point.push_back(constant);
      }

      std::vector<Vector> rays;
      std::vector<Node> boundVariables;
      const std::vector<std::vector<Integer>>& bases = data.d_hilbertBasis;
      for (size_t index = 0; index < bases.size(); index++)
      {
        const std::vector<Integer>& basis = bases[index];
        std::string name = "l" + std::to_string(index + 1);
        Node lambda = d_nm->mkBoundVar(name, d_nm->integerType());
        boundVariables.push_back(lambda);
        if (index < data.d_numPointed)
        {
          // (>= l 0); a lineality direction is unrestricted in sign
          conjunctions.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }

        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element.get_str()));
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
      disjunctions.push_back({data.d_disjunct, conjunction});
    }
  }

  d_stats.d_getLiaTime.stop();
  return disjunctions;
}

bool LiaStarExtension::hasNestedStar(TNode n)
{
  return expr::hasSubtermKind(Kind::STAR_CONTAINS, n);
}

bool LiaStarExtension::collectNestedStars(TNode n,
                                          bool positive,
                                          std::vector<Node>& stars)
{
  Kind k = n.getKind();
  if (k == Kind::STAR_CONTAINS)
  {
    if (!positive)
    {
      return false;
    }
    if (std::find(stars.begin(), stars.end(), n) == stars.end())
    {
      stars.push_back(n);
    }
    return true;
  }
  if (k == Kind::NOT)
  {
    return collectNestedStars(n[0], !positive, stars);
  }
  if (k == Kind::IMPLIES)
  {
    return collectNestedStars(n[0], !positive, stars)
           && collectNestedStars(n[1], positive, stars);
  }
  if (k == Kind::AND || k == Kind::OR)
  {
    for (const Node& c : n)
    {
      if (!collectNestedStars(c, positive, stars))
      {
        return false;
      }
    }
    return true;
  }
  // under any other operator the atom has both polarities (an ite condition,
  // an equivalence) or is the argument of a term
  return !hasNestedStar(n);
}

Node LiaStarExtension::flattenNestedStars(Node lambda,
                                          std::vector<Node>& extraVars)
{
  Assert(lambda.getKind() == Kind::LAMBDA);
  std::vector<Node> stars;
  if (!collectNestedStars(lambda[1], true, stars))
  {
    return Node::null();
  }
  if (stars.empty())
  {
    return lambda;
  }
  TypeNode intType = d_nm->integerType();
  std::vector<Node> vars(lambda[0].begin(), lambda[0].end());
  Node body = lambda[1];
  for (const Node& star : stars)
  {
    Node innerLambda =
        uf::FunctionConst::toLambda(SkolemManager::getOriginalForm(star[0]));
    Assert(!innerLambda.isNull() && innerLambda.getKind() == Kind::LAMBDA)
        << "Expected a lambda as the first child of " << star << std::endl;
    std::vector<Node> innerExtra;
    Node flat = flattenNestedStars(innerLambda, innerExtra);
    if (flat.isNull())
    {
      return Node::null();
    }
    std::vector<Node> vec(star.begin() + 1, star.end());
    for (size_t i = 0, ne = innerExtra.size(); i < ne; i++)
    {
      // the witnesses of the inner star's own inner stars are summed over its
      // rows, and that sum is a further coordinate of the outer row
      Node w = d_nm->mkBoundVar("liastar_nested", intType);
      vec.push_back(w);
      vars.push_back(w);
      extraVars.push_back(w);
    }
    std::vector<std::pair<std::vector<std::string>, Node>> pairs =
        convertQFLIAToMatrices(flat);
    std::vector<ConeData> cones = computeConeData(vec.size(), pairs);
    std::vector<Node> witnesses;
    Node formula = starFormula(vec, cones, witnesses, true);
    vars.insert(vars.end(), witnesses.begin(), witnesses.end());
    extraVars.insert(extraVars.end(), witnesses.begin(), witnesses.end());
    Trace("liastar-ext") << "nested star " << star << " with " << cones.size()
                         << " cones and " << witnesses.size() << " witnesses"
                         << std::endl;
    TNode from = star;
    TNode to = formula;
    body = body.substitute(from, to);
    ++d_stats.d_nestedStarsFlattened;
  }
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, vars), body);
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

const std::vector<std::pair<std::vector<std::string>, Node>>
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

  Node dnf = LiaStarUtils::toDNF(predicate, d_env, &d_stats);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  d_stats.d_getMatricesTime.start();
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
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

#endif /* CVC5_USE_NORMALIZ */
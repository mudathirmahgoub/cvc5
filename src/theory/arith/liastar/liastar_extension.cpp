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
 * Extension to the theory of arithmetic handling lia star operator.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

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
      d_hasLiaStarTerms(context(), false)
{
  d_extTheory.addFunctionKind(Kind::STAR_CONTAINS);
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
  if (env.isTheoryProofProducing())
  {
    d_proof.reset(
        new CDProofSet<CDProof>(env, env.getUserContext(), "liastar-ext"));
    d_proofGen.reset(new LiaStarProofGenerator(env, env.getUserContext()));
  }
  Options subOptions;
  // we read the model below to construct the disjunct.
  subOptions.write_smt().produceModels = true;
  d_solverEngine = new SolverEngine(d_nm, &subOptions);
  d_solverEngine->setIsInternalSubsolver();
  LogicInfo info("QF_LIA");
  d_solverEngine->setLogic(info);
  d_solverEngine->setOption("incremental", "true");
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
  // run a last call effort check
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
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(literal, nm);
    // assert that vector elements are non negative
    if (d_proofGen != nullptr)
    {
      d_proofGen->registerNonnegative(nonnegative, literal);
    }
    d_im.addPendingLemma(
        nonnegative, InferenceId::ARITH_LIA_STAR_NONNEGATIVE, d_proofGen.get());
    // add a spliting lemma for vector predicate
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
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }
  // more work need to be done
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
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
    std::transform(
        lia.begin(), lia.end(), std::back_inserter(disjunctions), [](auto& p) {
          return p.second;
        });
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
  if (d_proofGen != nullptr)
  {
    d_proofGen->registerContainsReduce(lemma, literal, star);
  }
  d_im.addPendingLemma(
      lemma, InferenceId::ARITH_LIA_STAR_EXISTS, d_proofGen.get());
  d_processedStarTerms.push_back(literal);
  d_im.doPendingLemmas();
}

void LiaStarExtension::lazyCheckStar(Node literal, Node lambda)
{
  if (std::find(
          d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
      != d_processedStarTerms.end())
  {
    return;
  }

  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>> pairs =
      d_lazyCones[lambda];
  Node formula = lambda[1];
  if (pairs.size() == 0)
  {
    // The lambda's bound variables appear free in `assertion`. A formula with
    // free (bound) variables cannot be asserted to a subsolver, so we replace
    // them with fresh free constants and substitute them back in the returned
    // disjunct.
    std::vector<Node> from;
    std::vector<Node> to;
    for (Node var : lambda[0])
    {
      if (var.getKind() == Kind::BOUND_VARIABLE)
      {
        from.push_back(var);
        to.push_back(d_nm->mkDummySkolem(var.toString(), var.getType()));
      }
    }
    if (!from.empty())
    {
      formula =
          formula.substitute(from.begin(), from.end(), to.begin(), to.end());
    }
    d_solverEngine->assertFormula(formula);
  }
  else
  {
    d_solverEngine->push();
    Node disjunct = pairs[pairs.size() - 1].first;
    d_solverEngine->assertFormula(disjunct.notNode());
  }
  // for (auto& pair : pairs)
  // {
  //   Node disjunct = pair.first;
  //   formula = formula.andNode(disjunct.notNode());
  // }
  lazyHilbert(literal, formula);
}

std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
          std::vector<Node>>
LiaStarExtension::getCones(
    Node n, const std::vector<std::pair<std::vector<std::string>, Node>>& pairs)
{
  std::vector<std::pair<Node, Cone<Integer>>> cones;
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  std::vector<Integer> zeroVector(dimension, Integer(0));
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;

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
    ss << "nonnegative" << std::endl;
    ss << "HilbertBasis" << std::endl;
    ss << "ModuleGenerators" << std::endl;
    Trace("liastar-ext") << "normaliz input:" << std::endl;
    Trace("liastar-ext") << ss.str() << std::endl;

    // here we use mpq_class instead of Integer (or mpz_class)
    // because libnormaliz.so only has implementation for
    // readNormalizInput<mpq_class>
    std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
    input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                      options,
                                                      num_param_input,
                                                      bool_param_input,
                                                      poly_param_input,
                                                      number_field_ref);
    Cone<Integer> cone(input);
    cone.setNonnegative(true);
    // always use infinite precision for integers
    cone.deactivateChangeOfPrecision();
    cone.compute(ConeProperty::HilbertBasis);
    cone.compute(ConeProperty::ModuleGenerators);

    if (cone.isInhomogeneous())
    {
      // AffineDim is only computed for inhomogeneous cones
      if (cone.getAffineDim() == -1)
      {
        // the cone is empty skip.
        Trace("liastar-ext") << "empty cone" << std::endl;
        continue;
      }
    }

    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : cone.getHilbertBasis())
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }

    Trace("liastar-ext") << "Module generators:" << std::endl;
    std::vector<std::vector<Integer>> generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      generators = cone.getModuleGenerators();
    }
    for (const auto& generator : generators)
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      Node mu = d_one;
      if (generator != zeroVector)
      {
        mu = d_nm->mkDummySkolem("mu", d_nm->integerType());
      }

      starConstraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        Node monomial = d_nm->mkNode(Kind::MULT, constant, mu);
        point.push_back(monomial);
      }
      std::vector<Vector> rays;
      for (const auto& basis : cone.getHilbertBasis())
      {
        Node lambda = d_nm->mkDummySkolem("l", d_nm->integerType());
        // (>= l 0)
        starConstraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        // (=> (= mu 0) (= l 0))
        starConstraints.push_back(
            d_nm->mkNode(Kind::EQUAL, mu, d_zero)
                .impNode(d_nm->mkNode(Kind::EQUAL, lambda, d_zero)));

        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = d_nm->mkNode(Kind::MULT, constant, lambda);
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }
      lambdas.push_back({point, rays});
    }
    cones.push_back({pair.second, cone});
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

  return std::make_pair(cones, starConstraints);
}

void LiaStarExtension::addCone(
    Node n, const std::pair<std::vector<std::string>, Node>& pair)
{
  size_t dimension = n.getNumChildren() - 1;

  // the cones accumulated so far for this lambda (n[0])
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[n[0]];

  // Build the cone for the current pair and append it to the list of cones.
  {
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << std::endl
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
    ss << "nonnegative" << std::endl;
    ss << "HilbertBasis" << std::endl;
    ss << "ModuleGenerators" << std::endl;
    Trace("liastar-ext") << "normaliz input:" << std::endl;
    Trace("liastar-ext") << ss.str() << std::endl;

    // here we use mpq_class instead of Integer (or mpz_class)
    // because libnormaliz.so only has implementation for
    // readNormalizInput<mpq_class>
    std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
    input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                      options,
                                                      num_param_input,
                                                      bool_param_input,
                                                      poly_param_input,
                                                      number_field_ref);
    Cone<Integer> cone(input);
    cone.setNonnegative(true);
    // always use infinite precision for integers
    cone.deactivateChangeOfPrecision();
    cone.compute(ConeProperty::HilbertBasis);
    cone.compute(ConeProperty::ModuleGenerators);

    bool empty = cone.isInhomogeneous() && cone.getAffineDim() == -1;
    if (empty)
    {
      // the cone is empty, do not add it to the list.
      Trace("liastar-ext") << "empty cone" << std::endl;
    }
    else
    {
      cones.push_back({pair.second, cone});
    }
  }
}

std::vector<Node> LiaStarExtension::getStarConstraints(Node n)
{
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  std::vector<Integer> zeroVector(dimension, Integer(0));

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

    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (auto& basis : cone.getHilbertBasis())
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }

    Trace("liastar-ext") << "Module generators:" << std::endl;
    std::vector<std::vector<Integer>> generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      generators = cone.getModuleGenerators();
    }
    for (const auto& generator : generators)
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
  Vector sums(dimension, d_zero);
  for (const std::pair<Vector, std::vector<Vector>>& p : lambdas)
  {
    for (size_t i = 0; i < dimension; i++)
    {
      sums[i] = d_nm->mkNode(Kind::ADD, sums[i], p.first[i]);
      for (const auto& ray : p.second)
      {
        sums[i] = d_nm->mkNode(Kind::ADD, sums[i], ray[i]);
      }
    }
  }

  for (size_t i = 0; i < dimension; i++)
  {
    result.push_back(vec[i].eqNode(sums[i]));
  }

  return result;
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getLia(
    Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones)
{
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;
  std::vector<Integer> zeroVector(dimension, Integer(0));

  for (auto& pair : cones)
  {
    Node node = pair.first;
    libnormaliz::Cone<Integer> cone = pair.second;
    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : cone.getHilbertBasis())
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }

    Trace("liastar-ext") << "Module generators:" << std::endl;
    std::vector<std::vector<Integer>> generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      generators = cone.getModuleGenerators();
    }
    for (const auto& generator : generators)
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

  Node dnf = LiaStarUtils::toDNF(predicate, &d_env);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      LiaStarUtils::getMatrices(variables, dnf);
  return pairs;
}
void LiaStarExtension::lazyHilbert(Node literal, Node formula)
{
  Node variables = literal[0][0];
  Trace("liastar-lazy") << "lazyHilbert::variables:" << variables << std::endl;
  Trace("liastar-lazy") << "lazyHilbert::formula:" << formula << std::endl;
  Trace("liastar-lazy") << "formula: " << formula << std::endl;

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

  Node nnf = LiaStarUtils::removeItesAndNots(formula, &d_env);
  std::vector<Node> freeVariables;
  for (size_t i = 0; i < variables.getNumChildren(); i++)
  {
    freeVariables.push_back(variables[i]);
  }
  Node disjunct =
      LiaStarUtils::getDisjunct(freeVariables, nnf, &d_env, d_solverEngine);
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
/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for lia star utilities.
 */

#ifdef CVC5_USE_NORMALIZ

#include <iostream>
#include <memory>
#include <vector>

#include "cvc5/cvc5.h"
#include "cvc5/cvc5_parser.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "test_smt.h"
#include "theory/arith/liastar/liastar_utils.h"
#include "theory/logic_info.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace cvc5;
using namespace cvc5::parser;
using namespace theory;
using namespace theory::arith;
using namespace theory::arith::liastar;

namespace test {

class TestLiaStarUtils : public TestSmt
{
 protected:
  TypeNode intType;
  Node zero, one, two, x, y;
  NodeManager* nm;
  Env* e;

  void SetUp() override
  {
    TestSmt::SetUp();
    d_slvEngine->setOption("dag-thresh", "0", true);
    nm = d_nodeManager.get();
    e = &d_slvEngine->getEnv();
    intType = nm->integerType();
    zero = nm->mkConstInt(Rational(0));
    one = nm->mkConstInt(Rational(1));
    two = nm->mkConstInt(Rational(2));
    x = nm->mkBoundVar("x", intType);
    y = nm->mkBoundVar("y", intType);
  }

  Node boundVarList(const std::vector<Node>& vars)
  {
    return nm->mkNode(Kind::BOUND_VAR_LIST, vars);
  }

  Node lambda(const std::vector<Node>& vars, Node body)
  {
    return nm->mkNode(Kind::LAMBDA, boundVarList(vars), body);
  }

  Node boolVar(const std::string& name)
  {
    return nm->mkBoundVar(name, nm->booleanType());
  }
};

TEST_F(TestLiaStarUtils, getVectorPredicateInstantiatesLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  Node v = nm->mkBoundVar("v", intType);
  // (int.star-contains (lambda ((u Int) (v Int)) (>= u v)) x y)
  Node star = nm->mkNode(
      Kind::STAR_CONTAINS, lambda({u, v}, nm->mkNode(Kind::GEQ, u, v)), x, y);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkNode(Kind::GEQ, x, y), predicate);
  ASSERT_EQ("(and (and true (>= x 0)) (>= y 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getVectorPredicateAcceptsConstantLambda)
{
  Node u = nm->mkBoundVar("u", intType);
  // (int.star-contains (lambda ((u Int)) false) x), where the rewriter
  // normalizes the constant lambda to a function array constant
  Node constantLambda =
      e->getRewriter()->rewrite(lambda({u}, nm->mkConst<bool>(false)));
  Node star = nm->mkNode(Kind::STAR_CONTAINS, constantLambda, x);

  auto [predicate, nonnegative] = LiaStarUtils::getVectorPredicate(star, nm);

  ASSERT_EQ(nm->mkConst<bool>(false), predicate);
  ASSERT_EQ("(and true (>= x 0))", nonnegative.toString());
}

TEST_F(TestLiaStarUtils, getMatricesConjunctionIsOneMatrix)
{
  // (and (>= x 1) (= y 0)) over the coordinates (x y)
  Node conjunction = nm->mkNode(Kind::AND,
                                nm->mkNode(Kind::GEQ, x, one),
                                nm->mkNode(Kind::EQUAL, y, zero));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), conjunction);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;", "x[2] = 0;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, getMatricesDisjunctionIsOneMatrixPerDisjunct)
{
  // (or (>= x 1) (>= y 2))
  Node disjunction = nm->mkNode(
      Kind::OR, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::GEQ, y, two));

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), disjunction);

  ASSERT_EQ(2, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"x[1] >= 1;"}), matrices[0].first);
  ASSERT_EQ(std::vector<std::string>({"x[2] >= 2;"}), matrices[1].first);
}

TEST_F(TestLiaStarUtils, getMatricesPrintsCoefficients)
{
  // (>= (+ (* 2 x) y) 1)
  Node sum = nm->mkNode(Kind::ADD, nm->mkNode(Kind::MULT, two, x), y);
  Node constraint = nm->mkNode(Kind::GEQ, sum, one);

  auto matrices = LiaStarUtils::getMatrices(boundVarList({x, y}), constraint);

  ASSERT_EQ(1, matrices.size());
  ASSERT_EQ(std::vector<std::string>({"2x[1] + x[2] >= 1;"}),
            matrices[0].first);
}

TEST_F(TestLiaStarUtils, cvc5CheckSatUnsat)
{
  // exists x. x >= 1 and x <= 0
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, e);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, cvc5CheckSatSat)
{
  // exists x. x >= 1
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result = LiaStarUtils::cvc5CheckSat({x}, assertion, e);

  ASSERT_EQ(Result::Status::SAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatConjoinsAssertions)
{
  // x >= 1 and x <= 0 are unsat together, satisfiable apart
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::areAssertionsUnsat({lower, upper}, e).getStatus());
  ASSERT_EQ(Result::Status::SAT,
            LiaStarUtils::areAssertionsUnsat({lower}, e).getStatus());
}

TEST_F(TestLiaStarUtils, areAssertionsUnsatIsNoneWhenSubsolverIsDisabled)
{
  d_slvEngine->setOption("arith-liastar-subsolver", "false", true);
  Node lower = nm->mkNode(Kind::GEQ, x, one);
  Node upper = nm->mkNode(Kind::LEQ, x, zero);

  Result result = LiaStarUtils::areAssertionsUnsat({lower, upper}, e);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatEmptyConeIsUnsat)
{
  // x >= 1 and x <= 0 describe an empty cone
  Node assertion = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, x, one), nm->mkNode(Kind::LEQ, x, zero));

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::UNSAT, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatNonemptyConeIsNone)
{
  // x >= 1 describes a nonempty cone, which is reported as none rather
  // than sat
  Node assertion = nm->mkNode(Kind::GEQ, x, one);

  Result result =
      LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false);

  ASSERT_EQ(Result::Status::NONE, result.getStatus());
}

TEST_F(TestLiaStarUtils, normalizCheckSatAssumeNonnegative)
{
  // x <= -1 is satisfiable over the integers, but not over the
  // nonnegative orthant
  Node assertion = nm->mkNode(Kind::LEQ, x, nm->mkConstInt(Rational(-1)));

  ASSERT_EQ(Result::Status::NONE,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, false)
                .getStatus());
  ASSERT_EQ(Result::Status::UNSAT,
            LiaStarUtils::normalizCheckSat(boundVarList({x}), assertion, true)
                .getStatus());
}

TEST_F(TestLiaStarUtils, distribute1)
{
  Node a = boolVar("a"), b = boolVar("b"), f = boolVar("f"), g = boolVar("g");
  Node u = boolVar("u"), v = boolVar("v"), p = boolVar("p"), q = boolVar("q");
  Node z = boolVar("z");
  // (and
  //   (or
  //     (and
  //        (or f g)
  //        (or p q))
  //      z)
  //     (or u v)
  //   (and a b)
  //  )

  Node or_fg = nm->mkNode(Kind::OR, {f, g});
  Node or_xy = nm->mkNode(Kind::OR, {p, q});
  Node or_uv = nm->mkNode(Kind::OR, {u, v});
  Node and_ab = nm->mkNode(Kind::AND, {a, b});
  Node and_or_fg_or_xy = nm->mkNode(Kind::AND, {or_fg, or_xy});
  Node and_z = nm->mkNode(Kind::AND, {and_or_fg_or_xy, z});
  Node or_uv_z = nm->mkNode(Kind::OR, {or_uv, and_z});
  Node and_outer = nm->mkNode(Kind::AND, {or_uv_z, and_ab});
  Node dnf = LiaStarUtils::distribute(and_outer, e);
  dnf = LiaStarUtils::recursiveFlatten(nm, dnf);
  // The disjuncts and their literals are fixed, but the order of an AND's
  // children follows node ids, so it depends on `distribute`'s construction
  // order. This expects the order produced by the implementation in
  // `liastar_utils.cpp`; the formula is the same either way.
  ASSERT_EQ(
      "(or (and u a b) (and v a b) (and f p z a b) (and g p z a b) (and f q z "
      "a b) (and g q z a b))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF1)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9)), i.e., not (3*x - y >= 9)
  Node three = nm->mkConstInt(Rational(3));
  Node nine = nm->mkConstInt(Rational(9));

  Node threeTimesX = nm->mkNode(Kind::MULT, three, x);
  Node minus = nm->mkNode(Kind::SUB, threeTimesX, y);
  Node geq = nm->mkNode(Kind::GEQ, minus, nine);
  Node notGEQ = geq.notNode();
  Node dnf = LiaStarUtils::toDNF(notGEQ, e);
  ASSERT_EQ("(< (- (* 3 x) y) 9)", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF2)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  // (and (or a b) (or c d))
  Node or_a_b = a.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and a d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF3)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or (and a p) b) (or c d))
  Node and_a_x = a.andNode(p);
  Node or_a_b = and_a_x.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a p c) (and b c) (and a p d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF4)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a (and b p)) (or c d))
  Node and_b_x = b.andNode(p);
  Node or_a_b = a.orNode(and_b_x);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b p c) (and a d) (and b p d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF5)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p");
  // (and (or a b p) (or c d))
  Node or1 = nm->mkNode(Kind::OR, {a, b, p});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node and = or1.andNode(or2);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and p c) (and a d) (and b d) (and p d))",
            dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF6)
{
  Node a = boolVar("a"), b = boolVar("b"), c = boolVar("c"), d = boolVar("d");
  Node p = boolVar("p"), q = boolVar("q");
  // (and (or a b) (or c d) (or p q))
  Node or1 = nm->mkNode(Kind::OR, {a, b});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node or3 = nm->mkNode(Kind::OR, {p, q});
  Node and = nm->mkNode(Kind::AND, {or1, or2, or3});
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ(
      "(or (and a c p) (and b c p) (and a d p) (and b d p) (and a c q) (and b "
      "c q) (and a d q) (and b d q))",
      dnf.toString());
}


// The tests below exercise the lazy-strategy helpers. They keep their own
// fixture: the expected DNF strings are sensitive to the order in which the
// bound variables are created (AND/OR children are sorted by node id), so the
// setup is preserved verbatim from the lazy branch rather than folded into the
// fixture above.

class TestLiaStarLazyUtils : public TestSmt
{
 protected:
  TypeNode intType, boolType;
  Node trueConst, falseConst;
  Node negativeOne, zero, one, two, three, nine, twentyOne;
  Node a, b, c, d, f, g, u, v, x, y, z;
  NodeManager* nm;
  Env* e;

  void SetUp() override
  {
    TestSmt::SetUp();
    d_slvEngine->setOption("dag-thresh", "0", true);
    d_slvEngine->setOption("trace", "liastar-ext-smt", true);
    d_slvEngine->setOption("arith-liastar-subsolver", "false", true);
    nm = d_nodeManager.get();
    e = &d_slvEngine->getEnv();
    intType = nm->integerType();
    boolType = nm->booleanType();
    trueConst = nm->mkConst<bool>(true);
    falseConst = nm->mkConst<bool>(false);
    negativeOne = nm->mkConstInt(Rational(-1));
    zero = nm->mkConstInt(Rational(0));
    one = nm->mkConstInt(Rational(1));
    two = nm->mkConstInt(Rational(2));
    three = nm->mkConstInt(Rational(3));
    nine = nm->mkConstInt(Rational(9));
    twentyOne = nm->mkConstInt(Rational(21));
    a = nm->mkBoundVar("a", boolType);
    b = nm->mkBoundVar("b", boolType);
    c = nm->mkBoundVar("c", boolType);
    d = nm->mkBoundVar("d", boolType);
    f = nm->mkBoundVar("f", boolType);
    g = nm->mkBoundVar("g", boolType);
    u = nm->mkBoundVar("u", boolType);
    v = nm->mkBoundVar("v", boolType);
    x = nm->mkBoundVar("x", boolType);
    y = nm->mkBoundVar("y", boolType);
    z = nm->mkBoundVar("z", boolType);
  }

  /**
   * Create an incremental QF_LIA subsolver seeded with `base` conjoined with
   * the non-negativity of `variables`, the way
   * LiaStarExtension::getSubsolver seeds the subsolver that
   * LiaStarUtils::getDisjunct reads models from. Returns the engine and the
   * full (nonnegative) assertion it holds.
   */
  std::pair<std::unique_ptr<SolverEngine>, Node> mkSeededSubsolver(
      Node base, const std::vector<Node>& variables)
  {
    std::vector<Node> conjuncts{base};
    for (Node var : variables)
    {
      conjuncts.push_back(nm->mkNode(Kind::GEQ, var, zero));
    }
    Node assertion = conjuncts.size() == 1 ? conjuncts[0]
                                           : nm->mkNode(Kind::AND, conjuncts);
    Options subOptions;
    // getDisjunct reads the model to construct the disjunct
    subOptions.write_smt().produceModels = true;
    auto engine = std::make_unique<SolverEngine>(nm, &subOptions);
    engine->setIsInternalSubsolver();
    LogicInfo info("QF_LIA");
    engine->setLogic(info);
    engine->setOption("incremental", "true");
    engine->assertFormula(assertion);
    return {std::move(engine), assertion};
  }
};

TEST_F(TestLiaStarLazyUtils, toDNF7)
{
  TermManager tm;
  Solver slv(tm);
  SymbolManager sm(tm);
  Env env(tm.d_nm.get(), slv.d_originalOptions.get());
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic ALL)"
     << "(declare-const a Int)" << std::endl
     << "(declare-const b Int)" << std::endl
     << "(declare-const c Int)" << std::endl
     << "(declare-const d Int)" << std::endl
     << "(declare-const e Int)" << std::endl
     << "(declare-const g Int)" << std::endl
     << "(declare-const h Int)" << std::endl
     << "(declare-const i Int)" << std::endl
     << "(declare-const U Int)" << std::endl
     << "(declare-const f Int)" << std::endl
     << "(declare-const A Int)" << std::endl
     << "(declare-const B Int)" << std::endl
     << "(declare-const t Int)" << std::endl
     << "(declare-const n Int)" << std::endl;

  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to std::cout
    cmd.invoke(&slv, &sm, std::cout);
  }

  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(and (or (and (= a 0) (>= (+ U (* (- 1) f)) 0)) (and (= a 1) (< (+ U "
         "(* (- 1) f)) 0))) (or (and (= b 1) (>= U 1)) (and (= b 0) (< U 1))) "
         "(or (and (= c 1) (>= f 1)) (and (= c 0) (< f 1))) (or (and (= d 0) "
         "(>= (+ U (* (- 1) B)) 0)) (and (= d 1) (< (+ U (* (- 1) B)) 0))) (or "
         "(and (= e 1) (>= B 1)) (and (= e 0) (< B 1))) (or (and (= g 0) (>= "
         "(+ U (* (- 1) A)) 0)) (and (= g 1) (< (+ U (* (- 1) A)) 0))) (or "
         "(and (= h 1) (>= A 1)) (and (= h 0) (< A 1))) (or (and (= i 1) (or "
         "(and (>= (+ U (* (- 1) f)) 1) (or (and (>= (+ (* (- 1) U) f B) 0) "
         "(>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= "
         "(+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) "
         "U) f A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and "
         "(>= A 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)))) (and (>= "
         "0 1) (< (+ U (* (- 1) f)) 1) (or (and (>= (+ (* (- 1) U) f B) 0) (>= "
         "(+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= (+ "
         "A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) U) f "
         "A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= A "
         "0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)))) (and (>= B 1) "
         "(>= (+ A (* (- 1) B)) 1) (or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- "
         "1) B)) 1) (< (+ U (* (- 1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) "
         "1) (>= (+ U (* (- 1) f)) 1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A "
         "(* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- "
         "1) B)) 1) (>= (+ U (* (- 1) f)) 1))) (and (>= A 1) (< (+ A (* (- 1) "
         "B)) 1) (or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U "
         "(* (- 1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- "
         "1) f)) 1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< "
         "(+ U (* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U "
         "(* (- 1) f)) 1))))) (and (= i 0) (or (< (+ U (* (- 1) f)) 1) (and "
         "(or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- "
         "1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) "
         "1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< (+ U "
         "(* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- "
         "1) f)) 1)))) (or (< 0 1) (>= (+ U (* (- 1) f)) 1) (and (or (< (+ (* "
         "(- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) "
         "(or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (or (< "
         "(+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) "
         "1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)))) "
         "(or (< B 1) (< (+ A (* (- 1) B)) 1) (and (>= (+ (* (- 1) U) f B) 0) "
         "(>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= "
         "(+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) "
         "U) f A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and "
         "(>= A 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1))) (or (< A "
         "1) (>= (+ A (* (- 1) B)) 1) (and (>= (+ (* (- 1) U) f B) 0) (>= (+ A "
         "(* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= (+ A (* "
         "(- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) U) f A) "
         "0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= A 0) "
         "(< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1))))) (>= f 0) (>= U "
         "0) (>= B 0) (>= A 0))"
      << std::endl;
  parser2.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss2, "MyStream2");

  Term t = parser2.nextTerm();
  // Node dnf = LiaStarUtils::toDNF(*(t.d_node.get()), env);
}

TEST_F(TestLiaStarLazyUtils, toDnf8)
{
  TermManager tm;
  Solver slv(tm);
  SymbolManager sm(tm);
  Env env(tm.d_nm.get(), slv.d_originalOptions.get());
  // construct an input parser associated the solver above
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic ALL)"
     << "(declare-const a Int)" << std::endl
     << "(declare-const b Int)" << std::endl
     << "(declare-const c Int)" << std::endl
     << "(declare-const d Int)" << std::endl
     << "(declare-const e Int)" << std::endl
     << "(declare-const g Int)" << std::endl
     << "(declare-const h Int)" << std::endl
     << "(declare-const i Int)" << std::endl
     << "(declare-const U Int)" << std::endl
     << "(declare-const f Int)" << std::endl
     << "(declare-const A Int)" << std::endl
     << "(declare-const B Int)" << std::endl
     << "(declare-const t Int)" << std::endl
     << "(declare-const n Int)" << std::endl;

  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to std::cout
    cmd.invoke(&slv, &sm, std::cout);
  }

  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(or"
      << "(and (= i 1)"
      << "  (or"
      << "    (and"
      << "      (>= (+ U (* (- 1) f)) 1)"
      << "      (or"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f B) 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= B 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f A) 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= A 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))))"
      << "    (and (>= 0 1)"
      << "      (< (+ U (* (- 1) f)) 1)"
      << "      (or"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f B) 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= B 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f A) 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= A 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))))"
      << "    (and (>= B 1)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1)))"
      << "    (and (>= A 1)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1)))))"
      << "(and (= i 0)"
      << "  (or"
      << "    (< (+ U (* (- 1) f)) 1)"
      << "    (and"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))))"
      << "  (or (< 0 1)"
      << "    (>= (+ U (* (- 1) f)) 1)"
      << "    (and"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))))"
      << "  (or (< B 1)"
      << "    (< (+ A (* (- 1) B)) 1)"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f B) 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= B 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1))"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f A) 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= A 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1)))"
      << "  (or (< A 1)"
      << "    (>= (+ A (* (- 1) B)) 1)"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f B) 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= B 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1))"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f A) 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= A 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1)))))" << std::endl;
  parser2.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss2, "MyStream2");

  Term t = parser2.nextTerm();
  // Node dnf = LiaStarUtils::toDNF(*(t.d_node.get()), env);
}

TEST_F(TestLiaStarLazyUtils, getDisjunctUnsat)
{
  // The subsolver is seeded with (< x 0) and the nonnegativity constraint
  // (>= x 0), which together are unsatisfiable, so the returned disjunct must
  // be the false constant (the predicate is fully covered).
  Node xInt = nm->mkVar("x", intType);
  Node base = nm->mkNode(Kind::LT, xInt, zero);
  auto [engine, assertion] = mkSeededSubsolver(base, {xInt});
  Node disjunct = LiaStarUtils::getDisjunct(assertion, {}, {}, e, engine.get());
  ASSERT_EQ(falseConst, disjunct);
}

TEST_F(TestLiaStarLazyUtils, getDisjunctSatEquality)
{
  // (= x 5) is satisfiable together with the x >= 0 constraint. The returned
  // disjunct is a conjunction fixing every atom to its model value; it must
  // not be false and must itself be satisfiable.
  Node xInt = nm->mkVar("x", intType);
  Node five = nm->mkConstInt(Rational(5));
  Node base = nm->mkNode(Kind::EQUAL, xInt, five);
  auto [engine, assertion] = mkSeededSubsolver(base, {xInt});
  Node disjunct = LiaStarUtils::getDisjunct(assertion, {}, {}, e, engine.get());
  ASSERT_FALSE(disjunct.isNull());
  ASSERT_NE(falseConst, disjunct);
  Result result = LiaStarUtils::cvc5CheckSat({}, disjunct, e);
  ASSERT_EQ(Result::Status::SAT, result.getStatus());
}

TEST_F(TestLiaStarLazyUtils, getDisjunctSatInequalities)
{
  // (and (>= x 1) (>= y 2)) is satisfiable with the nonnegativity
  // constraints; the disjunct must be a satisfiable, non-false formula.
  Node xInt = nm->mkVar("x", intType);
  Node yInt = nm->mkVar("y", intType);
  Node geqX = nm->mkNode(Kind::GEQ, xInt, one);
  Node geqY = nm->mkNode(Kind::GEQ, yInt, two);
  Node base = nm->mkNode(Kind::AND, geqX, geqY);
  auto [engine, assertion] = mkSeededSubsolver(base, {xInt, yInt});
  Node disjunct = LiaStarUtils::getDisjunct(assertion, {}, {}, e, engine.get());
  ASSERT_FALSE(disjunct.isNull());
  ASSERT_NE(falseConst, disjunct);
  Result result = LiaStarUtils::cvc5CheckSat({}, disjunct, e);
  ASSERT_EQ(Result::Status::SAT, result.getStatus());
}

TEST_F(TestLiaStarLazyUtils, getDisjunctDisjunction)
{
  // (or (> x (+ y z)) (= x (+ y z))) is satisfiable with the nonnegativity
  // constraints. getDisjunct fixes every atom to its model value, selecting a
  // single convex cell of the satisfying region, so the result must be a
  // satisfiable, non-false formula that entails the original disjunction.
  Node xInt = nm->mkVar("x", intType);
  Node yInt = nm->mkVar("y", intType);
  Node zInt = nm->mkVar("z", intType);
  Node sum = nm->mkNode(Kind::ADD, yInt, zInt);
  Node gt = nm->mkNode(Kind::GT, xInt, sum);
  Node eq = nm->mkNode(Kind::EQUAL, xInt, sum);
  Node base = nm->mkNode(Kind::OR, gt, eq);
  auto [engine, assertion] = mkSeededSubsolver(base, {xInt, yInt, zInt});
  Node disjunct = LiaStarUtils::getDisjunct(assertion, {}, {}, e, engine.get());
  ASSERT_FALSE(disjunct.isNull());
  ASSERT_NE(falseConst, disjunct);
  Result result = LiaStarUtils::cvc5CheckSat({}, disjunct, e);
  ASSERT_EQ(Result::Status::SAT, result.getStatus());
  // The disjunct must entail the original disjunction: (and disjunct (not
  // base)) is unsatisfiable.
  Node entailment = nm->mkNode(Kind::AND, disjunct, base.notNode());
  Result entailmentResult =
      LiaStarUtils::cvc5CheckSat({xInt, yInt, zInt}, entailment, e);
  ASSERT_EQ(Result::Status::UNSAT, entailmentResult.getStatus());
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */

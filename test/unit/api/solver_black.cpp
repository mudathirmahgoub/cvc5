/*********************                                                        */
/*! \file solver_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mudathir Mohamed, Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Solver class of the  C++ API.
 **
 ** Black box testing of the Solver class of the  C++ API.
 **/

#include "base/configuration.h"
#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiBlackSolver : public TestApi
{
 protected:
  Solver * testSolver;
  // Sets up the test fixture.
  virtual void SetUp();

  // Tears down the test fixture.
  virtual void TearDown();
};

void TestApiBlackSolver::SetUp()
{
  std::cout<<"New Solver"<<std::endl;
  testSolver = new Solver();
}

void TestApiBlackSolver::TearDown()
{
  std::cout<<"Deleting Solver"<<std::endl;
  delete testSolver;
}


TEST_F(TestApiBlackSolver, recoverableException)
{
  testSolver->setOption("produce-models", "true");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x).notTerm());
  ASSERT_THROW(testSolver->getValue(x), CVC4ApiRecoverableException);
}

TEST_F(TestApiBlackSolver, supportsFloatingPoint)
{
  if (testSolver->supportsFloatingPoint())
  {
    ASSERT_NO_THROW(testSolver->mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
  }
  else
  {
    ASSERT_THROW(testSolver->mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN),
                 CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, getBooleanSort)
{
  ASSERT_NO_THROW(testSolver->getBooleanSort());
}

TEST_F(TestApiBlackSolver, getIntegerSort)
{
  ASSERT_NO_THROW(testSolver->getIntegerSort());
}

TEST_F(TestApiBlackSolver, getNullSort)
{
  ASSERT_NO_THROW(testSolver->getNullSort());
}

TEST_F(TestApiBlackSolver, getRealSort)
{
  ASSERT_NO_THROW(testSolver->getRealSort());
}

TEST_F(TestApiBlackSolver, getRegExpSort)
{
  ASSERT_NO_THROW(testSolver->getRegExpSort());
}

TEST_F(TestApiBlackSolver, getStringSort)
{
  ASSERT_NO_THROW(testSolver->getStringSort());
}

TEST_F(TestApiBlackSolver, getRoundingModeSort)
{
  if (testSolver->supportsFloatingPoint())
  {
    ASSERT_NO_THROW(testSolver->getRoundingModeSort());
  }
  else
  {
    ASSERT_THROW(testSolver->getRoundingModeSort(), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkArraySort)
{
  Sort boolSort = testSolver->getBooleanSort();
  Sort intSort = testSolver->getIntegerSort();
  Sort realSort = testSolver->getRealSort();
  Sort bvSort = testSolver->mkBitVectorSort(32);
  ASSERT_NO_THROW(testSolver->mkArraySort(boolSort, boolSort));
  ASSERT_NO_THROW(testSolver->mkArraySort(intSort, intSort));
  ASSERT_NO_THROW(testSolver->mkArraySort(realSort, realSort));
  ASSERT_NO_THROW(testSolver->mkArraySort(bvSort, bvSort));
  ASSERT_NO_THROW(testSolver->mkArraySort(boolSort, intSort));
  ASSERT_NO_THROW(testSolver->mkArraySort(realSort, bvSort));

  if (testSolver->supportsFloatingPoint())
  {
    Sort fpSort = testSolver->mkFloatingPointSort(3, 5);
    ASSERT_NO_THROW(testSolver->mkArraySort(fpSort, fpSort));
    ASSERT_NO_THROW(testSolver->mkArraySort(bvSort, fpSort));
  }

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkArraySort(boolSort, boolSort), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkBitVectorSort)
{
  ASSERT_NO_THROW(testSolver->mkBitVectorSort(32));
  ASSERT_THROW(testSolver->mkBitVectorSort(0), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, mkFloatingPointSort)
{
  if (testSolver->supportsFloatingPoint())
  {
    ASSERT_NO_THROW(testSolver->mkFloatingPointSort(4, 8));
    ASSERT_THROW(testSolver->mkFloatingPointSort(0, 8), CVC4ApiException);
    ASSERT_THROW(testSolver->mkFloatingPointSort(4, 0), CVC4ApiException);
  }
  else
  {
    ASSERT_THROW(testSolver->mkFloatingPointSort(4, 8), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkDatatypeSort)
{
  DatatypeDecl dtypeSpec = testSolver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = testSolver->mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", testSolver->getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = testSolver->mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  ASSERT_NO_THROW(testSolver->mkDatatypeSort(dtypeSpec));

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkDatatypeSort(dtypeSpec), CVC4ApiException);

  DatatypeDecl throwsDtypeSpec = testSolver->mkDatatypeDecl("list");
  ASSERT_THROW(testSolver->mkDatatypeSort(throwsDtypeSpec), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkDatatypeSorts)
{
  Solver* slv = new Solver();

  DatatypeDecl dtypeSpec1 = testSolver->mkDatatypeDecl("list1");
  DatatypeConstructorDecl cons1 = testSolver->mkDatatypeConstructorDecl("cons1");
  cons1.addSelector("head1", testSolver->getIntegerSort());
  dtypeSpec1.addConstructor(cons1);
  DatatypeConstructorDecl nil1 = testSolver->mkDatatypeConstructorDecl("nil1");
  dtypeSpec1.addConstructor(nil1);
  DatatypeDecl dtypeSpec2 = testSolver->mkDatatypeDecl("list2");
  DatatypeConstructorDecl cons2 = testSolver->mkDatatypeConstructorDecl("cons2");
  cons2.addSelector("head2", testSolver->getIntegerSort());
  dtypeSpec2.addConstructor(cons2);
  DatatypeConstructorDecl nil2 = testSolver->mkDatatypeConstructorDecl("nil2");
  dtypeSpec2.addConstructor(nil2);
  std::vector<DatatypeDecl> decls = {dtypeSpec1, dtypeSpec2};
  ASSERT_NO_THROW(testSolver->mkDatatypeSorts(decls));

  ASSERT_THROW(slv->mkDatatypeSorts(decls), CVC4ApiException);

  DatatypeDecl throwsDtypeSpec = testSolver->mkDatatypeDecl("list");
  std::vector<DatatypeDecl> throwsDecls = {throwsDtypeSpec};
  ASSERT_THROW(testSolver->mkDatatypeSorts(throwsDecls), CVC4ApiException);

  /* with unresolved sorts */
  Sort unresList = testSolver->mkUninterpretedSort("ulist");
  std::set<Sort> unresSorts = {unresList};
  DatatypeDecl ulist = testSolver->mkDatatypeDecl("ulist");
  DatatypeConstructorDecl ucons = testSolver->mkDatatypeConstructorDecl("ucons");
  ucons.addSelector("car", unresList);
  ucons.addSelector("cdr", unresList);
  ulist.addConstructor(ucons);
  DatatypeConstructorDecl unil = testSolver->mkDatatypeConstructorDecl("unil");
  ulist.addConstructor(unil);
  std::vector<DatatypeDecl> udecls = {ulist};
  ASSERT_NO_THROW(testSolver->mkDatatypeSorts(udecls, unresSorts));

  ASSERT_THROW(slv->mkDatatypeSorts(udecls, unresSorts), CVC4ApiException);
  delete slv;
  /* Note: More tests are in datatype_api_black. */
}

TEST_F(TestApiBlackSolver, mkFunctionSort)
{
  ASSERT_NO_THROW(testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                          testSolver->getIntegerSort()));
  Sort funSort = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                         testSolver->getIntegerSort());
  ASSERT_THROW(testSolver->mkFunctionSort(funSort, testSolver->getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(testSolver->mkFunctionSort(testSolver->getIntegerSort(), funSort),
               CVC4ApiException);
  ASSERT_NO_THROW(testSolver->mkFunctionSort(
      {testSolver->mkUninterpretedSort("u"), testSolver->getIntegerSort()},
      testSolver->getIntegerSort()));
  Sort funSort2 = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                          testSolver->getIntegerSort());
  ASSERT_THROW(
      testSolver->mkFunctionSort({funSort2, testSolver->mkUninterpretedSort("u")},
                              testSolver->getIntegerSort()),
      CVC4ApiException);
  ASSERT_THROW(testSolver->mkFunctionSort({testSolver->getIntegerSort(),
                                        testSolver->mkUninterpretedSort("u")},
                                       funSort2),
               CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                  testSolver->getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(slv->mkFunctionSort(slv->mkUninterpretedSort("u"),
                                  testSolver->getIntegerSort()),
               CVC4ApiException);
  std::vector<Sort> sorts1 = {testSolver->getBooleanSort(),
                              slv->getIntegerSort(),
                              testSolver->getIntegerSort()};
  std::vector<Sort> sorts2 = {slv->getBooleanSort(), slv->getIntegerSort()};
  ASSERT_NO_THROW(slv->mkFunctionSort(sorts2, slv->getIntegerSort()));
  ASSERT_THROW(slv->mkFunctionSort(sorts1, slv->getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(slv->mkFunctionSort(sorts2, testSolver->getIntegerSort()),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkParamSort)
{
  ASSERT_NO_THROW(testSolver->mkParamSort("T"));
  ASSERT_NO_THROW(testSolver->mkParamSort(""));
}

TEST_F(TestApiBlackSolver, mkPredicateSort)
{
  ASSERT_NO_THROW(testSolver->mkPredicateSort({testSolver->getIntegerSort()}));
  ASSERT_THROW(testSolver->mkPredicateSort({}), CVC4ApiException);
  Sort funSort = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                         testSolver->getIntegerSort());
  ASSERT_THROW(testSolver->mkPredicateSort({testSolver->getIntegerSort(), funSort}),
               CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkPredicateSort({testSolver->getIntegerSort()}),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkRecordSort)
{
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", testSolver->getBooleanSort()),
      std::make_pair("bv", testSolver->mkBitVectorSort(8)),
      std::make_pair("i", testSolver->getIntegerSort())};
  std::vector<std::pair<std::string, Sort>> empty;
  ASSERT_NO_THROW(testSolver->mkRecordSort(fields));
  ASSERT_NO_THROW(testSolver->mkRecordSort(empty));
  Sort recSort = testSolver->mkRecordSort(fields);
  ASSERT_NO_THROW(recSort.getDatatype());

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkRecordSort(fields), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkSetSort)
{
  ASSERT_NO_THROW(testSolver->mkSetSort(testSolver->getBooleanSort()));
  ASSERT_NO_THROW(testSolver->mkSetSort(testSolver->getIntegerSort()));
  ASSERT_NO_THROW(testSolver->mkSetSort(testSolver->mkBitVectorSort(4)));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkSetSort(testSolver->mkBitVectorSort(4)), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkBagSort)
{
  ASSERT_NO_THROW(testSolver->mkBagSort(testSolver->getBooleanSort()));
  ASSERT_NO_THROW(testSolver->mkBagSort(testSolver->getIntegerSort()));
  ASSERT_NO_THROW(testSolver->mkBagSort(testSolver->mkBitVectorSort(4)));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkBagSort(testSolver->mkBitVectorSort(4)), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkSequenceSort)
{
  ASSERT_NO_THROW(testSolver->mkSequenceSort(testSolver->getBooleanSort()));
  ASSERT_NO_THROW(testSolver->mkSequenceSort(
      testSolver->mkSequenceSort(testSolver->getIntegerSort())));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkSequenceSort(testSolver->getIntegerSort()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkUninterpretedSort)
{
  ASSERT_NO_THROW(testSolver->mkUninterpretedSort("u"));
  ASSERT_NO_THROW(testSolver->mkUninterpretedSort(""));
}

TEST_F(TestApiBlackSolver, mkSortConstructorSort)
{
  ASSERT_NO_THROW(testSolver->mkSortConstructorSort("s", 2));
  ASSERT_NO_THROW(testSolver->mkSortConstructorSort("", 2));
  ASSERT_THROW(testSolver->mkSortConstructorSort("", 0), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, mkTupleSort)
{
  ASSERT_NO_THROW(testSolver->mkTupleSort({testSolver->getIntegerSort()}));
  Sort funSort = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                         testSolver->getIntegerSort());
  ASSERT_THROW(testSolver->mkTupleSort({testSolver->getIntegerSort(), funSort}),
               CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkTupleSort({testSolver->getIntegerSort()}), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkBitVector)
{
  uint32_t size0 = 0, size1 = 8, size2 = 32, val1 = 2;
  uint64_t val2 = 2;
  ASSERT_NO_THROW(testSolver->mkBitVector(size1, val1));
  ASSERT_NO_THROW(testSolver->mkBitVector(size2, val2));
  ASSERT_NO_THROW(testSolver->mkBitVector("1010", 2));
  ASSERT_NO_THROW(testSolver->mkBitVector("1010", 10));
  ASSERT_NO_THROW(testSolver->mkBitVector("1234", 10));
  ASSERT_NO_THROW(testSolver->mkBitVector("1010", 16));
  ASSERT_NO_THROW(testSolver->mkBitVector("a09f", 16));
  ASSERT_NO_THROW(testSolver->mkBitVector(8, "-127", 10));
  ASSERT_THROW(testSolver->mkBitVector(size0, val1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector(size0, val2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector("", 2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector("10", 3), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector("20", 2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector(8, "101010101", 2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkBitVector(8, "-256", 10), CVC4ApiException);
  ASSERT_EQ(testSolver->mkBitVector("1010", 2), testSolver->mkBitVector("10", 10));
  ASSERT_EQ(testSolver->mkBitVector("1010", 2), testSolver->mkBitVector("a", 16));
  ASSERT_EQ(testSolver->mkBitVector(8, "01010101", 2).toString(), "#b01010101");
  ASSERT_EQ(testSolver->mkBitVector(8, "F", 16).toString(), "#b00001111");
  ASSERT_EQ(testSolver->mkBitVector(8, "-1", 10),
            testSolver->mkBitVector(8, "FF", 16));
}

TEST_F(TestApiBlackSolver, mkVar)
{
  Sort boolSort = testSolver->getBooleanSort();
  Sort intSort = testSolver->getIntegerSort();
  Sort funSort = testSolver->mkFunctionSort(intSort, boolSort);
  ASSERT_NO_THROW(testSolver->mkVar(boolSort));
  ASSERT_NO_THROW(testSolver->mkVar(funSort));
  ASSERT_NO_THROW(testSolver->mkVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(testSolver->mkVar(funSort, ""));
  ASSERT_THROW(testSolver->mkVar(Sort()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkVar(Sort(), "a"), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkVar(boolSort, "x"), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkBoolean)
{
  ASSERT_NO_THROW(testSolver->mkBoolean(true));
  ASSERT_NO_THROW(testSolver->mkBoolean(false));
}

TEST_F(TestApiBlackSolver, mkRoundingMode)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));
  }
  else
  {
    ASSERT_THROW(testSolver->mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO),
                 CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkUninterpretedConst)
{
  ASSERT_NO_THROW(testSolver->mkUninterpretedConst(testSolver->getBooleanSort(), 1));
  ASSERT_THROW(testSolver->mkUninterpretedConst(Sort(), 1), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkUninterpretedConst(testSolver->getBooleanSort(), 1),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkAbstractValue)
{
  ASSERT_NO_THROW(testSolver->mkAbstractValue(std::string("1")));
  ASSERT_THROW(testSolver->mkAbstractValue(std::string("0")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkAbstractValue(std::string("-1")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkAbstractValue(std::string("1.2")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkAbstractValue("1/2"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkAbstractValue("asdf"), CVC4ApiException);

  ASSERT_NO_THROW(testSolver->mkAbstractValue((uint32_t)1));
  ASSERT_NO_THROW(testSolver->mkAbstractValue((int32_t)1));
  ASSERT_NO_THROW(testSolver->mkAbstractValue((uint64_t)1));
  ASSERT_NO_THROW(testSolver->mkAbstractValue((int64_t)1));
  ASSERT_NO_THROW(testSolver->mkAbstractValue((int32_t)-1));
  ASSERT_NO_THROW(testSolver->mkAbstractValue((int64_t)-1));
  ASSERT_THROW(testSolver->mkAbstractValue(0), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, mkFloatingPoint)
{
  Term t1 = testSolver->mkBitVector(8);
  Term t2 = testSolver->mkBitVector(4);
  Term t3 = testSolver->mkInteger(2);
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkFloatingPoint(3, 5, t1));
  }
  else
  {
    ASSERT_THROW(testSolver->mkFloatingPoint(3, 5, t1), CVC4ApiException);
  }
  ASSERT_THROW(testSolver->mkFloatingPoint(0, 5, Term()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkFloatingPoint(0, 5, t1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkFloatingPoint(3, 0, t1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkFloatingPoint(3, 5, t2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkFloatingPoint(3, 5, t2), CVC4ApiException);

  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    Solver* slv = new Solver();
    ASSERT_THROW(slv->mkFloatingPoint(3, 5, t1), CVC4ApiException);
    delete slv;
  }
}

TEST_F(TestApiBlackSolver, mkEmptySet)
{
  Solver* slv = new Solver();
  Sort s = testSolver->mkSetSort(testSolver->getBooleanSort());
  ASSERT_NO_THROW(testSolver->mkEmptySet(Sort()));
  ASSERT_NO_THROW(testSolver->mkEmptySet(s));
  ASSERT_THROW(testSolver->mkEmptySet(testSolver->getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv->mkEmptySet(s), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkEmptyBag)
{
  Solver* slv = new Solver();
  Sort s = testSolver->mkBagSort(testSolver->getBooleanSort());
  ASSERT_NO_THROW(testSolver->mkEmptyBag(Sort()));
  ASSERT_NO_THROW(testSolver->mkEmptyBag(s));
  ASSERT_THROW(testSolver->mkEmptyBag(testSolver->getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv->mkEmptyBag(s), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkEmptySequence)
{
  Solver* slv = new Solver();
  Sort s = testSolver->mkSequenceSort(testSolver->getBooleanSort());
  ASSERT_NO_THROW(testSolver->mkEmptySequence(s));
  ASSERT_NO_THROW(testSolver->mkEmptySequence(testSolver->getBooleanSort()));
  ASSERT_THROW(slv->mkEmptySequence(s), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkFalse)
{
  ASSERT_NO_THROW(testSolver->mkFalse());
  ASSERT_NO_THROW(testSolver->mkFalse());
}

TEST_F(TestApiBlackSolver, mkNaN)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkNaN(3, 5));
  }
  else
  {
    ASSERT_THROW(testSolver->mkNaN(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkNegZero)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkNegZero(3, 5));
  }
  else
  {
    ASSERT_THROW(testSolver->mkNegZero(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkNegInf)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkNegInf(3, 5));
  }
  else
  {
    ASSERT_THROW(testSolver->mkNegInf(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkPosInf)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkPosInf(3, 5));
  }
  else
  {
    ASSERT_THROW(testSolver->mkPosInf(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkPosZero)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(testSolver->mkPosZero(3, 5));
  }
  else
  {
    ASSERT_THROW(testSolver->mkPosZero(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiBlackSolver, mkOp)
{
  // mkOp(Kind kind, Kind k)
  ASSERT_THROW(testSolver->mkOp(BITVECTOR_EXTRACT, EQUAL), CVC4ApiException);

  // mkOp(Kind kind, const std::string& arg)
  ASSERT_NO_THROW(testSolver->mkOp(RECORD_UPDATE, "asdf"));
  ASSERT_NO_THROW(testSolver->mkOp(DIVISIBLE, "2147483648"));
  ASSERT_THROW(testSolver->mkOp(BITVECTOR_EXTRACT, "asdf"), CVC4ApiException);

  // mkOp(Kind kind, uint32_t arg)
  ASSERT_NO_THROW(testSolver->mkOp(DIVISIBLE, 1));
  ASSERT_NO_THROW(testSolver->mkOp(BITVECTOR_ROTATE_LEFT, 1));
  ASSERT_NO_THROW(testSolver->mkOp(BITVECTOR_ROTATE_RIGHT, 1));
  ASSERT_THROW(testSolver->mkOp(BITVECTOR_EXTRACT, 1), CVC4ApiException);

  // mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
  ASSERT_NO_THROW(testSolver->mkOp(BITVECTOR_EXTRACT, 1, 1));
  ASSERT_THROW(testSolver->mkOp(DIVISIBLE, 1, 2), CVC4ApiException);

  // mkOp(Kind kind, std::vector<uint32_t> args)
  std::vector<uint32_t> args = {1, 2, 2};
  ASSERT_NO_THROW(testSolver->mkOp(TUPLE_PROJECT, args));
}

TEST_F(TestApiBlackSolver, mkPi) { ASSERT_NO_THROW(testSolver->mkPi()); }

TEST_F(TestApiBlackSolver, mkInteger)
{
  ASSERT_NO_THROW(testSolver->mkInteger("123"));
  ASSERT_THROW(testSolver->mkInteger("1.23"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("1/23"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("12/3"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(".2"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("2."), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(""), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("asdf"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("1.2/3"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("."), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("/"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("2/"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger("/2"), CVC4ApiException);

  ASSERT_NO_THROW(testSolver->mkReal(std::string("123")));
  ASSERT_THROW(testSolver->mkInteger(std::string("1.23")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("1/23")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("12/3")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string(".2")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("2.")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("asdf")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("1.2/3")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string(".")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("/")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("2/")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkInteger(std::string("/2")), CVC4ApiException);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  ASSERT_NO_THROW(testSolver->mkInteger(val1));
  ASSERT_NO_THROW(testSolver->mkInteger(val2));
  ASSERT_NO_THROW(testSolver->mkInteger(val3));
  ASSERT_NO_THROW(testSolver->mkInteger(val4));
  ASSERT_NO_THROW(testSolver->mkInteger(val4));
}

TEST_F(TestApiBlackSolver, mkReal)
{
  ASSERT_NO_THROW(testSolver->mkReal("123"));
  ASSERT_NO_THROW(testSolver->mkReal("1.23"));
  ASSERT_NO_THROW(testSolver->mkReal("1/23"));
  ASSERT_NO_THROW(testSolver->mkReal("12/3"));
  ASSERT_NO_THROW(testSolver->mkReal(".2"));
  ASSERT_NO_THROW(testSolver->mkReal("2."));
  ASSERT_THROW(testSolver->mkReal(""), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("asdf"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("1.2/3"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("."), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("/"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("2/"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal("/2"), CVC4ApiException);

  ASSERT_NO_THROW(testSolver->mkReal(std::string("123")));
  ASSERT_NO_THROW(testSolver->mkReal(std::string("1.23")));
  ASSERT_NO_THROW(testSolver->mkReal(std::string("1/23")));
  ASSERT_NO_THROW(testSolver->mkReal(std::string("12/3")));
  ASSERT_NO_THROW(testSolver->mkReal(std::string(".2")));
  ASSERT_NO_THROW(testSolver->mkReal(std::string("2.")));
  ASSERT_THROW(testSolver->mkReal(std::string("")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string("asdf")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string("1.2/3")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string(".")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string("/")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string("2/")), CVC4ApiException);
  ASSERT_THROW(testSolver->mkReal(std::string("/2")), CVC4ApiException);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  ASSERT_NO_THROW(testSolver->mkReal(val1));
  ASSERT_NO_THROW(testSolver->mkReal(val2));
  ASSERT_NO_THROW(testSolver->mkReal(val3));
  ASSERT_NO_THROW(testSolver->mkReal(val4));
  ASSERT_NO_THROW(testSolver->mkReal(val4));
  ASSERT_NO_THROW(testSolver->mkReal(val1, val1));
  ASSERT_NO_THROW(testSolver->mkReal(val2, val2));
  ASSERT_NO_THROW(testSolver->mkReal(val3, val3));
  ASSERT_NO_THROW(testSolver->mkReal(val4, val4));
}

TEST_F(TestApiBlackSolver, mkRegexpEmpty)
{
  Sort strSort = testSolver->getStringSort();
  Term s = testSolver->mkConst(strSort, "s");
  ASSERT_NO_THROW(
      testSolver->mkTerm(STRING_IN_REGEXP, s, testSolver->mkRegexpEmpty()));
}

TEST_F(TestApiBlackSolver, mkRegexpSigma)
{
  Sort strSort = testSolver->getStringSort();
  Term s = testSolver->mkConst(strSort, "s");
  ASSERT_NO_THROW(
      testSolver->mkTerm(STRING_IN_REGEXP, s, testSolver->mkRegexpSigma()));
}

TEST_F(TestApiBlackSolver, mkSepNil)
{
  ASSERT_NO_THROW(testSolver->mkSepNil(testSolver->getBooleanSort()));
  ASSERT_THROW(testSolver->mkSepNil(Sort()), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkSepNil(testSolver->getIntegerSort()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkString)
{
  ASSERT_NO_THROW(testSolver->mkString(""));
  ASSERT_NO_THROW(testSolver->mkString("asdfasdf"));
  ASSERT_EQ(testSolver->mkString("asdf\\nasdf").toString(),
            "\"asdf\\u{5c}nasdf\"");
  ASSERT_EQ(testSolver->mkString("asdf\\u{005c}nasdf", true).toString(),
            "\"asdf\\u{5c}nasdf\"");
}

TEST_F(TestApiBlackSolver, mkChar)
{
  ASSERT_NO_THROW(testSolver->mkChar(std::string("0123")));
  ASSERT_NO_THROW(testSolver->mkChar("aA"));
  ASSERT_THROW(testSolver->mkChar(""), CVC4ApiException);
  ASSERT_THROW(testSolver->mkChar("0g0"), CVC4ApiException);
  ASSERT_THROW(testSolver->mkChar("100000"), CVC4ApiException);
  ASSERT_EQ(testSolver->mkChar("abc"), testSolver->mkChar("ABC"));
}

TEST_F(TestApiBlackSolver, mkTerm)
{
  Sort bv32 = testSolver->mkBitVectorSort(32);
  Term a = testSolver->mkConst(bv32, "a");
  Term b = testSolver->mkConst(bv32, "b");
  std::vector<Term> v1 = {a, b};
  std::vector<Term> v2 = {a, Term()};
  std::vector<Term> v3 = {a, testSolver->mkTrue()};
  std::vector<Term> v4 = {testSolver->mkInteger(1), testSolver->mkInteger(2)};
  std::vector<Term> v5 = {testSolver->mkInteger(1), Term()};
  std::vector<Term> v6 = {};
  Solver* slv = new Solver();

  // mkTerm(Kind kind) const
  ASSERT_NO_THROW(testSolver->mkTerm(PI));
  ASSERT_NO_THROW(testSolver->mkTerm(REGEXP_EMPTY));
  ASSERT_NO_THROW(testSolver->mkTerm(REGEXP_SIGMA));
  ASSERT_THROW(testSolver->mkTerm(CONST_BITVECTOR), CVC4ApiException);

  // mkTerm(Kind kind, Term child) const
  ASSERT_NO_THROW(testSolver->mkTerm(NOT, testSolver->mkTrue()));
  ASSERT_THROW(testSolver->mkTerm(NOT, Term()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(NOT, a), CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(NOT, testSolver->mkTrue()), CVC4ApiException);

  // mkTerm(Kind kind, Term child1, Term child2) const
  ASSERT_NO_THROW(testSolver->mkTerm(EQUAL, a, b));
  ASSERT_THROW(testSolver->mkTerm(EQUAL, Term(), b), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(EQUAL, a, Term()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(EQUAL, a, testSolver->mkTrue()), CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(EQUAL, a, b), CVC4ApiException);

  // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
  ASSERT_NO_THROW(testSolver->mkTerm(
      ITE, testSolver->mkTrue(), testSolver->mkTrue(), testSolver->mkTrue()));
  ASSERT_THROW(
      testSolver->mkTerm(ITE, Term(), testSolver->mkTrue(), testSolver->mkTrue()),
      CVC4ApiException);
  ASSERT_THROW(
      testSolver->mkTerm(ITE, testSolver->mkTrue(), Term(), testSolver->mkTrue()),
      CVC4ApiException);
  ASSERT_THROW(
      testSolver->mkTerm(ITE, testSolver->mkTrue(), testSolver->mkTrue(), Term()),
      CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(ITE, testSolver->mkTrue(), testSolver->mkTrue(), b),
               CVC4ApiException);
  ASSERT_THROW(
      slv->mkTerm(ITE, testSolver->mkTrue(), testSolver->mkTrue(), testSolver->mkTrue()),
      CVC4ApiException);

  // mkTerm(Kind kind, const std::vector<Term>& children) const
  ASSERT_NO_THROW(testSolver->mkTerm(EQUAL, v1));
  ASSERT_THROW(testSolver->mkTerm(EQUAL, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(EQUAL, v3), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(DISTINCT, v6), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkTermFromOp)
{
  Sort bv32 = testSolver->mkBitVectorSort(32);
  Term a = testSolver->mkConst(bv32, "a");
  Term b = testSolver->mkConst(bv32, "b");
  std::vector<Term> v1 = {testSolver->mkInteger(1), testSolver->mkInteger(2)};
  std::vector<Term> v2 = {testSolver->mkInteger(1), Term()};
  std::vector<Term> v3 = {};
  std::vector<Term> v4 = {testSolver->mkInteger(5)};
  Solver* slv = new Solver();

  // simple operator terms
  Op opterm1 = testSolver->mkOp(BITVECTOR_EXTRACT, 2, 1);
  Op opterm2 = testSolver->mkOp(DIVISIBLE, 1);

  // list datatype
  Sort sort = testSolver->mkParamSort("T");
  DatatypeDecl listDecl = testSolver->mkDatatypeDecl("paramlist", sort);
  DatatypeConstructorDecl cons = testSolver->mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = testSolver->mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = testSolver->mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{testSolver->getIntegerSort()});
  Term c = testSolver->mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();

  // list datatype constructor and selector operator terms
  Term consTerm1 = list.getConstructorTerm("cons");
  Term consTerm2 = list.getConstructor("cons").getConstructorTerm();
  Term nilTerm1 = list.getConstructorTerm("nil");
  Term nilTerm2 = list.getConstructor("nil").getConstructorTerm();
  Term headTerm1 = list["cons"].getSelectorTerm("head");
  Term headTerm2 = list["cons"].getSelector("head").getSelectorTerm();
  Term tailTerm1 = list["cons"].getSelectorTerm("tail");
  Term tailTerm2 = list["cons"]["tail"].getSelectorTerm();

  // mkTerm(Op op, Term term) const
  ASSERT_NO_THROW(testSolver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1));
  ASSERT_NO_THROW(testSolver->mkTerm(APPLY_CONSTRUCTOR, nilTerm2));
  ASSERT_THROW(testSolver->mkTerm(APPLY_SELECTOR, nilTerm1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(APPLY_SELECTOR, consTerm1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(APPLY_CONSTRUCTOR, consTerm2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(APPLY_SELECTOR, headTerm1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm1), CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(APPLY_CONSTRUCTOR, nilTerm1), CVC4ApiException);

  // mkTerm(Op op, Term child) const
  ASSERT_NO_THROW(testSolver->mkTerm(opterm1, a));
  ASSERT_NO_THROW(testSolver->mkTerm(opterm2, testSolver->mkInteger(1)));
  ASSERT_NO_THROW(testSolver->mkTerm(APPLY_SELECTOR, headTerm1, c));
  ASSERT_NO_THROW(testSolver->mkTerm(APPLY_SELECTOR, tailTerm2, c));
  ASSERT_THROW(testSolver->mkTerm(opterm2, a), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm1, Term()), CVC4ApiException);
  ASSERT_THROW(
      testSolver->mkTerm(APPLY_CONSTRUCTOR, consTerm1, testSolver->mkInteger(0)),
      CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(opterm1, a), CVC4ApiException);

  // mkTerm(Op op, Term child1, Term child2) const
  ASSERT_NO_THROW(
      testSolver->mkTerm(APPLY_CONSTRUCTOR,
                      consTerm1,
                      testSolver->mkInteger(0),
                      testSolver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
  ASSERT_THROW(
      testSolver->mkTerm(opterm2, testSolver->mkInteger(1), testSolver->mkInteger(2)),
      CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm1, a, b), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm2, testSolver->mkInteger(1), Term()),
               CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm2, Term(), testSolver->mkInteger(1)),
               CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(APPLY_CONSTRUCTOR,
                          consTerm1,
                          testSolver->mkInteger(0),
                          testSolver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1)),
               CVC4ApiException);

  // mkTerm(Op op, Term child1, Term child2, Term child3) const
  ASSERT_THROW(testSolver->mkTerm(opterm1, a, b, a), CVC4ApiException);
  ASSERT_THROW(
      testSolver->mkTerm(
          opterm2, testSolver->mkInteger(1), testSolver->mkInteger(1), Term()),
      CVC4ApiException);

  // mkTerm(Op op, const std::vector<Term>& children) const
  ASSERT_NO_THROW(testSolver->mkTerm(opterm2, v4));
  ASSERT_THROW(testSolver->mkTerm(opterm2, v1), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm2, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(opterm2, v3), CVC4ApiException);
  ASSERT_THROW(slv->mkTerm(opterm2, v4), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkTrue)
{
  ASSERT_NO_THROW(testSolver->mkTrue());
  ASSERT_NO_THROW(testSolver->mkTrue());
}

TEST_F(TestApiBlackSolver, mkTuple)
{
  ASSERT_NO_THROW(testSolver->mkTuple({testSolver->mkBitVectorSort(3)},
                                   {testSolver->mkBitVector("101", 2)}));
  ASSERT_NO_THROW(
      testSolver->mkTuple({testSolver->getRealSort()}, {testSolver->mkInteger("5")}));

  ASSERT_THROW(testSolver->mkTuple({}, {testSolver->mkBitVector("101", 2)}),
               CVC4ApiException);
  ASSERT_THROW(testSolver->mkTuple({testSolver->mkBitVectorSort(4)},
                                {testSolver->mkBitVector("101", 2)}),
               CVC4ApiException);
  ASSERT_THROW(
      testSolver->mkTuple({testSolver->getIntegerSort()}, {testSolver->mkReal("5.3")}),
      CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(
      slv->mkTuple({testSolver->mkBitVectorSort(3)}, {slv->mkBitVector("101", 2)}),
      CVC4ApiException);
  ASSERT_THROW(
      slv->mkTuple({slv->mkBitVectorSort(3)}, {testSolver->mkBitVector("101", 2)}),
      CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkUniverseSet)
{
  ASSERT_NO_THROW(testSolver->mkUniverseSet(testSolver->getBooleanSort()));
  ASSERT_THROW(testSolver->mkUniverseSet(Sort()), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkUniverseSet(testSolver->getBooleanSort()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkConst)
{
  Sort boolSort = testSolver->getBooleanSort();
  Sort intSort = testSolver->getIntegerSort();
  Sort funSort = testSolver->mkFunctionSort(intSort, boolSort);
  ASSERT_NO_THROW(testSolver->mkConst(boolSort));
  ASSERT_NO_THROW(testSolver->mkConst(funSort));
  ASSERT_NO_THROW(testSolver->mkConst(boolSort, std::string("b")));
  ASSERT_NO_THROW(testSolver->mkConst(intSort, std::string("i")));
  ASSERT_NO_THROW(testSolver->mkConst(funSort, "f"));
  ASSERT_NO_THROW(testSolver->mkConst(funSort, ""));
  ASSERT_THROW(testSolver->mkConst(Sort()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkConst(Sort(), "a"), CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkConst(boolSort), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkConstArray)
{
  Sort intSort = testSolver->getIntegerSort();
  Sort arrSort = testSolver->mkArraySort(intSort, intSort);
  Term zero = testSolver->mkInteger(0);
  Term constArr = testSolver->mkConstArray(arrSort, zero);

  ASSERT_NO_THROW(testSolver->mkConstArray(arrSort, zero));
  ASSERT_THROW(testSolver->mkConstArray(Sort(), zero), CVC4ApiException);
  ASSERT_THROW(testSolver->mkConstArray(arrSort, Term()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkConstArray(arrSort, testSolver->mkBitVector(1, 1)),
               CVC4ApiException);
  ASSERT_THROW(testSolver->mkConstArray(intSort, zero), CVC4ApiException);
  Solver* slv = new Solver();
  Term zero2 = slv->mkInteger(0);
  Sort arrSort2 = slv->mkArraySort(slv->getIntegerSort(), slv->getIntegerSort());
  ASSERT_THROW(slv->mkConstArray(arrSort2, zero), CVC4ApiException);
  ASSERT_THROW(slv->mkConstArray(arrSort, zero2), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, declareDatatype)
{
  DatatypeConstructorDecl nil = testSolver->mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  ASSERT_NO_THROW(testSolver->declareDatatype(std::string("a"), ctors1));
  DatatypeConstructorDecl cons = testSolver->mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil2 = testSolver->mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil2};
  ASSERT_NO_THROW(testSolver->declareDatatype(std::string("b"), ctors2));
  DatatypeConstructorDecl cons2 = testSolver->mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil3 = testSolver->mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors3 = {cons2, nil3};
  ASSERT_NO_THROW(testSolver->declareDatatype(std::string(""), ctors3));
  std::vector<DatatypeConstructorDecl> ctors4;
  ASSERT_THROW(testSolver->declareDatatype(std::string("c"), ctors4),
               CVC4ApiException);
  ASSERT_THROW(testSolver->declareDatatype(std::string(""), ctors4),
               CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->declareDatatype(std::string("a"), ctors1), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, declareFun)
{
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                         testSolver->getIntegerSort());
  ASSERT_NO_THROW(testSolver->declareFun("f1", {}, bvSort));
  ASSERT_NO_THROW(
      testSolver->declareFun("f3", {bvSort, testSolver->getIntegerSort()}, bvSort));
  ASSERT_THROW(testSolver->declareFun("f2", {}, funSort), CVC4ApiException);
  ASSERT_THROW(testSolver->declareFun("f4", {bvSort, funSort}, bvSort),
               CVC4ApiException);
  ASSERT_THROW(testSolver->declareFun("f5", {bvSort, bvSort}, funSort),
               CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->declareFun("f1", {}, bvSort), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, declareSort)
{
  ASSERT_NO_THROW(testSolver->declareSort("s", 0));
  ASSERT_NO_THROW(testSolver->declareSort("s", 2));
  ASSERT_NO_THROW(testSolver->declareSort("", 2));
}

TEST_F(TestApiBlackSolver, defineSort)
{
  Sort sortVar0 = testSolver->mkParamSort("T0");
  Sort sortVar1 = testSolver->mkParamSort("T1");
  Sort intSort = testSolver->getIntegerSort();
  Sort realSort = testSolver->getRealSort();
  Sort arraySort0 = testSolver->mkArraySort(sortVar0, sortVar0);
  Sort arraySort1 = testSolver->mkArraySort(sortVar0, sortVar1);
  // Now create instantiations of the defined sorts
  ASSERT_NO_THROW(arraySort0.substitute(sortVar0, intSort));
  ASSERT_NO_THROW(
      arraySort1.substitute({sortVar0, sortVar1}, {intSort, realSort}));
}

TEST_F(TestApiBlackSolver, defineFun)
{
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort1 = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                          testSolver->getIntegerSort());
  Term b1 = testSolver->mkVar(bvSort, "b1");
  Term b11 = testSolver->mkVar(bvSort, "b1");
  Term b2 = testSolver->mkVar(testSolver->getIntegerSort(), "b2");
  Term b3 = testSolver->mkVar(funSort2, "b3");
  Term v1 = testSolver->mkConst(bvSort, "v1");
  Term v2 = testSolver->mkConst(testSolver->getIntegerSort(), "v2");
  Term v3 = testSolver->mkConst(funSort2, "v3");
  Term f1 = testSolver->mkConst(funSort1, "f1");
  Term f2 = testSolver->mkConst(funSort2, "f2");
  Term f3 = testSolver->mkConst(bvSort, "f3");
  ASSERT_NO_THROW(testSolver->defineFun("f", {}, bvSort, v1));
  ASSERT_NO_THROW(testSolver->defineFun("ff", {b1, b2}, bvSort, v1));
  ASSERT_NO_THROW(testSolver->defineFun(f1, {b1, b11}, v1));
  ASSERT_THROW(testSolver->defineFun("ff", {v1, b2}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun("fff", {b1}, bvSort, v3), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun("ffff", {b1}, funSort2, v3),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun("fffff", {b1, b3}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f1, {v1, b11}, v1), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f1, {b1}, v1), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f1, {b1, b11}, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f1, {b1, b11}, v3), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f2, {b1}, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFun(f3, {b1}, v1), CVC4ApiException);

  Solver* slv = new Solver();
  Sort bvSort2 = slv->mkBitVectorSort(32);
  Term v12 = slv->mkConst(bvSort2, "v1");
  Term b12 = slv->mkVar(bvSort2, "b1");
  Term b22 = slv->mkVar(slv->getIntegerSort(), "b2");
  ASSERT_THROW(slv->defineFun("f", {}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv->defineFun("f", {}, bvSort2, v1), CVC4ApiException);
  ASSERT_THROW(slv->defineFun("ff", {b1, b22}, bvSort2, v12), CVC4ApiException);
  ASSERT_THROW(slv->defineFun("ff", {b12, b2}, bvSort2, v12), CVC4ApiException);
  ASSERT_THROW(slv->defineFun("ff", {b12, b22}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv->defineFun("ff", {b12, b22}, bvSort2, v1), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, defineFunGlobal)
{
  Sort bSort = testSolver->getBooleanSort();
  Sort fSort = testSolver->mkFunctionSort(bSort, bSort);

  Term bTrue = testSolver->mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = testSolver->defineFun("f", {}, bSort, bTrue, true);
  Term b = testSolver->mkVar(bSort, "b");
  Term gSym = testSolver->mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = testSolver->defineFun(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  testSolver->assertFormula(testSolver->mkTerm(
      OR, f.notTerm(), testSolver->mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
  testSolver->resetAssertions();
  // (assert (or (not f) (not (g true))))
  testSolver->assertFormula(testSolver->mkTerm(
      OR, f.notTerm(), testSolver->mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, defineFunRec)
{
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort1 = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = testSolver->mkFunctionSort(testSolver->mkUninterpretedSort("u"),
                                          testSolver->getIntegerSort());
  Term b1 = testSolver->mkVar(bvSort, "b1");
  Term b11 = testSolver->mkVar(bvSort, "b1");
  Term b2 = testSolver->mkVar(testSolver->getIntegerSort(), "b2");
  Term b3 = testSolver->mkVar(funSort2, "b3");
  Term v1 = testSolver->mkConst(bvSort, "v1");
  Term v2 = testSolver->mkConst(testSolver->getIntegerSort(), "v2");
  Term v3 = testSolver->mkConst(funSort2, "v3");
  Term f1 = testSolver->mkConst(funSort1, "f1");
  Term f2 = testSolver->mkConst(funSort2, "f2");
  Term f3 = testSolver->mkConst(bvSort, "f3");
  ASSERT_NO_THROW(testSolver->defineFunRec("f", {}, bvSort, v1));
  ASSERT_NO_THROW(testSolver->defineFunRec("ff", {b1, b2}, bvSort, v1));
  ASSERT_NO_THROW(testSolver->defineFunRec(f1, {b1, b11}, v1));
  ASSERT_THROW(testSolver->defineFunRec("fff", {b1}, bvSort, v3),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec("ff", {b1, v2}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec("ffff", {b1}, funSort2, v3),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec("fffff", {b1, b3}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f1, {b1}, v1), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f1, {b1, b11}, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f1, {b1, b11}, v3), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f2, {b1}, v2), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f3, {b1}, v1), CVC4ApiException);

  Solver* slv = new Solver();
  Sort bvSort2 = slv->mkBitVectorSort(32);
  Term v12 = slv->mkConst(bvSort2, "v1");
  Term b12 = slv->mkVar(bvSort2, "b1");
  Term b22 = slv->mkVar(slv->getIntegerSort(), "b2");
  ASSERT_NO_THROW(slv->defineFunRec("f", {}, bvSort2, v12));
  ASSERT_NO_THROW(slv->defineFunRec("ff", {b12, b22}, bvSort2, v12));
  ASSERT_THROW(slv->defineFunRec("f", {}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv->defineFunRec("f", {}, bvSort2, v1), CVC4ApiException);
  ASSERT_THROW(slv->defineFunRec("ff", {b1, b22}, bvSort2, v12),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunRec("ff", {b12, b2}, bvSort2, v12),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunRec("ff", {b12, b22}, bvSort, v12),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunRec("ff", {b12, b22}, bvSort2, v1),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, defineFunRecWrongLogic)
{
  testSolver->setLogic("QF_BV");
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Term b = testSolver->mkVar(bvSort, "b");
  Term v = testSolver->mkConst(bvSort, "v");
  Term f = testSolver->mkConst(funSort, "f");
  ASSERT_THROW(testSolver->defineFunRec("f", {}, bvSort, v), CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunRec(f, {b, b}, v), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, defineFunRecGlobal)
{
  Sort bSort = testSolver->getBooleanSort();
  Sort fSort = testSolver->mkFunctionSort(bSort, bSort);

  testSolver->push();
  Term bTrue = testSolver->mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = testSolver->defineFunRec("f", {}, bSort, bTrue, true);
  Term b = testSolver->mkVar(bSort, "b");
  Term gSym = testSolver->mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = testSolver->defineFunRec(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  testSolver->assertFormula(testSolver->mkTerm(
      OR, f.notTerm(), testSolver->mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
  testSolver->pop();
  // (assert (or (not f) (not (g true))))
  testSolver->assertFormula(testSolver->mkTerm(
      OR, f.notTerm(), testSolver->mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, defineFunsRec)
{
  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort1 = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = testSolver->mkFunctionSort(uSort, testSolver->getIntegerSort());
  Term b1 = testSolver->mkVar(bvSort, "b1");
  Term b11 = testSolver->mkVar(bvSort, "b1");
  Term b2 = testSolver->mkVar(testSolver->getIntegerSort(), "b2");
  Term b3 = testSolver->mkVar(funSort2, "b3");
  Term b4 = testSolver->mkVar(uSort, "b4");
  Term v1 = testSolver->mkConst(bvSort, "v1");
  Term v2 = testSolver->mkConst(testSolver->getIntegerSort(), "v2");
  Term v3 = testSolver->mkConst(funSort2, "v3");
  Term v4 = testSolver->mkConst(uSort, "v4");
  Term f1 = testSolver->mkConst(funSort1, "f1");
  Term f2 = testSolver->mkConst(funSort2, "f2");
  Term f3 = testSolver->mkConst(bvSort, "f3");
  ASSERT_NO_THROW(
      testSolver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  ASSERT_THROW(testSolver->defineFunsRec({f1, f2}, {{v1, b11}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(testSolver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
               CVC4ApiException);

  Solver* slv = new Solver();
  Sort uSort2 = slv->mkUninterpretedSort("u");
  Sort bvSort2 = slv->mkBitVectorSort(32);
  Sort funSort12 = slv->mkFunctionSort({bvSort2, bvSort2}, bvSort2);
  Sort funSort22 = slv->mkFunctionSort(uSort2, slv->getIntegerSort());
  Term b12 = slv->mkVar(bvSort2, "b1");
  Term b112 = slv->mkVar(bvSort2, "b1");
  Term b42 = slv->mkVar(uSort2, "b4");
  Term v12 = slv->mkConst(bvSort2, "v1");
  Term v22 = slv->mkConst(slv->getIntegerSort(), "v2");
  Term f12 = slv->mkConst(funSort12, "f1");
  Term f22 = slv->mkConst(funSort22, "f2");
  ASSERT_NO_THROW(
      slv->defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v22}));
  ASSERT_THROW(slv->defineFunsRec({f1, f22}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f2}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f22}, {{b1, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f22}, {{b12, b11}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f22}, {{b12, b112}, {b4}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v1, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv->defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v2}),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, defineFunsRecWrongLogic)
{
  testSolver->setLogic("QF_BV");
  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort funSort1 = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = testSolver->mkFunctionSort(uSort, testSolver->getIntegerSort());
  Term b = testSolver->mkVar(bvSort, "b");
  Term u = testSolver->mkVar(uSort, "u");
  Term v1 = testSolver->mkConst(bvSort, "v1");
  Term v2 = testSolver->mkConst(testSolver->getIntegerSort(), "v2");
  Term f1 = testSolver->mkConst(funSort1, "f1");
  Term f2 = testSolver->mkConst(funSort2, "f2");
  ASSERT_THROW(testSolver->defineFunsRec({f1, f2}, {{b, b}, {u}}, {v1, v2}),
               CVC4ApiException);
}

TEST_F(TestApiBlackSolver, defineFunsRecGlobal)
{
  Sort bSort = testSolver->getBooleanSort();
  Sort fSort = testSolver->mkFunctionSort(bSort, bSort);

  testSolver->push();
  Term bTrue = testSolver->mkBoolean(true);
  Term b = testSolver->mkVar(bSort, "b");
  Term gSym = testSolver->mkConst(fSort, "g");
  // (define-funs-rec ((g ((b Bool)) Bool)) (b))
  testSolver->defineFunsRec({gSym}, {{b}}, {b}, true);

  // (assert (not (g true)))
  testSolver->assertFormula(testSolver->mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
  testSolver->pop();
  // (assert (not (g true)))
  testSolver->assertFormula(testSolver->mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(testSolver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, uFIteration)
{
  Sort intSort = testSolver->getIntegerSort();
  Sort funSort = testSolver->mkFunctionSort({intSort, intSort}, intSort);
  Term x = testSolver->mkConst(intSort, "x");
  Term y = testSolver->mkConst(intSort, "y");
  Term f = testSolver->mkConst(funSort, "f");
  Term fxy = testSolver->mkTerm(APPLY_UF, f, x, y);

  // Expecting the uninterpreted function to be one of the children
  Term expected_children[3] = {f, x, y};
  uint32_t idx = 0;
  for (auto c : fxy)
  {
    ASSERT_LT(idx, 3);
    ASSERT_EQ(c, expected_children[idx]);
    idx++;
  }
}

TEST_F(TestApiBlackSolver, getInfo)
{
  ASSERT_NO_THROW(testSolver->getInfo("name"));
  ASSERT_THROW(testSolver->getInfo("asdf"), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getInterpolant)
{
  testSolver->setLogic("QF_LIA");
  testSolver->setOption("produce-interpols", "default");
  testSolver->setOption("incremental", "false");

  Sort intSort = testSolver->getIntegerSort();
  Term zero = testSolver->mkInteger(0);
  Term x = testSolver->mkConst(intSort, "x");
  Term y = testSolver->mkConst(intSort, "y");
  Term z = testSolver->mkConst(intSort, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  testSolver->assertFormula(
      testSolver->mkTerm(GT, testSolver->mkTerm(PLUS, x, y), zero));
  testSolver->assertFormula(testSolver->mkTerm(LT, x, zero));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj =
      testSolver->mkTerm(OR,
                      testSolver->mkTerm(GT, testSolver->mkTerm(PLUS, y, z), zero),
                      testSolver->mkTerm(LT, z, zero));
  Term output;
  // Call the interpolation api, while the resulting interpolant is the output
  testSolver->getInterpolant(conj, output);

  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(output.getSort().isBoolean());
}

TEST_F(TestApiBlackSolver, getOp)
{
  Sort bv32 = testSolver->mkBitVectorSort(32);
  Term a = testSolver->mkConst(bv32, "a");
  Op ext = testSolver->mkOp(BITVECTOR_EXTRACT, 2, 1);
  Term exta = testSolver->mkTerm(ext, a);

  ASSERT_FALSE(a.hasOp());
  ASSERT_THROW(a.getOp(), CVC4ApiException);
  ASSERT_TRUE(exta.hasOp());
  ASSERT_EQ(exta.getOp(), ext);

  // Test Datatypes -- more complicated
  DatatypeDecl consListSpec = testSolver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = testSolver->mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", testSolver->getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = testSolver->mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = testSolver->mkDatatypeSort(consListSpec);
  Datatype consList = consListSort.getDatatype();

  Term consTerm = consList.getConstructorTerm("cons");
  Term nilTerm = consList.getConstructorTerm("nil");
  Term headTerm = consList["cons"].getSelectorTerm("head");

  Term listnil = testSolver->mkTerm(APPLY_CONSTRUCTOR, nilTerm);
  Term listcons1 = testSolver->mkTerm(
      APPLY_CONSTRUCTOR, consTerm, testSolver->mkInteger(1), listnil);
  Term listhead = testSolver->mkTerm(APPLY_SELECTOR, headTerm, listcons1);

  ASSERT_TRUE(listnil.hasOp());
  ASSERT_TRUE(listcons1.hasOp());
  ASSERT_TRUE(listhead.hasOp());
}

TEST_F(TestApiBlackSolver, getOption)
{
  ASSERT_NO_THROW(testSolver->getOption("incremental"));
  ASSERT_THROW(testSolver->getOption("asdf"), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions1)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "false");
  testSolver->checkSatAssuming(testSolver->mkFalse());
  ASSERT_THROW(testSolver->getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions2)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "true");
  testSolver->setOption("produce-unsat-assumptions", "false");
  testSolver->checkSatAssuming(testSolver->mkFalse());
  ASSERT_THROW(testSolver->getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions3)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "true");
  testSolver->setOption("produce-unsat-assumptions", "true");
  testSolver->checkSatAssuming(testSolver->mkFalse());
  ASSERT_NO_THROW(testSolver->getUnsatAssumptions());
  testSolver->checkSatAssuming(testSolver->mkTrue());
  ASSERT_THROW(testSolver->getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiBlackSolver, getUnsatCore1)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "false");
  testSolver->assertFormula(testSolver->mkFalse());
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getUnsatCore(), CVC4ApiException);
#endif
}

TEST_F(TestApiBlackSolver, getUnsatCore2)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-unsat-cores", "false");
  testSolver->assertFormula(testSolver->mkFalse());
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getUnsatCore(), CVC4ApiException);
#endif
}

TEST_F(TestApiBlackSolver, getUnsatCore3)
{
#if IS_PROOFS_BUILD
  testSolver->setOption("incremental", "true");
  testSolver->setOption("produce-unsat-cores", "true");

  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort intSort = testSolver->getIntegerSort();
  Sort boolSort = testSolver->getBooleanSort();
  Sort uToIntSort = testSolver->mkFunctionSort(uSort, intSort);
  Sort intPredSort = testSolver->mkFunctionSort(intSort, boolSort);
  std::vector<Term> unsat_core;

  Term x = testSolver->mkConst(uSort, "x");
  Term y = testSolver->mkConst(uSort, "y");
  Term f = testSolver->mkConst(uToIntSort, "f");
  Term p = testSolver->mkConst(intPredSort, "p");
  Term zero = testSolver->mkInteger(0);
  Term one = testSolver->mkInteger(1);
  Term f_x = testSolver->mkTerm(APPLY_UF, f, x);
  Term f_y = testSolver->mkTerm(APPLY_UF, f, y);
  Term sum = testSolver->mkTerm(PLUS, f_x, f_y);
  Term p_0 = testSolver->mkTerm(APPLY_UF, p, zero);
  Term p_f_y = testSolver->mkTerm(APPLY_UF, p, f_y);
  testSolver->assertFormula(testSolver->mkTerm(GT, zero, f_x));
  testSolver->assertFormula(testSolver->mkTerm(GT, zero, f_y));
  testSolver->assertFormula(testSolver->mkTerm(GT, sum, one));
  testSolver->assertFormula(p_0);
  testSolver->assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(testSolver->checkSat().isUnsat());

  ASSERT_NO_THROW(unsat_core = testSolver->getUnsatCore());

  testSolver->resetAssertions();
  for (const auto& t : unsat_core)
  {
    testSolver->assertFormula(t);
  }
  Result res = testSolver->checkSat();
  ASSERT_TRUE(res.isUnsat());
#endif
}

TEST_F(TestApiBlackSolver, getValue1)
{
  testSolver->setOption("produce-models", "false");
  Term t = testSolver->mkTrue();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getValue(t), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getValue2)
{
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkFalse();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getValue(t), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getValue3)
{
  testSolver->setOption("produce-models", "true");
  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort intSort = testSolver->getIntegerSort();
  Sort boolSort = testSolver->getBooleanSort();
  Sort uToIntSort = testSolver->mkFunctionSort(uSort, intSort);
  Sort intPredSort = testSolver->mkFunctionSort(intSort, boolSort);
  std::vector<Term> unsat_core;

  Term x = testSolver->mkConst(uSort, "x");
  Term y = testSolver->mkConst(uSort, "y");
  Term z = testSolver->mkConst(uSort, "z");
  Term f = testSolver->mkConst(uToIntSort, "f");
  Term p = testSolver->mkConst(intPredSort, "p");
  Term zero = testSolver->mkInteger(0);
  Term one = testSolver->mkInteger(1);
  Term f_x = testSolver->mkTerm(APPLY_UF, f, x);
  Term f_y = testSolver->mkTerm(APPLY_UF, f, y);
  Term sum = testSolver->mkTerm(PLUS, f_x, f_y);
  Term p_0 = testSolver->mkTerm(APPLY_UF, p, zero);
  Term p_f_y = testSolver->mkTerm(APPLY_UF, p, f_y);

  testSolver->assertFormula(testSolver->mkTerm(LEQ, zero, f_x));
  testSolver->assertFormula(testSolver->mkTerm(LEQ, zero, f_y));
  testSolver->assertFormula(testSolver->mkTerm(LEQ, sum, one));
  testSolver->assertFormula(p_0.notTerm());
  testSolver->assertFormula(p_f_y);
  ASSERT_TRUE(testSolver->checkSat().isSat());
  ASSERT_NO_THROW(testSolver->getValue(x));
  ASSERT_NO_THROW(testSolver->getValue(y));
  ASSERT_NO_THROW(testSolver->getValue(z));
  ASSERT_NO_THROW(testSolver->getValue(sum));
  ASSERT_NO_THROW(testSolver->getValue(p_f_y));

  Solver* slv = new Solver();
  ASSERT_THROW(slv->getValue(x), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, getQuantifierElimination)
{
  Term x = testSolver->mkVar(testSolver->getBooleanSort(), "x");
  Term forall =
      testSolver->mkTerm(FORALL,
                      testSolver->mkTerm(BOUND_VAR_LIST, x),
                      testSolver->mkTerm(OR, x, testSolver->mkTerm(NOT, x)));
  ASSERT_THROW(testSolver->getQuantifierElimination(Term()), CVC4ApiException);
  ASSERT_THROW(testSolver->getQuantifierElimination(Solver().mkBoolean(false)),
               CVC4ApiException);
  ASSERT_NO_THROW(testSolver->getQuantifierElimination(forall));
}

TEST_F(TestApiBlackSolver, getQuantifierEliminationDisjunct)
{
  Term x = testSolver->mkVar(testSolver->getBooleanSort(), "x");
  Term forall =
      testSolver->mkTerm(FORALL,
                      testSolver->mkTerm(BOUND_VAR_LIST, x),
                      testSolver->mkTerm(OR, x, testSolver->mkTerm(NOT, x)));
  ASSERT_THROW(testSolver->getQuantifierEliminationDisjunct(Term()),
               CVC4ApiException);
  ASSERT_THROW(
      testSolver->getQuantifierEliminationDisjunct(Solver().mkBoolean(false)),
      CVC4ApiException);
  ASSERT_NO_THROW(testSolver->getQuantifierEliminationDisjunct(forall));
}

TEST_F(TestApiBlackSolver, declareSeparationHeap)
{
  testSolver->setLogic("ALL_SUPPORTED");
  Sort integer = testSolver->getIntegerSort();
  ASSERT_NO_THROW(testSolver->declareSeparationHeap(integer, integer));
  // cannot declare separation logic heap more than once
  ASSERT_THROW(testSolver->declareSeparationHeap(integer, integer),
               CVC4ApiException);
}

namespace {
/**
 * Helper function for testGetSeparation{Heap,Nil}TermX. Asserts and checks
 * some simple separation logic constraints.
 */
void checkSimpleSeparationConstraints(Solver* solver)
{
  Sort integer = solver->getIntegerSort();
  // declare the separation heap
  solver->declareSeparationHeap(integer, integer);
  Term x = solver->mkConst(integer, "x");
  Term p = solver->mkConst(integer, "p");
  Term heap = solver->mkTerm(CVC4::api::Kind::SEP_PTO, p, x);
  solver->assertFormula(heap);
  Term nil = solver->mkSepNil(integer);
  solver->assertFormula(nil.eqTerm(solver->mkReal(5)));
  solver->checkSat();
}
}  // namespace

TEST_F(TestApiBlackSolver, getSeparationHeapTerm1)
{
  testSolver->setLogic("QF_BV");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkTrue();
  testSolver->assertFormula(t);
  ASSERT_THROW(testSolver->getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationHeapTerm2)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(testSolver->getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationHeapTerm3)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkFalse();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationHeapTerm4)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkTrue();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationHeapTerm5)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(testSolver->getSeparationHeap());
}

TEST_F(TestApiBlackSolver, getSeparationNilTerm1)
{
  testSolver->setLogic("QF_BV");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkTrue();
  testSolver->assertFormula(t);
  ASSERT_THROW(testSolver->getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationNilTerm2)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(testSolver->getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationNilTerm3)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkFalse();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationNilTerm4)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  Term t = testSolver->mkTrue();
  testSolver->assertFormula(t);
  testSolver->checkSat();
  ASSERT_THROW(testSolver->getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, getSeparationNilTerm5)
{
  testSolver->setLogic("ALL_SUPPORTED");
  testSolver->setOption("incremental", "false");
  testSolver->setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(testSolver->getSeparationNilTerm());
}

TEST_F(TestApiBlackSolver, push1)
{
  testSolver->setOption("incremental", "true");
  ASSERT_NO_THROW(testSolver->push(1));
  ASSERT_THROW(testSolver->setOption("incremental", "false"), CVC4ApiException);
  ASSERT_THROW(testSolver->setOption("incremental", "true"), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, push2)
{
  testSolver->setOption("incremental", "false");
  ASSERT_THROW(testSolver->push(1), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, pop1)
{
  testSolver->setOption("incremental", "false");
  ASSERT_THROW(testSolver->pop(1), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, pop2)
{
  testSolver->setOption("incremental", "true");
  ASSERT_THROW(testSolver->pop(1), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, pop3)
{
  testSolver->setOption("incremental", "true");
  ASSERT_NO_THROW(testSolver->push(1));
  ASSERT_NO_THROW(testSolver->pop(1));
  ASSERT_THROW(testSolver->pop(1), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModel1)
{
  testSolver->setOption("produce-models", "true");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_THROW(testSolver->blockModel(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModel2)
{
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_THROW(testSolver->blockModel(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModel3)
{
  testSolver->setOption("produce-models", "true");
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  ASSERT_THROW(testSolver->blockModel(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModel4)
{
  testSolver->setOption("produce-models", "true");
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_NO_THROW(testSolver->blockModel());
}

TEST_F(TestApiBlackSolver, blockModelValues1)
{
  testSolver->setOption("produce-models", "true");
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_THROW(testSolver->blockModelValues({}), CVC4ApiException);
  ASSERT_THROW(testSolver->blockModelValues({Term()}), CVC4ApiException);
  ASSERT_THROW(testSolver->blockModelValues({Solver().mkBoolean(false)}),
               CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues2)
{
  testSolver->setOption("produce-models", "true");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_THROW(testSolver->blockModelValues({x}), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues3)
{
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_THROW(testSolver->blockModelValues({x}), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues4)
{
  testSolver->setOption("produce-models", "true");
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  ASSERT_THROW(testSolver->blockModelValues({x}), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues5)
{
  testSolver->setOption("produce-models", "true");
  testSolver->setOption("block-models", "literals");
  Term x = testSolver->mkConst(testSolver->getBooleanSort(), "x");
  testSolver->assertFormula(x.eqTerm(x));
  testSolver->checkSat();
  ASSERT_NO_THROW(testSolver->blockModelValues({x}));
}

TEST_F(TestApiBlackSolver, setInfo)
{
  ASSERT_THROW(testSolver->setInfo("cvc4-lagic", "QF_BV"), CVC4ApiException);
  ASSERT_THROW(testSolver->setInfo("cvc2-logic", "QF_BV"), CVC4ApiException);
  ASSERT_THROW(testSolver->setInfo("cvc4-logic", "asdf"), CVC4ApiException);

  ASSERT_NO_THROW(testSolver->setInfo("source", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("category", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("difficulty", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("filename", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("license", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("name", "asdf"));
  ASSERT_NO_THROW(testSolver->setInfo("notes", "asdf"));

  ASSERT_NO_THROW(testSolver->setInfo("smt-lib-version", "2"));
  ASSERT_NO_THROW(testSolver->setInfo("smt-lib-version", "2.0"));
  ASSERT_NO_THROW(testSolver->setInfo("smt-lib-version", "2.5"));
  ASSERT_NO_THROW(testSolver->setInfo("smt-lib-version", "2.6"));
  ASSERT_THROW(testSolver->setInfo("smt-lib-version", ".0"), CVC4ApiException);

  ASSERT_NO_THROW(testSolver->setInfo("status", "sat"));
  ASSERT_NO_THROW(testSolver->setInfo("status", "unsat"));
  ASSERT_NO_THROW(testSolver->setInfo("status", "unknown"));
  ASSERT_THROW(testSolver->setInfo("status", "asdf"), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, simplify)
{
  ASSERT_THROW(testSolver->simplify(Term()), CVC4ApiException);

  Sort bvSort = testSolver->mkBitVectorSort(32);
  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort funSort1 = testSolver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = testSolver->mkFunctionSort(uSort, testSolver->getIntegerSort());
  DatatypeDecl consListSpec = testSolver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = testSolver->mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", testSolver->getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = testSolver->mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = testSolver->mkDatatypeSort(consListSpec);

  Term x = testSolver->mkConst(bvSort, "x");
  ASSERT_NO_THROW(testSolver->simplify(x));
  Term a = testSolver->mkConst(bvSort, "a");
  ASSERT_NO_THROW(testSolver->simplify(a));
  Term b = testSolver->mkConst(bvSort, "b");
  ASSERT_NO_THROW(testSolver->simplify(b));
  Term x_eq_x = testSolver->mkTerm(EQUAL, x, x);
  ASSERT_NO_THROW(testSolver->simplify(x_eq_x));
  ASSERT_NE(testSolver->mkTrue(), x_eq_x);
  ASSERT_EQ(testSolver->mkTrue(), testSolver->simplify(x_eq_x));
  Term x_eq_b = testSolver->mkTerm(EQUAL, x, b);
  ASSERT_NO_THROW(testSolver->simplify(x_eq_b));
  ASSERT_NE(testSolver->mkTrue(), x_eq_b);
  ASSERT_NE(testSolver->mkTrue(), testSolver->simplify(x_eq_b));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->simplify(x), CVC4ApiException);

  Term i1 = testSolver->mkConst(testSolver->getIntegerSort(), "i1");
  ASSERT_NO_THROW(testSolver->simplify(i1));
  Term i2 = testSolver->mkTerm(MULT, i1, testSolver->mkInteger("23"));
  ASSERT_NO_THROW(testSolver->simplify(i2));
  ASSERT_NE(i1, i2);
  ASSERT_NE(i1, testSolver->simplify(i2));
  Term i3 = testSolver->mkTerm(PLUS, i1, testSolver->mkInteger(0));
  ASSERT_NO_THROW(testSolver->simplify(i3));
  ASSERT_NE(i1, i3);
  ASSERT_EQ(i1, testSolver->simplify(i3));

  Datatype consList = consListSort.getDatatype();
  Term dt1 = testSolver->mkTerm(
      APPLY_CONSTRUCTOR,
      consList.getConstructorTerm("cons"),
      testSolver->mkInteger(0),
      testSolver->mkTerm(APPLY_CONSTRUCTOR, consList.getConstructorTerm("nil")));
  ASSERT_NO_THROW(testSolver->simplify(dt1));
  Term dt2 = testSolver->mkTerm(
      APPLY_SELECTOR, consList["cons"].getSelectorTerm("head"), dt1);
  ASSERT_NO_THROW(testSolver->simplify(dt2));

  Term b1 = testSolver->mkVar(bvSort, "b1");
  ASSERT_NO_THROW(testSolver->simplify(b1));
  Term b2 = testSolver->mkVar(bvSort, "b1");
  ASSERT_NO_THROW(testSolver->simplify(b2));
  Term b3 = testSolver->mkVar(uSort, "b3");
  ASSERT_NO_THROW(testSolver->simplify(b3));
  Term v1 = testSolver->mkConst(bvSort, "v1");
  ASSERT_NO_THROW(testSolver->simplify(v1));
  Term v2 = testSolver->mkConst(testSolver->getIntegerSort(), "v2");
  ASSERT_NO_THROW(testSolver->simplify(v2));
  Term f1 = testSolver->mkConst(funSort1, "f1");
  ASSERT_NO_THROW(testSolver->simplify(f1));
  Term f2 = testSolver->mkConst(funSort2, "f2");
  ASSERT_NO_THROW(testSolver->simplify(f2));
  testSolver->defineFunsRec({f1, f2}, {{b1, b2}, {b3}}, {v1, v2});
  ASSERT_NO_THROW(testSolver->simplify(f1));
  ASSERT_NO_THROW(testSolver->simplify(f2));
  delete slv;
}

TEST_F(TestApiBlackSolver, assertFormula)
{
  ASSERT_NO_THROW(testSolver->assertFormula(testSolver->mkTrue()));
  ASSERT_THROW(testSolver->assertFormula(Term()), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->assertFormula(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkEntailed)
{
  testSolver->setOption("incremental", "false");
  ASSERT_NO_THROW(testSolver->checkEntailed(testSolver->mkTrue()));
  ASSERT_THROW(testSolver->checkEntailed(testSolver->mkTrue()), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkEntailed(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkEntailed1)
{
  Sort boolSort = testSolver->getBooleanSort();
  Term x = testSolver->mkConst(boolSort, "x");
  Term y = testSolver->mkConst(boolSort, "y");
  Term z = testSolver->mkTerm(AND, x, y);
  testSolver->setOption("incremental", "true");
  ASSERT_NO_THROW(testSolver->checkEntailed(testSolver->mkTrue()));
  ASSERT_THROW(testSolver->checkEntailed(Term()), CVC4ApiException);
  ASSERT_NO_THROW(testSolver->checkEntailed(testSolver->mkTrue()));
  ASSERT_NO_THROW(testSolver->checkEntailed(z));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkEntailed(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkEntailed2)
{
  testSolver->setOption("incremental", "true");

  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort intSort = testSolver->getIntegerSort();
  Sort boolSort = testSolver->getBooleanSort();
  Sort uToIntSort = testSolver->mkFunctionSort(uSort, intSort);
  Sort intPredSort = testSolver->mkFunctionSort(intSort, boolSort);

  Term n = Term();
  // Constants
  Term x = testSolver->mkConst(uSort, "x");
  Term y = testSolver->mkConst(uSort, "y");
  // Functions
  Term f = testSolver->mkConst(uToIntSort, "f");
  Term p = testSolver->mkConst(intPredSort, "p");
  // Values
  Term zero = testSolver->mkInteger(0);
  Term one = testSolver->mkInteger(1);
  // Terms
  Term f_x = testSolver->mkTerm(APPLY_UF, f, x);
  Term f_y = testSolver->mkTerm(APPLY_UF, f, y);
  Term sum = testSolver->mkTerm(PLUS, f_x, f_y);
  Term p_0 = testSolver->mkTerm(APPLY_UF, p, zero);
  Term p_f_y = testSolver->mkTerm(APPLY_UF, p, f_y);
  // Assertions
  Term assertions =
      testSolver->mkTerm(AND,
                      std::vector<Term>{
                          testSolver->mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
                          testSolver->mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
                          testSolver->mkTerm(LEQ, sum, one),   // f(x) + f(y) <= 1
                          p_0.notTerm(),                    // not p(0)
                          p_f_y                             // p(f(y))
                      });

  ASSERT_NO_THROW(testSolver->checkEntailed(testSolver->mkTrue()));
  testSolver->assertFormula(assertions);
  ASSERT_NO_THROW(testSolver->checkEntailed(testSolver->mkTerm(DISTINCT, x, y)));
  ASSERT_NO_THROW(testSolver->checkEntailed(
      {testSolver->mkFalse(), testSolver->mkTerm(DISTINCT, x, y)}));
  ASSERT_THROW(testSolver->checkEntailed(n), CVC4ApiException);
  ASSERT_THROW(testSolver->checkEntailed({n, testSolver->mkTerm(DISTINCT, x, y)}),
               CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkEntailed(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkSat)
{
  testSolver->setOption("incremental", "false");
  ASSERT_NO_THROW(testSolver->checkSat());
  ASSERT_THROW(testSolver->checkSat(), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, checkSatAssuming)
{
  testSolver->setOption("incremental", "false");
  ASSERT_NO_THROW(testSolver->checkSatAssuming(testSolver->mkTrue()));
  ASSERT_THROW(testSolver->checkSatAssuming(testSolver->mkTrue()), CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkSatAssuming(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkSatAssuming1)
{
  Sort boolSort = testSolver->getBooleanSort();
  Term x = testSolver->mkConst(boolSort, "x");
  Term y = testSolver->mkConst(boolSort, "y");
  Term z = testSolver->mkTerm(AND, x, y);
  testSolver->setOption("incremental", "true");
  ASSERT_NO_THROW(testSolver->checkSatAssuming(testSolver->mkTrue()));
  ASSERT_THROW(testSolver->checkSatAssuming(Term()), CVC4ApiException);
  ASSERT_NO_THROW(testSolver->checkSatAssuming(testSolver->mkTrue()));
  ASSERT_NO_THROW(testSolver->checkSatAssuming(z));
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkSatAssuming(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, checkSatAssuming2)
{
  testSolver->setOption("incremental", "true");

  Sort uSort = testSolver->mkUninterpretedSort("u");
  Sort intSort = testSolver->getIntegerSort();
  Sort boolSort = testSolver->getBooleanSort();
  Sort uToIntSort = testSolver->mkFunctionSort(uSort, intSort);
  Sort intPredSort = testSolver->mkFunctionSort(intSort, boolSort);

  Term n = Term();
  // Constants
  Term x = testSolver->mkConst(uSort, "x");
  Term y = testSolver->mkConst(uSort, "y");
  // Functions
  Term f = testSolver->mkConst(uToIntSort, "f");
  Term p = testSolver->mkConst(intPredSort, "p");
  // Values
  Term zero = testSolver->mkInteger(0);
  Term one = testSolver->mkInteger(1);
  // Terms
  Term f_x = testSolver->mkTerm(APPLY_UF, f, x);
  Term f_y = testSolver->mkTerm(APPLY_UF, f, y);
  Term sum = testSolver->mkTerm(PLUS, f_x, f_y);
  Term p_0 = testSolver->mkTerm(APPLY_UF, p, zero);
  Term p_f_y = testSolver->mkTerm(APPLY_UF, p, f_y);
  // Assertions
  Term assertions =
      testSolver->mkTerm(AND,
                      std::vector<Term>{
                          testSolver->mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
                          testSolver->mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
                          testSolver->mkTerm(LEQ, sum, one),   // f(x) + f(y) <= 1
                          p_0.notTerm(),                    // not p(0)
                          p_f_y                             // p(f(y))
                      });

  ASSERT_NO_THROW(testSolver->checkSatAssuming(testSolver->mkTrue()));
  testSolver->assertFormula(assertions);
  ASSERT_NO_THROW(testSolver->checkSatAssuming(testSolver->mkTerm(DISTINCT, x, y)));
  ASSERT_NO_THROW(testSolver->checkSatAssuming(
      {testSolver->mkFalse(), testSolver->mkTerm(DISTINCT, x, y)}));
  ASSERT_THROW(testSolver->checkSatAssuming(n), CVC4ApiException);
  ASSERT_THROW(testSolver->checkSatAssuming({n, testSolver->mkTerm(DISTINCT, x, y)}),
               CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->checkSatAssuming(testSolver->mkTrue()), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, setLogic)
{
  ASSERT_NO_THROW(testSolver->setLogic("AUFLIRA"));
  ASSERT_THROW(testSolver->setLogic("AF_BV"), CVC4ApiException);
  testSolver->assertFormula(testSolver->mkTrue());
  ASSERT_THROW(testSolver->setLogic("AUFLIRA"), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, setOption)
{
  ASSERT_NO_THROW(testSolver->setOption("bv-sat-solver", "minisat"));
  ASSERT_THROW(testSolver->setOption("bv-sat-solver", "1"), CVC4ApiException);
  testSolver->assertFormula(testSolver->mkTrue());
  ASSERT_THROW(testSolver->setOption("bv-sat-solver", "minisat"),
               CVC4ApiException);
}

TEST_F(TestApiBlackSolver, resetAssertions)
{
  testSolver->setOption("incremental", "true");

  Sort bvSort = testSolver->mkBitVectorSort(4);
  Term one = testSolver->mkBitVector(4, 1);
  Term x = testSolver->mkConst(bvSort, "x");
  Term ule = testSolver->mkTerm(BITVECTOR_ULE, x, one);
  Term srem = testSolver->mkTerm(BITVECTOR_SREM, one, x);
  testSolver->push(4);
  Term slt = testSolver->mkTerm(BITVECTOR_SLT, srem, one);
  testSolver->resetAssertions();
  testSolver->checkSatAssuming({slt, ule});
}

TEST_F(TestApiBlackSolver, mkSygusVar)
{
  Sort boolSort = testSolver->getBooleanSort();
  Sort intSort = testSolver->getIntegerSort();
  Sort funSort = testSolver->mkFunctionSort(intSort, boolSort);

  ASSERT_NO_THROW(testSolver->mkSygusVar(boolSort));
  ASSERT_NO_THROW(testSolver->mkSygusVar(funSort));
  ASSERT_NO_THROW(testSolver->mkSygusVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(testSolver->mkSygusVar(funSort, ""));
  ASSERT_THROW(testSolver->mkSygusVar(Sort()), CVC4ApiException);
  ASSERT_THROW(testSolver->mkSygusVar(testSolver->getNullSort(), "a"),
               CVC4ApiException);
  Solver* slv = new Solver();
  ASSERT_THROW(slv->mkSygusVar(boolSort), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, mkSygusGrammar)
{
  Term nullTerm;
  Term boolTerm = testSolver->mkBoolean(true);
  Term boolVar = testSolver->mkVar(testSolver->getBooleanSort());
  Term intVar = testSolver->mkVar(testSolver->getIntegerSort());

  ASSERT_NO_THROW(testSolver->mkSygusGrammar({}, {intVar}));
  ASSERT_NO_THROW(testSolver->mkSygusGrammar({boolVar}, {intVar}));
  ASSERT_THROW(testSolver->mkSygusGrammar({}, {}), CVC4ApiException);
  ASSERT_THROW(testSolver->mkSygusGrammar({}, {nullTerm}), CVC4ApiException);
  ASSERT_THROW(testSolver->mkSygusGrammar({}, {boolTerm}), CVC4ApiException);
  ASSERT_THROW(testSolver->mkSygusGrammar({boolTerm}, {intVar}), CVC4ApiException);
  Solver* slv = new Solver();
  Term boolVar2 = slv->mkVar(slv->getBooleanSort());
  Term intVar2 = slv->mkVar(slv->getIntegerSort());
  ASSERT_NO_THROW(slv->mkSygusGrammar({boolVar2}, {intVar2}));
  ASSERT_THROW(slv->mkSygusGrammar({boolVar}, {intVar2}), CVC4ApiException);
  ASSERT_THROW(slv->mkSygusGrammar({boolVar2}, {intVar}), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, synthFun)
{
  Sort null = testSolver->getNullSort();
  Sort boolean = testSolver->getBooleanSort();
  Sort integer = testSolver->getIntegerSort();

  Term nullTerm;
  Term x = testSolver->mkVar(boolean);

  Term start1 = testSolver->mkVar(boolean);
  Term start2 = testSolver->mkVar(integer);

  Grammar g1 = testSolver->mkSygusGrammar({x}, {start1});
  g1.addRule(start1, testSolver->mkBoolean(false));

  Grammar g2 = testSolver->mkSygusGrammar({x}, {start2});
  g2.addRule(start2, testSolver->mkInteger(0));

  ASSERT_NO_THROW(testSolver->synthFun("", {}, boolean));
  ASSERT_NO_THROW(testSolver->synthFun("f1", {x}, boolean));
  ASSERT_NO_THROW(testSolver->synthFun("f2", {x}, boolean, g1));

  ASSERT_THROW(testSolver->synthFun("f3", {nullTerm}, boolean), CVC4ApiException);
  ASSERT_THROW(testSolver->synthFun("f4", {}, null), CVC4ApiException);
  ASSERT_THROW(testSolver->synthFun("f6", {x}, boolean, g2), CVC4ApiException);
  Solver* slv = new Solver();
  Term x2 = slv->mkVar(slv->getBooleanSort());
  ASSERT_NO_THROW(slv->synthFun("f1", {x2}, slv->getBooleanSort()));
  ASSERT_THROW(slv->synthFun("", {}, testSolver->getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv->synthFun("f1", {x}, testSolver->getBooleanSort()),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, synthInv)
{
  Sort boolean = testSolver->getBooleanSort();
  Sort integer = testSolver->getIntegerSort();

  Term nullTerm;
  Term x = testSolver->mkVar(boolean);

  Term start1 = testSolver->mkVar(boolean);
  Term start2 = testSolver->mkVar(integer);

  Grammar g1 = testSolver->mkSygusGrammar({x}, {start1});
  g1.addRule(start1, testSolver->mkBoolean(false));

  Grammar g2 = testSolver->mkSygusGrammar({x}, {start2});
  g2.addRule(start2, testSolver->mkInteger(0));

  ASSERT_NO_THROW(testSolver->synthInv("", {}));
  ASSERT_NO_THROW(testSolver->synthInv("i1", {x}));
  ASSERT_NO_THROW(testSolver->synthInv("i2", {x}, g1));

  ASSERT_THROW(testSolver->synthInv("i3", {nullTerm}), CVC4ApiException);
  ASSERT_THROW(testSolver->synthInv("i4", {x}, g2), CVC4ApiException);
}

TEST_F(TestApiBlackSolver, addSygusConstraint)
{
  Term nullTerm;
  Term boolTerm = testSolver->mkBoolean(true);
  Term intTerm = testSolver->mkInteger(1);

  ASSERT_NO_THROW(testSolver->addSygusConstraint(boolTerm));
  ASSERT_THROW(testSolver->addSygusConstraint(nullTerm), CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusConstraint(intTerm), CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->addSygusConstraint(boolTerm), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, addSygusInvConstraint)
{
  Sort boolean = testSolver->getBooleanSort();
  Sort real = testSolver->getRealSort();

  Term nullTerm;
  Term intTerm = testSolver->mkInteger(1);

  Term inv = testSolver->declareFun("inv", {real}, boolean);
  Term pre = testSolver->declareFun("pre", {real}, boolean);
  Term trans = testSolver->declareFun("trans", {real, real}, boolean);
  Term post = testSolver->declareFun("post", {real}, boolean);

  Term inv1 = testSolver->declareFun("inv1", {real}, real);

  Term trans1 = testSolver->declareFun("trans1", {boolean, real}, boolean);
  Term trans2 = testSolver->declareFun("trans2", {real, boolean}, boolean);
  Term trans3 = testSolver->declareFun("trans3", {real, real}, real);

  ASSERT_NO_THROW(testSolver->addSygusInvConstraint(inv, pre, trans, post));

  ASSERT_THROW(testSolver->addSygusInvConstraint(nullTerm, pre, trans, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, nullTerm, trans, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, nullTerm, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, trans, nullTerm),
               CVC4ApiException);

  ASSERT_THROW(testSolver->addSygusInvConstraint(intTerm, pre, trans, post),
               CVC4ApiException);

  ASSERT_THROW(testSolver->addSygusInvConstraint(inv1, pre, trans, post),
               CVC4ApiException);

  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, trans, trans, post),
               CVC4ApiException);

  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, intTerm, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, pre, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, trans1, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, trans2, post),
               CVC4ApiException);
  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, trans3, post),
               CVC4ApiException);

  ASSERT_THROW(testSolver->addSygusInvConstraint(inv, pre, trans, trans),
               CVC4ApiException);
  Solver* slv = new Solver();
  Sort boolean2 = slv->getBooleanSort();
  Sort real2 = slv->getRealSort();
  Term inv22 = slv->declareFun("inv", {real2}, boolean2);
  Term pre22 = slv->declareFun("pre", {real2}, boolean2);
  Term trans22 = slv->declareFun("trans", {real2, real2}, boolean2);
  Term post22 = slv->declareFun("post", {real2}, boolean2);
  ASSERT_NO_THROW(slv->addSygusInvConstraint(inv22, pre22, trans22, post22));
  ASSERT_THROW(slv->addSygusInvConstraint(inv, pre22, trans22, post22),
               CVC4ApiException);
  ASSERT_THROW(slv->addSygusInvConstraint(inv22, pre, trans22, post22),
               CVC4ApiException);
  ASSERT_THROW(slv->addSygusInvConstraint(inv22, pre22, trans, post22),
               CVC4ApiException);
  ASSERT_THROW(slv->addSygusInvConstraint(inv22, pre22, trans22, post),
               CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, getSynthSolution)
{
  testSolver->setOption("lang", "sygus2");
  testSolver->setOption("incremental", "false");

  Term nullTerm;
  Term x = testSolver->mkBoolean(false);
  Term f = testSolver->synthFun("f", {}, testSolver->getBooleanSort());

  ASSERT_THROW(testSolver->getSynthSolution(f), CVC4ApiException);

  testSolver->checkSynth();

  ASSERT_NO_THROW(testSolver->getSynthSolution(f));
  ASSERT_NO_THROW(testSolver->getSynthSolution(f));

  ASSERT_THROW(testSolver->getSynthSolution(nullTerm), CVC4ApiException);
  ASSERT_THROW(testSolver->getSynthSolution(x), CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->getSynthSolution(f), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, getSynthSolutions)
{
  testSolver->setOption("lang", "sygus2");
  testSolver->setOption("incremental", "false");

  Term nullTerm;
  Term x = testSolver->mkBoolean(false);
  Term f = testSolver->synthFun("f", {}, testSolver->getBooleanSort());

  ASSERT_THROW(testSolver->getSynthSolutions({}), CVC4ApiException);
  ASSERT_THROW(testSolver->getSynthSolutions({f}), CVC4ApiException);

  testSolver->checkSynth();

  ASSERT_NO_THROW(testSolver->getSynthSolutions({f}));
  ASSERT_NO_THROW(testSolver->getSynthSolutions({f, f}));

  ASSERT_THROW(testSolver->getSynthSolutions({}), CVC4ApiException);
  ASSERT_THROW(testSolver->getSynthSolutions({nullTerm}), CVC4ApiException);
  ASSERT_THROW(testSolver->getSynthSolutions({x}), CVC4ApiException);

  Solver* slv = new Solver();
  ASSERT_THROW(slv->getSynthSolutions({x}), CVC4ApiException);
  delete slv;
}

TEST_F(TestApiBlackSolver, tupleProject)
{
  std::vector<Sort> sorts = {testSolver->getBooleanSort(),
                             testSolver->getIntegerSort(),
                             testSolver->getStringSort(),
                             testSolver->mkSetSort(testSolver->getStringSort())};
  std::vector<Term> elements = {
      testSolver->mkBoolean(true),
      testSolver->mkInteger(3),
      testSolver->mkString("C"),
      testSolver->mkTerm(SINGLETON, testSolver->mkString("Z"))};

  Term tuple = testSolver->mkTuple(sorts, elements);

  std::vector<uint32_t> indices1 = {};
  std::vector<uint32_t> indices2 = {0};
  std::vector<uint32_t> indices3 = {0, 1};
  std::vector<uint32_t> indices4 = {0, 0, 2, 2, 3, 3, 0};
  std::vector<uint32_t> indices5 = {4};
  std::vector<uint32_t> indices6 = {0, 4};

  ASSERT_NO_THROW(
      testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices1), tuple));
  ASSERT_NO_THROW(
      testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices2), tuple));
  ASSERT_NO_THROW(
      testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices3), tuple));
  ASSERT_NO_THROW(
      testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices4), tuple));

  ASSERT_THROW(testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices5), tuple),
               CVC4ApiException);
  ASSERT_THROW(testSolver->mkTerm(testSolver->mkOp(TUPLE_PROJECT, indices6), tuple),
               CVC4ApiException);

  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};

  Op op = testSolver->mkOp(TUPLE_PROJECT, indices);
  Term projection = testSolver->mkTerm(op, tuple);

  Datatype datatype = tuple.getSort().getDatatype();
  DatatypeConstructor constructor = datatype[0];

  for (size_t i = 0; i < indices.size(); i++)
  {
    Term selectorTerm = constructor[indices[i]].getSelectorTerm();
    Term selectedTerm = testSolver->mkTerm(APPLY_SELECTOR, selectorTerm, tuple);
    Term simplifiedTerm = testSolver->simplify(selectedTerm);
    ASSERT_EQ(elements[indices[i]], simplifiedTerm);
  }

  ASSERT_EQ(
      "((_ tuple_project 0 3 2 0 1 2) (mkTuple true 3 \"C\" (singleton "
      "\"Z\")))",
      projection.toString());
}

}  // namespace test
}  // namespace CVC4

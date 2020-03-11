/*********************                                                        */
/*! \file theory_bags_type_enumerator_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mahgoub
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::sets::BagEnumerator
 **
 ** White box testing of CVC4::theory::sets::BagEnumerator.  (These tests
 ** depends  on the ordering that the BagEnumerator use, so it's a white-box
 *  test.)
 **/

#include <cxxtest/TestSuite.h>

#include "theory/sets/theory_bags_type_enumerator.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::kind;
using namespace CVC4::theory::sets;
using namespace std;

class BagEnumeratorWhite : public CxxTest::TestSuite
{
  ExprManager* d_em;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

 public:
  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_em;
  }

  void testBagOfBooleans()
  {
    TypeNode boolType = d_nm->booleanType();
    BagEnumerator bagEnumerator(d_nm->mkBagType(boolType));

    for(unsigned i = 0; i < 100; i++)
    {
      cout << *++bagEnumerator << endl;
    }
  }

  void testBagOfUF()
  {
    TypeNode typeNode = d_nm->mkSort("Atom");
    Type sort = typeNode.toType();
    BagEnumerator bagEnumerator(d_nm->mkBagType(typeNode));

    Node actual0 = *bagEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(typeNode).toType()));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual1 = *++bagEnumerator;
    Node expected1 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 0)));
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual2 = *++bagEnumerator;
    Node expected2 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 1)));
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual3 = *++bagEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual4 = *++bagEnumerator;
    Node expected4 = d_nm->mkNode(
        Kind::SINGLETON, d_nm->mkConst(UninterpretedConstant(sort, 2)));
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual5 = *++bagEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual6 = *++bagEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual7 = *++bagEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!bagEnumerator.isFinished());
  }

  void testBagOfFiniteDatatype()
  {
    Datatype dt(d_em, "Colors");
    dt.addConstructor(DatatypeConstructor("red"));
    dt.addConstructor(DatatypeConstructor("green"));
    dt.addConstructor(DatatypeConstructor("blue"));
    TypeNode datatype = TypeNode::fromType(d_em->mkDatatypeType(dt));
    BagEnumerator bagEnumerator(d_nm->mkBagType(datatype));

    Node red = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("red"));

    Node green = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("green"));

    Node blue = d_nm->mkNode(
        APPLY_CONSTRUCTOR,
        DatatypeType(datatype.toType()).getDatatype().getConstructor("blue"));

    Node actual0 = *bagEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(datatype).toType()));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual1 = *++bagEnumerator;
    Node expected1 = d_nm->mkNode(Kind::SINGLETON, red);
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual2 = *++bagEnumerator;
    Node expected2 = d_nm->mkNode(Kind::SINGLETON, green);
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual3 = *++bagEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual4 = *++bagEnumerator;
    Node expected4 = d_nm->mkNode(Kind::SINGLETON, blue);
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual5 = *++bagEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual6 = *++bagEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual7 = *++bagEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!bagEnumerator.isFinished());

    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
  }

  void testBV()
  {
    TypeNode bitVector2 = d_nm->mkBitVectorType(2);
    BagEnumerator bagEnumerator(d_nm->mkBagType(bitVector2));
    Node zero = d_nm->mkConst(BitVector(2u, 0u));
    Node one = d_nm->mkConst(BitVector(2u, 1u));
    Node two = d_nm->mkConst(BitVector(2u, 2u));
    Node three = d_nm->mkConst(BitVector(2u, 3u));
    Node four = d_nm->mkConst(BitVector(2u, 4u));

    Node actual0 = *bagEnumerator;
    Node expected0 =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(bitVector2).toType()));
    TS_ASSERT_EQUALS(expected0, actual0);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual1 = *++bagEnumerator;
    Node expected1 = d_nm->mkNode(Kind::SINGLETON, zero);
    TS_ASSERT_EQUALS(expected1, actual1);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual2 = *++bagEnumerator;
    Node expected2 = d_nm->mkNode(Kind::SINGLETON, one);
    TS_ASSERT_EQUALS(expected2, actual2);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual3 = *++bagEnumerator;
    Node expected3 = d_nm->mkNode(Kind::UNION, expected1, expected2);
    TS_ASSERT_EQUALS(expected3, actual3);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual4 = *++bagEnumerator;
    Node expected4 = d_nm->mkNode(Kind::SINGLETON, two);
    TS_ASSERT_EQUALS(expected4, actual4);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual5 = *++bagEnumerator;
    Node expected5 = d_nm->mkNode(Kind::UNION, expected1, expected4);
    TS_ASSERT_EQUALS(expected5, actual5);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual6 = *++bagEnumerator;
    Node expected6 = d_nm->mkNode(Kind::UNION, expected2, expected4);
    TS_ASSERT_EQUALS(expected6, actual6);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual7 = *++bagEnumerator;
    Node expected7 = d_nm->mkNode(Kind::UNION, expected3, expected4);
    TS_ASSERT_EQUALS(expected7, actual7);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual8 = *++bagEnumerator;
    Node expected8 = d_nm->mkNode(Kind::SINGLETON, three);
    TS_ASSERT_EQUALS(expected8, actual8);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual9 = *++bagEnumerator;
    Node expected9 = d_nm->mkNode(Kind::UNION, expected1, expected8);
    TS_ASSERT_EQUALS(expected9, actual9);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual10 = *++bagEnumerator;
    Node expected10 = d_nm->mkNode(Kind::UNION, expected2, expected8);
    TS_ASSERT_EQUALS(expected10, actual10);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual11 = *++bagEnumerator;
    Node expected11 = d_nm->mkNode(Kind::UNION, expected3, expected8);
    TS_ASSERT_EQUALS(expected11, actual11);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual12 = *++bagEnumerator;
    Node expected12 = d_nm->mkNode(Kind::UNION, expected4, expected8);
    TS_ASSERT_EQUALS(expected12, actual12);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual13 = *++bagEnumerator;
    Node expected13 = d_nm->mkNode(Kind::UNION, expected5, expected8);
    TS_ASSERT_EQUALS(expected13, actual13);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual14 = *++bagEnumerator;
    Node expected14 = d_nm->mkNode(Kind::UNION, expected6, expected8);
    TS_ASSERT_EQUALS(expected14, actual14);
    TS_ASSERT(!bagEnumerator.isFinished());

    Node actual15 = *++bagEnumerator;
    Node expected15 = d_nm->mkNode(Kind::UNION, expected7, expected8);
    TS_ASSERT_EQUALS(expected15, actual15);
    TS_ASSERT(!bagEnumerator.isFinished());

    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
    TS_ASSERT_THROWS(*++bagEnumerator, NoMoreValuesException&);
    TS_ASSERT(!bagEnumerator.isFinished());
  }

}; /* class BagEnumeratorWhite */

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

    cout << endl;
    for(unsigned i = 0; i < 10; i++)
    {
      cout << *bagEnumerator<< endl;
      ++ bagEnumerator;
    }
  }

  void testBagOfIntegers()
  {
    TypeNode integerType = d_nm->integerType();
    BagEnumerator bagEnumerator(d_nm->mkBagType(integerType));

    for(unsigned i = 0; i < 10; i++)
    {
      cout << *bagEnumerator<< endl;
      ++ bagEnumerator;
    }
  }

  void testBagOfUF()
  {
    TypeNode typeNode = d_nm->mkSort("Atom");
    Type sort = typeNode.toType();
    BagEnumerator bagEnumerator(d_nm->mkBagType(typeNode));

    for(unsigned i = 0; i < 10; i++)
    {
      cout << *bagEnumerator<< endl;
      ++ bagEnumerator;
    }
  }

  void testBagOfFiniteDatatype()
  {
    Datatype dt(d_em, "Colors");
    dt.addConstructor(DatatypeConstructor("red"));
    dt.addConstructor(DatatypeConstructor("green"));
    dt.addConstructor(DatatypeConstructor("blue"));
    TypeNode datatype = TypeNode::fromType(d_em->mkDatatypeType(dt));
    BagEnumerator bagEnumerator(d_nm->mkBagType(datatype));

    for(unsigned i = 0; i < 10; i++)
    {
      cout << *bagEnumerator<< endl;
      ++ bagEnumerator;
    }
  }

  void testBV()
  {
    TypeNode bitVector2 = d_nm->mkBitVectorType(2);
    BagEnumerator bagEnumerator(d_nm->mkBagType(bitVector2));

    for(unsigned i = 0; i < 10; i++)
    {
      cout << *bagEnumerator<< endl;
      ++ bagEnumerator;
    }
  }

}; /* class BagEnumeratorWhite */

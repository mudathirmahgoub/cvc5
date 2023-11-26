/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::theory::nullables::NullablesTypeEnumerator
 *
 * These tests depend on the ordering that the NullablesTypeEnumerator use, so
 * it's a white-box test.
 */

#include "expr/dtype.h"
#include "test_smt.h"
#include "theory/nullables/theory_nullables_type_enumerator.h"

namespace cvc5::internal {

using namespace theory;
using namespace kind;
using namespace theory::nullables;

namespace test {

class TestTheoryNullablesTypeEnumerator : public TestSmt
{
};

TEST_F(TestTheoryNullablesTypeEnumerator, nullable_of_booleans)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode boolType = d_nodeManager->booleanType();
  NullableEnumerator nullableEnumerator(
      d_nodeManager->mkNullableType(boolType));
  ASSERT_FALSE(nullableEnumerator.isFinished());

  ASSERT_THROW(*++nullableEnumerator, NoMoreValuesException);
  ASSERT_TRUE(nullableEnumerator.isFinished());
  ASSERT_THROW(*++nullableEnumerator, NoMoreValuesException);
  ASSERT_TRUE(nullableEnumerator.isFinished());
  ASSERT_THROW(*++nullableEnumerator, NoMoreValuesException);
  ASSERT_TRUE(nullableEnumerator.isFinished());
}

}  // namespace test
}  // namespace cvc5::internal

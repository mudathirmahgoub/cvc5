/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Nullable theory type rules.
 */

#include "theory/nullables/theory_nullables_type_rules.h"

#include <sstream>

#include "base/check.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/nullables/null.h"
#include "util/cardinality.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

TypeNode NullTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode NullTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_NULL);
  Null null = n.getConst<Null>();
  return null.getType();
}

TypeNode SomeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SomeTypeRule::computeType(NodeManager* nm,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_SOME);
  TypeNode elementType = n[0].getType(check);
  return nm->mkNullableType(elementType);
}

TypeNode ValTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode ValTypeRule::computeType(NodeManager* nm,
                                  TNode n,
                                  bool check,
                                  std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_VAL);
  TypeNode nullableType = n[0].getType(check);
  if (check)
  {
    if (!nullableType.isNullable())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "NULLABLE_VAL operator expects a "
                                         "nullable, a non-nullable is found");
    }
  }
  return nullableType.getNullableElementType();
}

bool SomeTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == Kind::NULLABLE_SOME);
  // for a nullable to be constant, its element should be constant
  return n[0].isConst();
}

TypeNode NullableLiftTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode NullableLiftTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_LIFT);

  return n[0].getType();
}

TypeNode IsNullTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode IsNullTypeRule::computeType(NodeManager* nm,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_ISNULL);
  TypeNode nullableType = n[0].getType(check);
  if (check)
  {
    if (!nullableType.isNullable())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "NULLABLE_ISNULL operator expects a "
                                         "nullable, a non-nullable is found");
    }
  }
  return NodeManager::currentNM()->booleanType();
}

Cardinality NullablesProperties::computeCardinality(TypeNode type)
{
  return type.getCardinality() + 1;
}

bool NullablesProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded();
}

Node NullablesProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.isNullable());
  return NodeManager::currentNM()->mkConst(Null(type));
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
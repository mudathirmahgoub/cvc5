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

TypeNode ValueTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ValueTypeRule::computeType(NodeManager* nm,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_VALUE);
  TypeNode elementType = n[0].getType(check);
  return nm->mkNullableType(elementType);
}

TypeNode SelectTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode SelectTypeRule::computeType(NodeManager* nm,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_SELECT);
  TypeNode nullableType = n[0].getType(check);
  if (check)
  {
    if (!nullableType.isNullable())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "NULLABLE_SELECT operator expects a "
                                         "nullable, a non-nullable is found");
    }
  }
  return nullableType.getNullableElementType();
}

bool ValueTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == Kind::NULLABLE_VALUE);
  // for a nullable to be constant, its element should be constant
  return n[0].isConst();
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
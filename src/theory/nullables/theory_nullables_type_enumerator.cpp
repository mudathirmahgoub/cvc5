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
 * Nullable enumerator implementation
 */

#include "theory/nullables/theory_nullables_type_enumerator.h"

#include "theory/nullables/null.h"
#include "theory_nullables_type_enumerator.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullableEnumerator::NullableEnumerator(TypeNode type,
                                       TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<NullableEnumerator>(type),
      d_nodeManager(NodeManager::currentNM()),
      d_elementTypeEnumerator(type.getNullableElementType(), tep)
{
  d_currentNullable = d_nodeManager->mkConst(Null(type));
  d_element = *d_elementTypeEnumerator;
}

NullableEnumerator::NullableEnumerator(const NullableEnumerator& enumerator)
    : TypeEnumeratorBase<NullableEnumerator>(enumerator.getType()),
      d_nodeManager(enumerator.d_nodeManager),
      d_elementTypeEnumerator(enumerator.d_elementTypeEnumerator),
      d_currentNullable(enumerator.d_currentNullable),
      d_element(enumerator.d_element)
{
}

NullableEnumerator::~NullableEnumerator() {}

Node NullableEnumerator::operator*()
{
  Trace("nullable-type-enum")
      << "NullableEnumerator::operator* d_currentNullable = "
      << d_currentNullable << std::endl;

  return d_currentNullable;
}

NullableEnumerator& NullableEnumerator::operator++() { return *this; }

bool NullableEnumerator::isFinished()
{
  // nullables sequence is infinite and it never ends
  return false;
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

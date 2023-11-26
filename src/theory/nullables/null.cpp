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
 * A class for null constant
 */

#include "null.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const Null& asa)
{
  return out << "null(" << asa.getType() << ")";
}

size_t NullHashFunction::operator()(const Null& es) const
{
  return std::hash<TypeNode>()(es.getType());
}

Null::Null(const TypeNode& nullableType) : d_type(new TypeNode(nullableType)) {}

Null::Null(const Null& es) : d_type(new TypeNode(es.getType())) {}

Null& Null::operator=(const Null& es)
{
  (*d_type) = es.getType();
  return *this;
}

Null::~Null() {}
const TypeNode& Null::getType() const { return *d_type; }
bool Null::operator==(const Null& es) const
{
  return getType() == es.getType();
}

bool Null::operator!=(const Null& es) const { return !(*this == es); }
bool Null::operator<(const Null& es) const { return getType() < es.getType(); }

bool Null::operator<=(const Null& es) const
{
  return getType() <= es.getType();
}

bool Null::operator>(const Null& es) const { return !(*this <= es); }
bool Null::operator>=(const Null& es) const { return !(*this < es); }
}  // namespace cvc5::internal

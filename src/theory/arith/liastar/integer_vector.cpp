/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Integer vectors and the arithmetic on them used by the lattice algorithms
 * of the liastar extension.
 */

#include "theory/arith/liastar/integer_vector.h"

#include <sstream>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

IntegerVector IntegerVectorUtils::zero(size_t size)
{
  return IntegerVector(size, Integer(0));
}

IntegerVector IntegerVectorUtils::unit(size_t size, size_t i)
{
  Assert(i < size);
  IntegerVector e = zero(size);
  e[i] = Integer(1);
  return e;
}

bool IntegerVectorUtils::isZero(const IntegerVector& a)
{
  for (const Integer& entry : a)
  {
    if (!entry.isZero())
    {
      return false;
    }
  }
  return true;
}

Integer IntegerVectorUtils::dot(const IntegerVector& a, const IntegerVector& b)
{
  Assert(a.size() == b.size());
  Integer result(0);
  for (size_t i = 0, size = a.size(); i < size; i++)
  {
    if (!a[i].isZero() && !b[i].isZero())
    {
      result += a[i] * b[i];
    }
  }
  return result;
}

IntegerVector IntegerVectorUtils::add(const IntegerVector& a,
                                      const IntegerVector& b)
{
  Assert(a.size() == b.size());
  IntegerVector result(a);
  for (size_t i = 0, size = a.size(); i < size; i++)
  {
    result[i] += b[i];
  }
  return result;
}

IntegerVector IntegerVectorUtils::negate(const IntegerVector& a)
{
  IntegerVector result;
  result.reserve(a.size());
  for (const Integer& entry : a)
  {
    result.push_back(-entry);
  }
  return result;
}

void IntegerVectorUtils::addMultiple(IntegerVector& a,
                                     const Integer& c,
                                     const IntegerVector& b)
{
  Assert(a.size() == b.size());
  if (c.isZero())
  {
    return;
  }
  for (size_t i = 0, size = a.size(); i < size; i++)
  {
    if (!b[i].isZero())
    {
      a[i] += c * b[i];
    }
  }
}

void IntegerVectorUtils::makePrimitive(IntegerVector& a)
{
  Integer content(0);
  for (const Integer& entry : a)
  {
    content = content.gcd(entry);
  }
  if (content.isZero() || content.isOne())
  {
    return;
  }
  for (Integer& entry : a)
  {
    entry = entry.exactQuotient(content);
  }
}

Integer IntegerVectorUtils::l1Norm(const IntegerVector& a)
{
  Integer norm(0);
  for (const Integer& entry : a)
  {
    norm += entry.abs();
  }
  return norm;
}

bool IntegerVectorUtils::lessByNorm(const IntegerVector& a,
                                    const IntegerVector& b)
{
  Integer normA = l1Norm(a);
  Integer normB = l1Norm(b);
  if (normA != normB)
  {
    return normA < normB;
  }
  return a < b;
}

std::string IntegerVectorUtils::toString(const IntegerVector& a)
{
  std::stringstream ss;
  ss << "(";
  for (size_t i = 0, size = a.size(); i < size; i++)
  {
    ss << (i == 0 ? "" : ", ") << a[i];
  }
  ss << ")";
  return ss.str();
}

std::string IntegerVectorUtils::toString(
    const std::vector<IntegerVector>& vectors)
{
  std::stringstream ss;
  ss << "{";
  for (size_t i = 0, size = vectors.size(); i < size; i++)
  {
    ss << (i == 0 ? "" : ", ") << toString(vectors[i]);
  }
  ss << "}";
  return ss.str();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

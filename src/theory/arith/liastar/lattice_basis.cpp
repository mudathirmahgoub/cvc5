/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A Z-basis of a sublattice of Z^d.
 */

#include "theory/arith/liastar/lattice_basis.h"

#include <algorithm>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LatticeBasis::LatticeBasis(size_t dimension) : d_dimension(dimension)
{
  for (size_t i = 0; i < dimension; i++)
  {
    d_basis.push_back(IntegerVectorUtils::unit(dimension, i));
  }
}

LatticeBasis::LatticeBasis(size_t dimension,
                           const std::vector<IntegerVector>& basis)
    : d_dimension(dimension), d_basis(basis)
{
  Assert(std::all_of(
      d_basis.begin(), d_basis.end(), [dimension](const IntegerVector& u) {
        return u.size() == dimension;
      }));
}

size_t LatticeBasis::euclid(std::vector<IntegerVector>& vectors,
                            std::vector<Integer>& values)
{
  Assert(vectors.size() == values.size());
  size_t size = vectors.size();
  while (true)
  {
    // the vector with the smallest nonzero value (in absolute value)
    size_t pivot = size;
    for (size_t i = 0; i < size; i++)
    {
      if (!values[i].isZero()
          && (pivot == size || values[i].abs() < values[pivot].abs()))
      {
        pivot = i;
      }
    }
    if (pivot == size)
    {
      // all values are zero
      return size;
    }
    // reduce every other value modulo the pivot value, which leaves a
    // remainder in [0, |values[pivot]|)
    bool done = true;
    for (size_t j = 0; j < size; j++)
    {
      if (j == pivot || values[j].isZero())
      {
        continue;
      }
      Integer q = values[j].euclidianDivideQuotient(values[pivot]);
      values[j] -= q * values[pivot];
      IntegerVectorUtils::addMultiple(vectors[j], -q, vectors[pivot]);
      done = done && values[j].isZero();
    }
    if (done)
    {
      return pivot;
    }
  }
}

IntegerVector LatticeBasis::intersectWithKernel(const IntegerVector& a)
{
  Assert(a.size() == d_dimension);
  std::vector<Integer> values;
  for (const IntegerVector& u : d_basis)
  {
    values.push_back(IntegerVectorUtils::dot(a, u));
  }
  size_t pivot = euclid(d_basis, values);
  if (pivot == d_basis.size())
  {
    // a vanishes on the lattice
    return IntegerVector();
  }
  // values[pivot] is now the gcd of the original values (up to sign), and
  // every other basis vector lies in the kernel of a
  IntegerVector h = d_basis[pivot];
  if (values[pivot].strictlyNegative())
  {
    h = IntegerVectorUtils::negate(h);
  }
  d_basis.erase(d_basis.begin() + pivot);
  d_pivots.clear();
  return h;
}

void LatticeBasis::toHermiteNormalForm()
{
  d_pivots.clear();
  // rows [0, top) are in Hermite normal form
  size_t top = 0;
  for (size_t column = 0; column < d_dimension && top < d_basis.size();
       column++)
  {
    std::vector<IntegerVector> rest(d_basis.begin() + top, d_basis.end());
    std::vector<Integer> values;
    for (const IntegerVector& row : rest)
    {
      values.push_back(row[column]);
    }
    size_t pivot = euclid(rest, values);
    if (pivot != rest.size())
    {
      // make the pivot row the next row of the echelon form
      std::swap(rest[0], rest[pivot]);
      if (rest[0][column].strictlyNegative())
      {
        rest[0] = IntegerVectorUtils::negate(rest[0]);
      }
    }
    std::copy(rest.begin(), rest.end(), d_basis.begin() + top);
    if (pivot == rest.size())
    {
      // no row has a nonzero entry in this column
      continue;
    }
    // bring the entries above the pivot into [0, pivot)
    const IntegerVector& pivotRow = d_basis[top];
    for (size_t r = 0; r < top; r++)
    {
      Integer q = d_basis[r][column].floorDivideQuotient(pivotRow[column]);
      IntegerVectorUtils::addMultiple(d_basis[r], -q, pivotRow);
    }
    d_pivots.push_back(column);
    top++;
  }
  // the basis vectors are linearly independent, so every row has a pivot
  Assert(top == d_basis.size());
}

void LatticeBasis::reduceModulo(IntegerVector& x) const
{
  Assert(x.size() == d_dimension);
  Assert(d_pivots.size() == d_basis.size())
      << "reduceModulo requires a basis in Hermite normal form";
  for (size_t i = 0, rank = d_basis.size(); i < rank; i++)
  {
    size_t column = d_pivots[i];
    Integer q = x[column].floorDivideQuotient(d_basis[i][column]);
    IntegerVectorUtils::addMultiple(x, -q, d_basis[i]);
  }
}

std::string LatticeBasis::toString() const
{
  return IntegerVectorUtils::toString(d_basis);
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

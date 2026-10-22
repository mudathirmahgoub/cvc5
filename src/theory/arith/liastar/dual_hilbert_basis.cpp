/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Hilbert bases of cones given by linear constraints, computed with the dual
 * algorithm.
 */

#include "theory/arith/liastar/dual_hilbert_basis.h"

#include <algorithm>
#include <iterator>

#include "base/check.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

DualHilbertBasis::DualHilbertBasis(
    size_t dimension,
    const std::vector<IntegerVector>& equations,
    const std::vector<IntegerVector>& inequalities,
    const IntegerVector& levelForm)
    : d_equations(equations),
      d_levelForm(levelForm),
      d_truncate(!levelForm.empty()),
      d_units(dimension),
      d_numCuts(0),
      d_hasLevelOneElements(false),
      d_numSums(0)
{
  // Normaliz removes zero and duplicate forms and cuts with the others
  // sorted by L1 norm and then lexicographically, which tends to keep the
  // intermediate Hilbert bases small ([BI], Remark 16(e)). The level form is
  // cut first, so that every later candidate has a nonnegative level.
  std::vector<IntegerVector> forms;
  for (IntegerVector a : inequalities)
  {
    Assert(a.size() == dimension);
    IntegerVectorUtils::makePrimitive(a);
    if (!IntegerVectorUtils::isZero(a) && a != d_levelForm)
    {
      forms.push_back(a);
    }
  }
  std::sort(forms.begin(), forms.end(), IntegerVectorUtils::lessByNorm);
  forms.erase(std::unique(forms.begin(), forms.end()), forms.end());
  if (d_truncate)
  {
    Assert(levelForm.size() == dimension);
    d_forms.push_back(levelForm);
  }
  d_forms.insert(d_forms.end(), forms.begin(), forms.end());
}

void DualHilbertBasis::compute()
{
  // the monoid of the whole space is the lattice L, all of whose points are
  // units
  for (const IntegerVector& e : d_equations)
  {
    d_units.intersectWithKernel(e);
  }
  Trace("liastar-dual") << "lattice: " << d_units.toString() << std::endl;
  for (const IntegerVector& a : d_forms)
  {
    cut(a);
    Trace("liastar-dual") << "after cutting with "
                          << IntegerVectorUtils::toString(a) << ": units "
                          << d_units.toString() << ", Hilbert basis "
                          << IntegerVectorUtils::toString(getHilbertBasis())
                          << std::endl;
    if (d_truncate
        && std::none_of(d_basis.begin(), d_basis.end(), [](const Candidate& c) {
             return c.d_level.isOne();
           }))
    {
      // An element of level 1 of the final monoid is a sum of elements of
      // the current Hilbert basis and a unit, whose levels add up to 1, so
      // one of them would have level 1.
      Trace("liastar-dual") << "no element of level 1" << std::endl;
      d_basis.clear();
      return;
    }
  }
  d_hasLevelOneElements = true;
}

std::vector<IntegerVector> DualHilbertBasis::getHilbertBasis() const
{
  std::vector<IntegerVector> basis;
  for (const Candidate& c : d_basis)
  {
    basis.push_back(c.d_point);
  }
  return basis;
}

DualHilbertBasis::Candidate DualHilbertBasis::makeUnitCandidate(
    const IntegerVector& point, const Integer& value) const
{
  Candidate c;
  c.d_point = point;
  c.d_values = std::vector<Integer>(d_numCuts, Integer(0));
  c.d_values.push_back(value);
  c.d_degree = value;
  c.d_level =
      d_truncate ? IntegerVectorUtils::dot(d_levelForm, point) : Integer(0);
  c.d_isNew = true;
  return c;
}

void DualHilbertBasis::cut(const IntegerVector& a)
{
  // (D1)-(D2): the units on which a does not vanish stop being units; h is
  // the smallest of them on the positive side, with a(h) = g > 0
  IntegerVector h = d_units.intersectWithKernel(a);
  Integer g = h.empty() ? Integer(0) : IntegerVectorUtils::dot(a, h);
  Integer levelOfH = d_truncate && !h.empty()
                         ? IntegerVectorUtils::dot(d_levelForm, h)
                         : Integer(0);

  // (D3)-(D4): split the current Hilbert basis by the sign of a, after
  // reducing each element x modulo h so that |a(x)| < g. This changes x only
  // by a unit of the monoid before the cut.
  std::vector<Candidate> positive;
  std::vector<Candidate> negative;
  std::vector<Candidate> neutral;
  for (Candidate& c : d_basis)
  {
    Integer value = IntegerVectorUtils::dot(a, c.d_point);
    if (!h.empty() && value.abs() >= g)
    {
      Integer m = value.abs().floorDivideQuotient(g);
      if (value.strictlyPositive())
      {
        m = -m;
      }
      IntegerVectorUtils::addMultiple(c.d_point, m, h);
      value += m * g;
      c.d_level += m * levelOfH;
    }
    c.d_values.push_back(value.abs());
    c.d_degree += value.abs();
    c.d_isNew = true;
    int sign = value.sgn();
    std::vector<Candidate>& side =
        sign > 0 ? positive : (sign < 0 ? negative : neutral);
    side.push_back(std::move(c));
  }
  d_basis.clear();

  // (D5): h and -h join the candidates, since the old units must still be
  // generated. Under truncation h is dropped if its level exceeds 1; this
  // only happens when cutting the level form, whose value at h is then g.
  if (!h.empty())
  {
    Candidate hCandidate = makeUnitCandidate(h, g);
    if (!d_truncate || hCandidate.d_level <= Integer(1))
    {
      positive.push_back(std::move(hCandidate));
    }
    negative.push_back(makeUnitCandidate(IntegerVectorUtils::negate(h), g));
  }
  // the candidate lists are kept sorted by degree, see isReducible
  for (std::vector<Candidate>* side : {&positive, &negative, &neutral})
  {
    std::stable_sort(side->begin(), side->end(), lessByDegree);
  }
  Trace("liastar-dual-debug")
      << "cut " << IntegerVectorUtils::toString(a) << ": " << positive.size()
      << " positive, " << negative.size() << " negative, " << neutral.size()
      << " neutral candidates" << std::endl;

  // (D6)-(D8): add the sums of positive and negative candidates that no
  // candidate reduces, until none is left. Sums of two candidates that were
  // both there in the previous round were formed in that round already.
  std::vector<Integer> values;
  Integer degree;
  while (true)
  {
    std::vector<Candidate> newPositive;
    std::vector<Candidate> newNegative;
    std::vector<Candidate> newNeutral;
    for (const Candidate& p : positive)
    {
      for (const Candidate& n : negative)
      {
        if (!p.d_isNew && !n.d_isNew)
        {
          continue;
        }
        if (d_truncate && p.d_level + n.d_level > Integer(1))
        {
          // levels add up, and sums of level 2 or more are not needed
          continue;
        }
        sumValues(p, n, values, degree);
        if (degree.isZero())
        {
          // p + n is a unit of the cut monoid, which is never a candidate;
          // this only happens for h + (-h) = 0
          continue;
        }
        ++d_numSums;
        // the sign of a at p + n
        const Integer& pValue = p.d_values.back();
        const Integer& nValue = n.d_values.back();
        int sign = pValue > nValue ? 1 : (pValue < nValue ? -1 : 0);
        if (isReducible(neutral, values, degree)
            || (sign > 0 && isReducible(positive, values, degree))
            || (sign < 0 && isReducible(negative, values, degree)))
        {
          continue;
        }
        Candidate z;
        z.d_point = IntegerVectorUtils::add(p.d_point, n.d_point);
        z.d_values = values;
        z.d_degree = degree;
        z.d_level = p.d_level + n.d_level;
        z.d_isNew = true;
        std::vector<Candidate>& side =
            sign > 0 ? newPositive : (sign < 0 ? newNegative : newNeutral);
        side.push_back(std::move(z));
      }
    }
    if (newPositive.empty() && newNegative.empty() && newNeutral.empty())
    {
      break;
    }
    // A neutral candidate is in both halfspaces, so it can reduce candidates
    // of either side, while a positive (negative) one only reduces positive
    // (negative) ones. Auto-reduce the new candidates, and remove the old
    // ones that a new one reduces ([BI], Remark 16(c)).
    autoReduce(newNeutral, {});
    autoReduce(newPositive, newNeutral);
    autoReduce(newNegative, newNeutral);
    removeReducible(neutral, newNeutral);
    removeReducible(positive, newNeutral);
    removeReducible(positive, newPositive);
    removeReducible(negative, newNeutral);
    removeReducible(negative, newNegative);
    for (std::vector<Candidate>* side : {&positive, &negative, &neutral})
    {
      for (Candidate& c : *side)
      {
        c.d_isNew = false;
      }
    }
    mergeByDegree(positive, newPositive);
    mergeByDegree(negative, newNegative);
    mergeByDegree(neutral, newNeutral);
  }

  // the Hilbert basis of the monoid in the halfspace a(x) >= 0 consists of
  // the positive and the neutral candidates
  std::move(positive.begin(), positive.end(), std::back_inserter(d_basis));
  std::move(neutral.begin(), neutral.end(), std::back_inserter(d_basis));
  d_numCuts++;
}

void DualHilbertBasis::sumValues(const Candidate& p,
                                 const Candidate& n,
                                 std::vector<Integer>& values,
                                 Integer& degree)
{
  // computed in place, which reuses the memory of `values`
  Assert(p.d_values.size() == n.d_values.size());
  size_t last = p.d_values.size() - 1;
  values.resize(last + 1);
  degree = Integer(0);
  for (size_t i = 0; i < last; i++)
  {
    values[i] = p.d_values[i];
    values[i] += n.d_values[i];
    degree += values[i];
  }
  bool positive = p.d_values[last] >= n.d_values[last];
  values[last] = positive ? p.d_values[last] : n.d_values[last];
  values[last] -= positive ? n.d_values[last] : p.d_values[last];
  degree += values[last];
}

bool DualHilbertBasis::lessByDegree(const Candidate& x, const Candidate& y)
{
  return x.d_degree < y.d_degree;
}

void DualHilbertBasis::mergeByDegree(std::vector<Candidate>& list,
                                     std::vector<Candidate>& added)
{
  std::vector<Candidate> merged;
  merged.reserve(list.size() + added.size());
  std::merge(std::make_move_iterator(list.begin()),
             std::make_move_iterator(list.end()),
             std::make_move_iterator(added.begin()),
             std::make_move_iterator(added.end()),
             std::back_inserter(merged),
             lessByDegree);
  list = std::move(merged);
}

bool DualHilbertBasis::isReducible(const std::vector<Candidate>& list,
                                   const std::vector<Integer>& values,
                                   const Integer& degree)
{
  // The coordinate that is compared first: initially the current form, and
  // then the one at which the previous reducer failed, which tends to fail
  // again ([BI], Remark 6, and Normaliz's reduction.cpp).
  size_t first = values.size() - 1;
  for (const Candidate& y : list)
  {
    if (y.d_degree > degree)
    {
      // the candidates are sorted by degree, and a reducer has at most the
      // degree of the point it reduces
      return false;
    }
    if (y.d_values[first] > values[first])
    {
      continue;
    }
    bool reduces = true;
    for (size_t i = 0, size = values.size(); i < size; i++)
    {
      if (y.d_values[i] > values[i])
      {
        first = i;
        reduces = false;
        break;
      }
    }
    if (reduces)
    {
      return true;
    }
  }
  return false;
}

void DualHilbertBasis::autoReduce(std::vector<Candidate>& list,
                                  const std::vector<Candidate>& reducers)
{
  // a reducer never has a larger degree than the candidate it reduces, so
  // after sorting by degree only earlier candidates can reduce a candidate
  std::stable_sort(list.begin(), list.end(), lessByDegree);
  std::vector<Candidate> irreducible;
  for (Candidate& x : list)
  {
    if (!isReducible(irreducible, x.d_values, x.d_degree)
        && !isReducible(reducers, x.d_values, x.d_degree))
    {
      irreducible.push_back(std::move(x));
    }
  }
  list = std::move(irreducible);
}

void DualHilbertBasis::removeReducible(std::vector<Candidate>& list,
                                       const std::vector<Candidate>& reducers)
{
  list.erase(std::remove_if(list.begin(),
                            list.end(),
                            [&](const Candidate& x) {
                              return isReducible(
                                  reducers, x.d_values, x.d_degree);
                            }),
             list.end());
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

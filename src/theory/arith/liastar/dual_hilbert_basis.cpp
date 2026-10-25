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
#include <limits>
#include <set>
#include <tuple>

#include "base/check.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

//------------------------------------------------------------ DualHilbertBasis

DualHilbertBasis::DualHilbertBasis(
    size_t dimension,
    const std::vector<IntegerVector>& equations,
    const std::vector<IntegerVector>& inequalities,
    const IntegerVector& levelForm)
    : d_lattice(dimension),
      d_levelForm(levelForm),
      d_units(dimension),
      d_hasLevelOneElements(false),
      d_numSums(0),
      d_usedArbitraryPrecision(false)
{
  // the monoid of the whole space is the lattice L, all of whose points are
  // units
  for (const IntegerVector& e : equations)
  {
    Assert(e.size() == dimension);
    d_lattice.intersectWithKernel(e);
  }
  d_lattice.toHermiteNormalForm();
  // Normaliz removes zero and duplicate forms and cuts with the others
  // sorted by L1 norm and then lexicographically, which tends to keep the
  // intermediate Hilbert bases small ([BI], Remark 16(e)). Forms are
  // compared by their restrictions to L: a form that vanishes on L is
  // skipped, and so is one that agrees on L with an earlier one up to a
  // positive factor. The level form is cut first, so that every later
  // candidate has a nonnegative level.
  std::vector<IntegerVector> forms;
  for (IntegerVector a : inequalities)
  {
    Assert(a.size() == dimension);
    IntegerVectorUtils::makePrimitive(a);
    forms.push_back(a);
  }
  std::stable_sort(forms.begin(), forms.end(), IntegerVectorUtils::lessByNorm);
  std::set<IntegerVector> restrictions;
  restrictions.insert(IntegerVectorUtils::zero(d_lattice.getRank()));
  if (!d_levelForm.empty())
  {
    Assert(levelForm.size() == dimension);
    restrictions.insert(getRestriction(d_levelForm));
    d_forms.push_back(levelForm);
  }
  for (const IntegerVector& a : forms)
  {
    if (restrictions.insert(getRestriction(a)).second)
    {
      d_forms.push_back(a);
    }
  }
}

IntegerVector DualHilbertBasis::getRestriction(const IntegerVector& a) const
{
  IntegerVector restriction;
  for (const IntegerVector& u : d_lattice.getBasis())
  {
    restriction.push_back(IntegerVectorUtils::dot(a, u));
  }
  IntegerVectorUtils::makePrimitive(restriction);
  return restriction;
}

void DualHilbertBasis::compute()
{
  try
  {
    run<int64_t>();
  }
  catch (const DualOverflow&)
  {
    Trace("liastar-dual") << "64-bit overflow, computing with arbitrary "
                             "precision"
                          << std::endl;
    d_usedArbitraryPrecision = true;
    run<Integer>();
  }
}

template <typename T>
void DualHilbertBasis::run()
{
  DualHilbertBasisComputation<T> computation(d_lattice, d_forms, d_levelForm);
  try
  {
    computation.compute();
  }
  catch (const DualOverflow&)
  {
    d_numSums += computation.getNumSums();
    throw;
  }
  d_numSums += computation.getNumSums();
  d_hilbertBasis = computation.getHilbertBasis();
  d_units = computation.getUnits();
  d_hasLevelOneElements = computation.hasLevelOneElements();
}

//------------------------------------------------------------ DualArithmetic

template <>
int64_t DualArithmetic<int64_t>::fromInteger(const Integer& x)
{
  static const Integer max(std::numeric_limits<int64_t>::max());
  static const Integer min(std::numeric_limits<int64_t>::min());
  if (x > max || x < min)
  {
    throw DualOverflow();
  }
  return x.getSigned64();
}

template <>
void DualArithmetic<int64_t>::addTo(int64_t& a, const int64_t& b)
{
  if ((b > 0 && a > std::numeric_limits<int64_t>::max() - b)
      || (b < 0 && a < std::numeric_limits<int64_t>::min() - b))
  {
    throw DualOverflow();
  }
  a += b;
}

template <>
Integer DualArithmetic<Integer>::fromInteger(const Integer& x)
{
  return x;
}

template <>
void DualArithmetic<Integer>::addTo(Integer& a, const Integer& b)
{
  a += b;
}

//------------------------------------------------- DualHilbertBasisComputation

template <typename T>
DualHilbertBasisComputation<T>::DualHilbertBasisComputation(
    const LatticeBasis& units,
    const std::vector<IntegerVector>& forms,
    const IntegerVector& levelForm)
    : d_forms(forms),
      d_levelForm(levelForm),
      d_truncate(!levelForm.empty()),
      d_units(units),
      d_numCuts(0),
      d_hasLevelOneElements(false),
      d_numSums(0)
{
}

template <typename T>
void DualHilbertBasisComputation<T>::compute()
{
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
             return c.d_level == T(1);
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

template <typename T>
std::vector<IntegerVector> DualHilbertBasisComputation<T>::getHilbertBasis()
    const
{
  std::vector<IntegerVector> basis;
  for (const Candidate& c : d_basis)
  {
    basis.push_back(c.d_point);
  }
  return basis;
}

template <typename T>
T DualHilbertBasisComputation<T>::getLevel(const IntegerVector& point) const
{
  if (!d_truncate)
  {
    return T(0);
  }
  return DualArithmetic<T>::fromInteger(
      IntegerVectorUtils::dot(d_levelForm, point));
}

template <typename T>
typename DualHilbertBasisComputation<T>::Candidate
DualHilbertBasisComputation<T>::makeUnitCandidate(const IntegerVector& point,
                                                  const Integer& value) const
{
  Candidate c;
  c.d_point = point;
  c.d_values = std::vector<T>(d_numCuts, T(0));
  c.d_values.push_back(DualArithmetic<T>::fromInteger(value));
  c.d_degree = c.d_values.back();
  c.d_oldDegree = T(0);
  c.d_level = getLevel(point);
  c.d_mother = T(0);
  return c;
}

template <typename T>
void DualHilbertBasisComputation<T>::cut(const IntegerVector& a)
{
  // whether the monoid before the cut has no units but 0
  bool pointed = d_units.getRank() == 0;
  // (D1)-(D2): the units on which a does not vanish stop being units; h is
  // the smallest of them on the positive side, with a(h) = g > 0
  IntegerVector h = d_units.intersectWithKernel(a);
  Integer g = h.empty() ? Integer(0) : IntegerVectorUtils::dot(a, h);

  // (D3)-(D4): split the current Hilbert basis by the sign of a, after
  // reducing each element x modulo h so that |a(x)| < g. This changes x only
  // by a unit of the monoid before the cut.
  CutState state;
  state.d_doReduction = true;
  // whether a positive or neutral candidate, and whether any candidate, has
  // level 0; the units h and -h have level 0
  bool positiveAtLevelZero = !pointed;
  bool anyAtLevelZero = !pointed;
  bool first = true;
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
      c.d_level = getLevel(c.d_point);
    }
    T absValue = DualArithmetic<T>::fromInteger(value.abs());
    c.d_oldDegree = c.d_degree;
    c.d_values.push_back(absValue);
    DualArithmetic<T>::addTo(c.d_degree, absValue);
    c.d_mother = T(0);
    if (first || c.d_oldDegree < state.d_minOldDegree)
    {
      state.d_minOldDegree = c.d_oldDegree;
      first = false;
    }
    int sign = value.sgn();
    if (c.d_level == T(0))
    {
      anyAtLevelZero = true;
      positiveAtLevelZero = positiveAtLevelZero || sign >= 0;
    }
    Side& side = sign > 0 ? state.d_positive
                          : (sign < 0 ? state.d_negative : state.d_neutral);
    side.d_candidates.push_back(std::move(c));
  }
  d_basis.clear();

  // (D5): h and -h join the candidates, since the old units must still be
  // generated. Under truncation h is dropped if its level exceeds 1; this
  // only happens when cutting the level form, whose value at h is then g.
  std::vector<Candidate> positiveUnits;
  std::vector<Candidate> negativeUnits;
  if (!h.empty())
  {
    state.d_minOldDegree = T(0);
    Candidate hCandidate = makeUnitCandidate(h, g);
    if (!d_truncate || hCandidate.d_level <= T(1))
    {
      positiveUnits.push_back(std::move(hCandidate));
    }
    negativeUnits.push_back(
        makeUnitCandidate(IntegerVectorUtils::negate(h), g));
  }

  // Truncation shortcuts (comment in Normaliz's cone_dual_mode.cpp). If no
  // positive or neutral candidate has level 0, every positive candidate has
  // level 1, so a sum of level at most 1 has a negative summand of level 0;
  // the negative candidates of level 1 are useless. If no candidate has
  // level 0, every sum has level 2 and none is formed.
  if (d_truncate && !positiveAtLevelZero)
  {
    state.d_doReduction = false;
    std::vector<Candidate>& negative = state.d_negative.d_candidates;
    negative.erase(
        std::remove_if(negative.begin(),
                       negative.end(),
                       [](const Candidate& c) { return c.d_level != T(0); }),
        negative.end());
  }
  bool noSums = d_truncate && !anyAtLevelZero;

  // The units h and -h come first and are old, since their sum is 0, while
  // the sums of the old Hilbert basis elements are new. The others are
  // ordered by degree, which is also the initial order of the reducers.
  std::vector<Candidate> noUnits;
  for (auto [side, units] : {std::make_pair(&state.d_positive, &positiveUnits),
                             std::make_pair(&state.d_negative, &negativeUnits),
                             std::make_pair(&state.d_neutral, &noUnits)})
  {
    std::vector<Candidate> candidates = std::move(side->d_candidates);
    side->d_candidates.clear();
    std::stable_sort(candidates.begin(), candidates.end(), lessByDegree);
    append(*side, *units);
    side->d_firstNew = side->d_candidates.size();
    append(*side, candidates);
  }
  Trace("liastar-dual-debug")
      << "cut " << IntegerVectorUtils::toString(a) << ": "
      << state.d_positive.d_candidates.size() << " positive, "
      << state.d_negative.d_candidates.size() << " negative, "
      << state.d_neutral.d_candidates.size() << " neutral candidates"
      << std::endl;

  // (D6)-(D8): rounds of forming sums and promoting them, until no sum is
  // left in the positive and negative depots
  while (!noSums)
  {
    formSums(state);
    if (!promote(state))
    {
      break;
    }
  }

  // the Hilbert basis of the monoid in the halfspace a(x) >= 0 consists of
  // the positive and the neutral candidates
  d_basis = std::move(state.d_positive.d_candidates);
  std::move(state.d_neutral.d_candidates.begin(),
            state.d_neutral.d_candidates.end(),
            std::back_inserter(d_basis));
  d_numCuts++;
}

template <typename T>
void DualHilbertBasisComputation<T>::formSums(CutState& state)
{
  // The indices of the old and the new candidates of each side, by level.
  // Under truncation, after the level form is cut, every level is 0 or 1, and
  // the sums of two candidates of level 1 are not needed, so those pairs are
  // not even visited. Otherwise all candidates are in group 0.
  bool byLevel = d_truncate && d_numCuts > 0;
  std::vector<size_t> positiveOld[2], positiveNew[2];
  std::vector<size_t> negativeOld[2], negativeNew[2];
  for (auto [side, old, fresh] :
       {std::make_tuple(&state.d_positive, positiveOld, positiveNew),
        std::make_tuple(&state.d_negative, negativeOld, negativeNew)})
  {
    for (size_t i = 0, size = side->d_candidates.size(); i < size; i++)
    {
      size_t group = byLevel && side->d_candidates[i].d_level != T(0) ? 1 : 0;
      (i < side->d_firstNew ? old : fresh)[group].push_back(i);
    }
  }
  Round round;
  const std::vector<Candidate>& positives = state.d_positive.d_candidates;
  const std::vector<Candidate>& negatives = state.d_negative.d_candidates;
  for (size_t pGroup = 0; pGroup < 2; pGroup++)
  {
    for (size_t nGroup = 0; nGroup < 2; nGroup++)
    {
      if (byLevel && pGroup + nGroup > 1)
      {
        continue;
      }
      // the sums of two old candidates were formed in an earlier round
      for (auto [pIndices, nIndices] :
           {std::make_pair(&positiveNew[pGroup], &negativeOld[nGroup]),
            std::make_pair(&positiveNew[pGroup], &negativeNew[nGroup]),
            std::make_pair(&positiveOld[pGroup], &negativeNew[nGroup])})
      {
        for (size_t i : *pIndices)
        {
          for (size_t j : *nIndices)
          {
            formSum(state, positives[i], negatives[j], round);
          }
        }
      }
    }
  }
  // all candidates are old now; the ones promoted next will be new
  for (Side* side : {&state.d_positive, &state.d_negative, &state.d_neutral})
  {
    side->d_firstNew = side->d_candidates.size();
  }
  addToDepot(state.d_positiveDepot, round.d_positive);
  addToDepot(state.d_negativeDepot, round.d_negative);
  addToDepot(state.d_neutralDepot, round.d_neutral);
}

template <typename T>
void DualHilbertBasisComputation<T>::formSum(CutState& state,
                                             const Candidate& p,
                                             const Candidate& n,
                                             Round& round)
{
  if (d_truncate)
  {
    // levels add up, and sums of level 2 or more are not needed
    round.d_level = p.d_level;
    DualArithmetic<T>::addTo(round.d_level, n.d_level);
    if (round.d_level > T(1))
    {
      return;
    }
  }
  if (isPredictedReducible(p, n))
  {
    return;
  }
  // the sign of a at p + n
  const T& pValue = p.d_values.back();
  const T& nValue = n.d_values.back();
  int sign = pValue > nValue ? 1 : (pValue < nValue ? -1 : 0);
  if (sign < 0 && !state.d_doReduction)
  {
    // negative sums are not needed, see CutState::d_doReduction
    return;
  }
  std::vector<T>& values = round.d_values;
  T& degree = round.d_degree;
  sumValues(p, n, values, degree);
  if (degree == T(0))
  {
    // p + n is a unit of the cut monoid, which is never a candidate; this
    // only happens for h + (-h) = 0
    return;
  }
  ++d_numSums;
  if (state.d_doReduction
      && ((sign > 0 && isReducibleBy(state.d_positive, values, degree))
          || (sign < 0 && isReducibleBy(state.d_negative, values, degree))
          || isReducibleBy(state.d_neutral, values, degree)))
  {
    return;
  }
  Candidate z;
  z.d_point = IntegerVectorUtils::add(p.d_point, n.d_point);
  z.d_values = values;
  z.d_degree = degree;
  z.d_oldDegree = p.d_oldDegree;
  DualArithmetic<T>::addTo(z.d_oldDegree, n.d_oldDegree);
  z.d_level = d_truncate ? round.d_level : T(0);
  z.d_mother = sign > 0 ? pValue : (sign < 0 ? nValue : T(0));
  std::vector<Candidate>& side =
      sign > 0 ? round.d_positive
               : (sign < 0 ? round.d_negative : round.d_neutral);
  side.push_back(std::move(z));
}

template <typename T>
bool DualHilbertBasisComputation<T>::isPredictedReducible(const Candidate& p,
                                                          const Candidate& n)
{
  // the differences below are of a value and a smaller one, so they do not
  // overflow
  const T& pv = p.d_values.back();
  const T& nv = n.d_values.back();
  const T& pm = p.d_mother;
  const T& nm = n.d_mother;
  if (pv > nv)
  {
    return nm != T(0) && (nm <= pv || (nm <= pm && pm - nm <= pv - nv));
  }
  if (pv < nv)
  {
    return pm != T(0) && (pm <= nv || (pm <= nm && nm - pm <= nv - pv));
  }
  return pm != T(0) && pm == nm;
}

template <typename T>
bool DualHilbertBasisComputation<T>::promote(CutState& state)
{
  bool reduce = state.d_doReduction;
  if (state.d_positiveDepot.empty() && state.d_negativeDepot.empty())
  {
    // no more sums will be formed, and the neutral ones only need to be
    // auto-reduced
    std::vector<Candidate> neutral = std::move(state.d_neutralDepot);
    state.d_neutralDepot.clear();
    autoReduce(neutral);
    removeReducibleBy(neutral, state.d_neutral);
    append(state.d_neutral, neutral);
    return false;
  }
  // the smallest old degree of a sum formed later
  T next = state.d_minOldDegree;
  bool first = true;
  T minDepot = T(0);
  for (const std::vector<Candidate>* depot :
       {&state.d_positiveDepot, &state.d_negativeDepot})
  {
    for (const Candidate& c : *depot)
    {
      if (first || c.d_oldDegree < minDepot)
      {
        minDepot = c.d_oldDegree;
        first = false;
      }
    }
  }
  DualArithmetic<T>::addTo(next, minDepot);
  T maxOldDegree = next;
  DualArithmetic<T>::addTo(maxOldDegree, next);
  maxOldDegree = maxOldDegree - T(1);
  // Promote the neutral sums first, since they also reduce the sums of the
  // other sides. Without reduction, all sums are promoted, after dropping
  // those that duplicate a candidate.
  std::vector<Candidate> neutral;
  takePromoted(state.d_neutralDepot, maxOldDegree, reduce, neutral);
  if (!reduce)
  {
    removeReducibleBy(neutral, state.d_neutral);
  }
  if (!neutral.empty())
  {
    if (reduce)
    {
      removeReducible(state.d_positiveDepot, neutral);
      removeReducible(state.d_neutralDepot, neutral);
    }
    removeReducible(state.d_negativeDepot, neutral);
    append(state.d_neutral, neutral);
  }
  std::vector<Candidate> positive;
  takePromoted(state.d_positiveDepot, maxOldDegree, reduce, positive);
  if (!reduce)
  {
    removeReducibleBy(positive, state.d_positive);
  }
  if (!positive.empty())
  {
    if (reduce)
    {
      removeReducible(state.d_positiveDepot, positive);
    }
    append(state.d_positive, positive);
  }
  std::vector<Candidate> negative;
  takePromoted(state.d_negativeDepot, maxOldDegree, reduce, negative);
  if (!negative.empty())
  {
    removeReducible(state.d_negativeDepot, negative);
    append(state.d_negative, negative);
  }
  return true;
}

template <typename T>
void DualHilbertBasisComputation<T>::takePromoted(
    std::vector<Candidate>& depot,
    const T& maxOldDegree,
    bool reduce,
    std::vector<Candidate>& promoted)
{
  std::vector<Candidate> rest;
  for (Candidate& c : depot)
  {
    if (!reduce || c.d_oldDegree <= maxOldDegree)
    {
      promoted.push_back(std::move(c));
    }
    else
    {
      rest.push_back(std::move(c));
    }
  }
  depot = std::move(rest);
  if (reduce)
  {
    autoReduce(promoted);
  }
  else
  {
    std::stable_sort(promoted.begin(), promoted.end(), lessByDegree);
  }
}

template <typename T>
void DualHilbertBasisComputation<T>::addToDepot(std::vector<Candidate>& depot,
                                                std::vector<Candidate>& added)
{
  if (added.empty())
  {
    return;
  }
  std::move(added.begin(), added.end(), std::back_inserter(depot));
  // equal value vectors become adjacent, the smallest mother first
  std::stable_sort(
      depot.begin(), depot.end(), [](const Candidate& x, const Candidate& y) {
        if (x.d_values != y.d_values)
        {
          return x.d_values < y.d_values;
        }
        return x.d_mother < y.d_mother;
      });
  depot.erase(std::unique(depot.begin(),
                          depot.end(),
                          [](const Candidate& x, const Candidate& y) {
                            return x.d_values == y.d_values;
                          }),
              depot.end());
}

template <typename T>
void DualHilbertBasisComputation<T>::sumValues(const Candidate& p,
                                               const Candidate& n,
                                               std::vector<T>& values,
                                               T& degree)
{
  // computed in place, which reuses the memory of `values`
  Assert(p.d_values.size() == n.d_values.size());
  size_t last = p.d_values.size() - 1;
  values.resize(last + 1);
  degree = T(0);
  for (size_t i = 0; i < last; i++)
  {
    values[i] = p.d_values[i];
    DualArithmetic<T>::addTo(values[i], n.d_values[i]);
    DualArithmetic<T>::addTo(degree, values[i]);
  }
  bool positive = p.d_values[last] >= n.d_values[last];
  values[last] = positive ? p.d_values[last] : n.d_values[last];
  values[last] -= positive ? n.d_values[last] : p.d_values[last];
  DualArithmetic<T>::addTo(degree, values[last]);
}

template <typename T>
bool DualHilbertBasisComputation<T>::lessByDegree(const Candidate& x,
                                                  const Candidate& y)
{
  return x.d_degree < y.d_degree;
}

template <typename T>
void DualHilbertBasisComputation<T>::append(Side& side,
                                            std::vector<Candidate>& added)
{
  for (Candidate& c : added)
  {
    side.d_order.push_back(side.d_candidates.size());
    side.d_candidates.push_back(std::move(c));
  }
}

template <typename T>
bool DualHilbertBasisComputation<T>::isReducibleBy(Side& side,
                                                   const std::vector<T>& values,
                                                   const T& degree)
{
  // The coordinate that is compared first: initially the current form, and
  // then the one at which the previous reducer failed, which tends to fail
  // again (Normaliz's reduction.cpp).
  size_t size = values.size();
  size_t first = size - 1;
  std::vector<size_t>& order = side.d_order;
  for (size_t j = 0, length = order.size(); j < length; j++)
  {
    const Candidate& y = side.d_candidates[order[j]];
    if (y.d_degree > degree || y.d_values[first] > values[first])
    {
      continue;
    }
    bool reduces = true;
    for (size_t i = 0; i < size; i++)
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
      std::rotate(order.begin(), order.begin() + j, order.begin() + j + 1);
      return true;
    }
  }
  return false;
}

template <typename T>
void DualHilbertBasisComputation<T>::removeReducibleBy(
    std::vector<Candidate>& list, Side& side)
{
  list.erase(std::remove_if(list.begin(),
                            list.end(),
                            [&](const Candidate& x) {
                              return isReducibleBy(
                                  side, x.d_values, x.d_degree);
                            }),
             list.end());
}

template <typename T>
bool DualHilbertBasisComputation<T>::isReducible(
    const std::vector<Candidate>& list,
    const std::vector<T>& values,
    const T& degree)
{
  // The coordinate that is compared first: initially the current form, and
  // then the one at which the previous reducer failed, which tends to fail
  // again (Normaliz's reduction.cpp).
  size_t size = values.size();
  size_t first = size - 1;
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
    for (size_t i = 0; i < size; i++)
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

template <typename T>
void DualHilbertBasisComputation<T>::autoReduce(std::vector<Candidate>& list)
{
  // a reducer never has a larger degree than the candidate it reduces, so
  // after sorting by degree only earlier candidates can reduce a candidate
  std::stable_sort(list.begin(), list.end(), lessByDegree);
  std::vector<Candidate> irreducible;
  for (Candidate& x : list)
  {
    if (!isReducible(irreducible, x.d_values, x.d_degree))
    {
      irreducible.push_back(std::move(x));
    }
  }
  list = std::move(irreducible);
}

template <typename T>
void DualHilbertBasisComputation<T>::removeReducible(
    std::vector<Candidate>& list, const std::vector<Candidate>& reducers)
{
  list.erase(std::remove_if(list.begin(),
                            list.end(),
                            [&](const Candidate& x) {
                              return isReducible(
                                  reducers, x.d_values, x.d_degree);
                            }),
             list.end());
}

template class DualHilbertBasisComputation<int64_t>;
template class DualHilbertBasisComputation<Integer>;

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

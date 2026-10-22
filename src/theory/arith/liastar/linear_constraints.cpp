/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A conjunction of linear constraints over integer variables, as integer
 * matrices.
 */

#include "theory/arith/liastar/linear_constraints.h"

#include <sstream>

#include "base/check.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LinearConstraints::LinearConstraints(size_t numVariables)
    : d_numVariables(numVariables)
{
}

LinearConstraints::LinearConstraints(Node variables, Node conjunction)
    : d_numVariables(variables.getNumChildren()),
      d_variables(variables.begin(), variables.end())
{
  Assert(variables.getKind() == Kind::BOUND_VAR_LIST)
      << "variables: " << variables << std::endl;
  for (size_t i = 0; i < d_numVariables; i++)
  {
    d_indices[d_variables[i]] = i;
  }
  addConjunction(conjunction);
}

void LinearConstraints::addEquation(IntegerVector row)
{
  Assert(row.size() == d_numVariables + 1);
  IntegerVectorUtils::makePrimitive(row);
  d_equations.push_back(row);
}

void LinearConstraints::addInequality(IntegerVector row)
{
  Assert(row.size() == d_numVariables + 1);
  IntegerVectorUtils::makePrimitive(row);
  d_inequalities.push_back(row);
}

void LinearConstraints::addNonnegativity()
{
  for (size_t i = 0; i < d_numVariables; i++)
  {
    addInequality(IntegerVectorUtils::unit(d_numVariables + 1, i));
  }
}

void LinearConstraints::addFalse()
{
  addEquation(IntegerVectorUtils::unit(d_numVariables + 1, d_numVariables));
}

void LinearConstraints::addConjunction(Node conjunction)
{
  Kind k = conjunction.getKind();
  switch (k)
  {
    case Kind::CONST_BOOLEAN:
    {
      if (!conjunction.getConst<bool>())
      {
        addFalse();
      }
      return;
    }
    case Kind::AND:
    {
      for (const Node& child : conjunction)
      {
        addConjunction(child);
      }
      return;
    }
    case Kind::EQUAL:
    {
      addEquation(getDifference(conjunction[0], conjunction[1]));
      return;
    }
    case Kind::GEQ:
    case Kind::LEQ:
    {
      // a >= b is a - b >= 0, and a <= b is b - a >= 0
      bool geq = k == Kind::GEQ;
      addInequality(geq ? getDifference(conjunction[0], conjunction[1])
                        : getDifference(conjunction[1], conjunction[0]));
      return;
    }
    case Kind::GT:
    case Kind::LT:
    {
      // a > b is a - b > 0, i.e. a - b - 1 >= 0 since a - b is an integer
      bool gt = k == Kind::GT;
      IntegerVector row = gt ? getDifference(conjunction[0], conjunction[1])
                             : getDifference(conjunction[1], conjunction[0]);
      row[d_numVariables] -= Integer(1);
      addInequality(row);
      return;
    }
    default: break;
  }
  InternalError() << "Unexpected kind " << k << " in the linear constraint "
                  << conjunction << std::endl;
}

void LinearConstraints::addTerm(Node term,
                                const Rational& factor,
                                std::vector<Rational>& form) const
{
  switch (term.getKind())
  {
    case Kind::CONST_INTEGER:
    case Kind::CONST_RATIONAL:
    {
      form[d_numVariables] += factor * term.getConst<Rational>();
      return;
    }
    case Kind::TO_REAL:
    {
      addTerm(term[0], factor, form);
      return;
    }
    case Kind::NEG:
    {
      addTerm(term[0], -factor, form);
      return;
    }
    case Kind::ADD:
    {
      for (const Node& child : term)
      {
        addTerm(child, factor, form);
      }
      return;
    }
    case Kind::SUB:
    {
      addTerm(term[0], factor, form);
      addTerm(term[1], -factor, form);
      return;
    }
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      // a product of constants and at most one other factor
      Rational product = factor;
      Node other;
      for (const Node& child : term)
      {
        if (child.isConst())
        {
          product *= child.getConst<Rational>();
        }
        else if (other.isNull())
        {
          other = child;
        }
        else
        {
          InternalError() << "Nonlinear term " << term
                          << " in a linear constraint" << std::endl;
        }
      }
      if (other.isNull())
      {
        form[d_numVariables] += product;
      }
      else
      {
        addTerm(other, product, form);
      }
      return;
    }
    default: break;
  }
  auto it = d_indices.find(term);
  if (it == d_indices.end())
  {
    InternalError() << "Unexpected term " << term << " in a linear constraint"
                    << std::endl;
  }
  form[it->second] += factor;
}

IntegerVector LinearConstraints::getDifference(Node a, Node b) const
{
  std::vector<Rational> form(d_numVariables + 1, Rational(0));
  addTerm(a, Rational(1), form);
  addTerm(b, Rational(-1), form);
  Integer denominator(1);
  for (const Rational& coefficient : form)
  {
    denominator = denominator.lcm(coefficient.getDenominator());
  }
  IntegerVector row;
  for (const Rational& coefficient : form)
  {
    Rational scaled = coefficient * Rational(denominator);
    Assert(scaled.isIntegral());
    row.push_back(scaled.getNumerator());
  }
  return row;
}

std::string LinearConstraints::rowToString(const IntegerVector& row) const
{
  std::stringstream ss;
  bool first = true;
  for (size_t i = 0; i <= d_numVariables; i++)
  {
    const Integer& c = row[i];
    bool isConstant = i == d_numVariables;
    if (c.isZero() && !(isConstant && first))
    {
      continue;
    }
    if (first)
    {
      ss << (c.strictlyNegative() ? "-" : "");
    }
    else
    {
      ss << (c.strictlyNegative() ? " - " : " + ");
    }
    first = false;
    Integer abs = c.abs();
    if (isConstant)
    {
      ss << abs;
      continue;
    }
    if (!abs.isOne())
    {
      ss << abs << "*";
    }
    if (d_variables.empty())
    {
      ss << "x" << (i + 1);
    }
    else
    {
      ss << d_variables[i];
    }
  }
  return ss.str();
}

std::string LinearConstraints::toString() const
{
  std::stringstream ss;
  bool first = true;
  for (const IntegerVector& row : d_equations)
  {
    ss << (first ? "" : ", ") << rowToString(row) << " = 0";
    first = false;
  }
  for (const IntegerVector& row : d_inequalities)
  {
    ss << (first ? "" : ", ") << rowToString(row) << " >= 0";
    first = false;
  }
  return first ? "true" : ss.str();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

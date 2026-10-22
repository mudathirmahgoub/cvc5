/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the lattice algorithms of the liastar extension: integer
 * vectors, lattice bases, the dual Hilbert basis algorithm, linear
 * constraints and integer polyhedra.
 *
 * Many expected results are the outputs of Normaliz 3.11.1 on the examples
 * of the Normaliz notes (paper-fmcad26-liastar/normaliz/normaliz_v2_build/
 * examples), whose file names are given in the tests.
 */

#include <algorithm>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "test_smt.h"
#include "theory/arith/liastar/dual_hilbert_basis.h"
#include "theory/arith/liastar/integer_polyhedron.h"
#include "theory/arith/liastar/integer_vector.h"
#include "theory/arith/liastar/lattice_basis.h"
#include "theory/arith/liastar/linear_constraints.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::arith;
using namespace theory::arith::liastar;

namespace test {

class TestLiaStarHilbertBasis : public TestSmt
{
 protected:
  TypeNode intType;
  NodeManager* nm;

  void SetUp() override
  {
    TestSmt::SetUp();
    nm = d_nodeManager.get();
    intType = nm->integerType();
  }

  /** @return the integer vector with the given entries */
  static IntegerVector vec(const std::vector<int>& entries)
  {
    IntegerVector v;
    for (int entry : entries)
    {
      v.push_back(Integer(entry));
    }
    return v;
  }

  /** @return the integer vectors with the given entries */
  static std::vector<IntegerVector> vecs(
      const std::vector<std::vector<int>>& entries)
  {
    std::vector<IntegerVector> vs;
    for (const std::vector<int>& v : entries)
    {
      vs.push_back(vec(v));
    }
    return vs;
  }

  /** @return the vectors sorted lexicographically, to compare them as sets */
  static std::vector<IntegerVector> sorted(std::vector<IntegerVector> vs)
  {
    std::sort(vs.begin(), vs.end());
    return vs;
  }

  /** @return the n unit vectors of Z^n, as inequalities x_i >= 0 */
  static std::vector<IntegerVector> nonnegativity(size_t n)
  {
    std::vector<IntegerVector> forms;
    for (size_t i = 0; i < n; i++)
    {
      forms.push_back(IntegerVectorUtils::unit(n, i));
    }
    return forms;
  }

  /** @return the constraints with the given equations and inequalities */
  static LinearConstraints constraints(
      size_t n,
      const std::vector<std::vector<int>>& equations,
      const std::vector<std::vector<int>>& inequalities)
  {
    LinearConstraints c(n);
    for (const IntegerVector& row : vecs(equations))
    {
      c.addEquation(row);
    }
    for (const IntegerVector& row : vecs(inequalities))
    {
      c.addInequality(row);
    }
    return c;
  }
};

//------------------------------------------------------------ IntegerVector

TEST_F(TestLiaStarHilbertBasis, integerVectorArithmetic)
{
  ASSERT_EQ(Integer(-1), IntegerVectorUtils::dot(vec({2, 3}), vec({1, -1})));
  ASSERT_EQ(vec({3, 2}), IntegerVectorUtils::add(vec({1, 2}), vec({2, 0})));
  ASSERT_EQ(vec({-1, 2}), IntegerVectorUtils::negate(vec({1, -2})));
  IntegerVector a = vec({1, 1});
  IntegerVectorUtils::addMultiple(a, Integer(-2), vec({0, 3}));
  ASSERT_EQ(vec({1, -5}), a);
  IntegerVector b = vec({2, -4, 6});
  IntegerVectorUtils::makePrimitive(b);
  ASSERT_EQ(vec({1, -2, 3}), b);
  ASSERT_TRUE(IntegerVectorUtils::isZero(vec({0, 0})));
  ASSERT_EQ("(1, -2, 0)", IntegerVectorUtils::toString(vec({1, -2, 0})));
}

TEST_F(TestLiaStarHilbertBasis, integerVectorOrder)
{
  // by L1 norm first, lexicographically second
  std::vector<IntegerVector> vs = vecs({{2, 0}, {1, 1}, {1, 0}, {0, 1}});
  std::sort(vs.begin(), vs.end(), IntegerVectorUtils::lessByNorm);
  ASSERT_EQ(vecs({{0, 1}, {1, 0}, {1, 1}, {2, 0}}), vs);
}

//------------------------------------------------------------ LatticeBasis

TEST_F(TestLiaStarHilbertBasis, intersectWithKernel)
{
  // the example of the documentation of intersectWithKernel
  LatticeBasis lattice(2);
  IntegerVector h = lattice.intersectWithKernel(vec({2, 3}));
  ASSERT_EQ(vec({-1, 1}), h);
  ASSERT_EQ(vecs({{3, -2}}), lattice.getBasis());
}

TEST_F(TestLiaStarHilbertBasis, intersectWithKernelGcd)
{
  // the smallest positive value of 2x + 4y on Z^2 is 2
  LatticeBasis lattice(2);
  IntegerVector a = vec({2, 4});
  IntegerVector h = lattice.intersectWithKernel(a);
  ASSERT_EQ(Integer(2), IntegerVectorUtils::dot(a, h));
  ASSERT_EQ(1, lattice.getRank());
  ASSERT_EQ(Integer(0), IntegerVectorUtils::dot(a, lattice.getBasis()[0]));
}

TEST_F(TestLiaStarHilbertBasis, intersectWithKernelVanishing)
{
  // x - y vanishes on Z (1, 1), so the lattice is unchanged
  LatticeBasis lattice(2, vecs({{1, 1}}));
  IntegerVector h = lattice.intersectWithKernel(vec({1, -1}));
  ASSERT_TRUE(h.empty());
  ASSERT_EQ(vecs({{1, 1}}), lattice.getBasis());
}

TEST_F(TestLiaStarHilbertBasis, hermiteNormalForm)
{
  // the examples of the documentation of toHermiteNormalForm
  LatticeBasis plane(2, vecs({{3, -2}, {-1, 1}}));
  plane.toHermiteNormalForm();
  ASSERT_EQ(vecs({{1, 0}, {0, 1}}), plane.getBasis());
  LatticeBasis lattice(3, vecs({{2, 2, 0}, {1, 1, 1}}));
  lattice.toHermiteNormalForm();
  ASSERT_EQ(vecs({{1, 1, 1}, {0, 0, 2}}), lattice.getBasis());
}

TEST_F(TestLiaStarHilbertBasis, reduceModulo)
{
  LatticeBasis line(2, vecs({{-1, 1}}));
  line.toHermiteNormalForm();
  ASSERT_EQ(vecs({{1, -1}}), line.getBasis());
  IntegerVector x = vec({5, -4});
  line.reduceModulo(x);
  ASSERT_EQ(vec({0, 1}), x);
  // the representative of (2, 0, 3) modulo Z (1, 1, 1) + Z (0, 0, 2)
  LatticeBasis lattice(3, vecs({{2, 2, 0}, {1, 1, 1}}));
  lattice.toHermiteNormalForm();
  IntegerVector y = vec({2, 0, 3});
  lattice.reduceModulo(y);
  ASSERT_EQ(vec({0, -2, 1}), y);
}

//------------------------------------------------------------ DualHilbertBasis

TEST_F(TestLiaStarHilbertBasis, dualCone2)
{
  // 2cone_ineq.in: -x + 2y >= 0, 3x - y >= 0, traced in the documentation
  // of DualHilbertBasis
  DualHilbertBasis dual(2, {}, vecs({{-1, 2}, {3, -1}}));
  dual.compute();
  ASSERT_EQ(sorted(vecs({{1, 1}, {1, 2}, {1, 3}, {2, 1}})),
            sorted(dual.getHilbertBasis()));
  ASSERT_EQ(0, dual.getUnits().getRank());
}

TEST_F(TestLiaStarHilbertBasis, dualWholeSpace)
{
  // without inequalities every point is a unit
  DualHilbertBasis dual(3, {}, {});
  dual.compute();
  ASSERT_TRUE(dual.getHilbertBasis().empty());
  ASSERT_EQ(3, dual.getUnits().getRank());
}

TEST_F(TestLiaStarHilbertBasis, dualHalfplane)
{
  // x + y >= 0 contains the line Z (1, -1), and one more element (with
  // x + y = 1) generates it modulo the line
  IntegerVector a = vec({1, 1});
  DualHilbertBasis dual(2, {}, {a});
  dual.compute();
  ASSERT_EQ(1, dual.getUnits().getRank());
  ASSERT_EQ(1, dual.getHilbertBasis().size());
  ASSERT_EQ(Integer(1), IntegerVectorUtils::dot(a, dual.getHilbertBasis()[0]));
}

TEST_F(TestLiaStarHilbertBasis, dualPlane)
{
  // plane.in: x + y - z = 0 in the nonnegative orthant
  DualHilbertBasis dual(3, vecs({{1, 1, -1}}), nonnegativity(3));
  dual.compute();
  ASSERT_EQ(sorted(vecs({{0, 1, 1}, {1, 0, 1}})),
            sorted(dual.getHilbertBasis()));
}

TEST_F(TestLiaStarHilbertBasis, dualMagicSquares)
{
  // 3x3magic.in: nonnegative 3x3 squares with equal row, column and diagonal
  // sums
  std::vector<IntegerVector> equations = vecs({{1, 1, 1, -1, -1, -1, 0, 0, 0},
                                               {1, 1, 1, 0, 0, 0, -1, -1, -1},
                                               {0, 1, 1, -1, 0, 0, -1, 0, 0},
                                               {1, 0, 1, 0, -1, 0, 0, -1, 0},
                                               {1, 1, 0, 0, 0, -1, 0, 0, -1},
                                               {0, 1, 1, 0, -1, 0, 0, 0, -1},
                                               {1, 1, 0, 0, -1, 0, -1, 0, 0}});
  DualHilbertBasis dual(9, equations, nonnegativity(9));
  dual.compute();
  ASSERT_EQ(sorted(vecs({{0, 2, 1, 2, 1, 0, 1, 0, 2},
                         {1, 0, 2, 2, 1, 0, 0, 2, 1},
                         {1, 1, 1, 1, 1, 1, 1, 1, 1},
                         {1, 2, 0, 0, 1, 2, 2, 0, 1},
                         {2, 0, 1, 0, 1, 2, 1, 2, 0}})),
            sorted(dual.getHilbertBasis()));
  ASSERT_EQ(0, dual.getUnits().getRank());
}

TEST_F(TestLiaStarHilbertBasis, dualArbitraryPrecision)
{
  // The lattice x = 2^70 y cut with x >= 0 has the Hilbert basis
  // {(2^70, 1)}, where x does not fit into 64 bits, so the computation is
  // repeated with arbitrary precision.
  Integer big("1180591620717411303424");
  IntegerVector equation = {Integer(1), -big};
  DualHilbertBasis dual(2, {equation}, vecs({{1, 0}}));
  dual.compute();
  ASSERT_TRUE(dual.usedArbitraryPrecision());
  ASSERT_EQ(std::vector<IntegerVector>({{big, Integer(1)}}),
            dual.getHilbertBasis());
  // small values do not need it
  DualHilbertBasis small(2, {}, vecs({{-1, 2}, {3, -1}}));
  small.compute();
  ASSERT_FALSE(small.usedArbitraryPrecision());
}

TEST_F(TestLiaStarHilbertBasis, dualTruncation)
{
  // x >= 1 homogenized to x - t >= 0 with level t: the irreducible points of
  // level at most 1 are (1, 0) (level 0) and (1, 1) (level 1)
  DualHilbertBasis dual(2, {}, vecs({{1, -1}}), vec({0, 1}));
  dual.compute();
  ASSERT_TRUE(dual.hasLevelOneElements());
  ASSERT_EQ(sorted(vecs({{1, 0}, {1, 1}})), sorted(dual.getHilbertBasis()));
}

//------------------------------------------------------------ LinearConstraints

TEST_F(TestLiaStarHilbertBasis, linearConstraintsFromNodes)
{
  // the example of the documentation of LinearConstraints
  Node x = nm->mkBoundVar("x", intType);
  Node y = nm->mkBoundVar("y", intType);
  Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, x, y);
  Node two = nm->mkConstInt(Rational(2));
  Node five = nm->mkConstInt(Rational(5));
  Node half = nm->mkConstReal(Rational(1, 2));
  Node sum = nm->mkNode(Kind::ADD, x, y);
  Node twoY = nm->mkNode(Kind::MULT, two, y);
  Node realY = nm->mkNode(Kind::TO_REAL, y);
  Node atLeastTwo = nm->mkNode(Kind::GEQ, sum, two);
  Node lessThanFive = nm->mkNode(Kind::LT, x, five);
  Node equal = nm->mkNode(Kind::EQUAL, x, twoY);
  Node atLeastHalf = nm->mkNode(Kind::GEQ, realY, half);
  Node conjunction =
      nm->mkNode(Kind::AND, {atLeastTwo, lessThanFive, equal, atLeastHalf});

  LinearConstraints c(variables, conjunction);

  ASSERT_EQ(2, c.getNumVariables());
  ASSERT_EQ(vecs({{1, 1, -2}, {-1, 0, 4}, {0, 2, -1}}), c.getInequalities());
  ASSERT_EQ(vecs({{1, -2, 0}}), c.getEquations());
  ASSERT_EQ("x - 2*y = 0, x + y - 2 >= 0, -x + 4 >= 0, 2*y - 1 >= 0",
            c.toString());
}

TEST_F(TestLiaStarHilbertBasis, linearConstraintsTerms)
{
  // (> (- (* 3 x) y) (- 9)) and (<= x (+ y 1)), where the first is not in
  // the normal form of the rewriter
  Node x = nm->mkBoundVar("x", intType);
  Node y = nm->mkBoundVar("y", intType);
  Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, x, y);
  Node one = nm->mkConstInt(Rational(1));
  Node three = nm->mkConstInt(Rational(3));
  Node nine = nm->mkConstInt(Rational(9));
  Node threeX = nm->mkNode(Kind::MULT, three, x);
  Node difference = nm->mkNode(Kind::SUB, threeX, y);
  Node minusNine = nm->mkNode(Kind::NEG, nine);
  Node greater = nm->mkNode(Kind::GT, difference, minusNine);
  Node yPlusOne = nm->mkNode(Kind::ADD, y, one);
  Node atMost = nm->mkNode(Kind::LEQ, x, yPlusOne);
  Node conjunction = nm->mkNode(Kind::AND, greater, atMost);

  LinearConstraints c(variables, conjunction);

  // 3x - y + 9 > 0 is 3x - y + 8 >= 0, and x <= y + 1 is -x + y + 1 >= 0
  ASSERT_EQ(vecs({{3, -1, 8}, {-1, 1, 1}}), c.getInequalities());
  ASSERT_TRUE(c.getEquations().empty());
}

TEST_F(TestLiaStarHilbertBasis, linearConstraintsConstants)
{
  Node x = nm->mkBoundVar("x", intType);
  Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, x);
  LinearConstraints trueConstraints(variables, nm->mkConst(true));
  ASSERT_TRUE(trueConstraints.getEquations().empty());
  ASSERT_TRUE(trueConstraints.getInequalities().empty());
  ASSERT_EQ("true", trueConstraints.toString());
  // false is 1 = 0
  LinearConstraints falseConstraints(variables, nm->mkConst(false));
  ASSERT_EQ(vecs({{0, 1}}), falseConstraints.getEquations());
}

//------------------------------------------------------------ IntegerPolyhedron

TEST_F(TestLiaStarHilbertBasis, polyhedronStrictCone)
{
  // 2cone_int.in: -x + 2y > 0 and 3x - y > 0, i.e. -x + 2y - 1 >= 0 and
  // 3x - y - 1 >= 0
  IntegerPolyhedron p(constraints(2, {}, {{-1, 2, -1}, {3, -1, -1}}));
  ASSERT_FALSE(p.isEmpty());
  ASSERT_EQ(vecs({{1, 1}, {1, 2}}), p.getModuleGenerators());
  ASSERT_EQ(vecs({{1, 1}, {1, 2}, {2, 1}, {1, 3}}), p.getHilbertBasis());
  ASSERT_TRUE(p.getMaximalSubspace().empty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronRationalConstants)
{
  // InhomIneq.in: y >= -1/2, y <= 3/2 and -x + y <= 3/2
  Node x = nm->mkBoundVar("x", intType);
  Node y = nm->mkBoundVar("y", intType);
  Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, x, y);
  Node realX = nm->mkNode(Kind::TO_REAL, x);
  Node realY = nm->mkNode(Kind::TO_REAL, y);
  Node minusHalf = nm->mkConstReal(Rational(-1, 2));
  Node threeHalves = nm->mkConstReal(Rational(3, 2));
  Node lower = nm->mkNode(Kind::GEQ, realY, minusHalf);
  Node upper = nm->mkNode(Kind::LEQ, realY, threeHalves);
  Node minusX = nm->mkNode(Kind::NEG, realX);
  Node difference = nm->mkNode(Kind::ADD, minusX, realY);
  Node slanted = nm->mkNode(Kind::LEQ, difference, threeHalves);
  Node conjunction = nm->mkNode(Kind::AND, lower, upper, slanted);

  IntegerPolyhedron p(LinearConstraints(variables, conjunction));

  ASSERT_EQ(vecs({{-1, 0}, {0, 1}}), p.getModuleGenerators());
  ASSERT_EQ(vecs({{1, 0}}), p.getHilbertBasis());
  ASSERT_TRUE(p.getMaximalSubspace().empty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronPolytope)
{
  // NumSemi.in: 6x + 10y + 15z = 97 with x, y, z >= 0 has six solutions
  LinearConstraints c = constraints(3, {{6, 10, 15, -97}}, {});
  c.addNonnegativity();
  IntegerPolyhedron p(c);
  ASSERT_EQ(
      vecs({{2, 1, 5}, {2, 4, 3}, {2, 7, 1}, {7, 1, 3}, {7, 4, 1}, {12, 1, 1}}),
      p.getModuleGenerators());
  ASSERT_TRUE(p.getHilbertBasis().empty());
  ASSERT_TRUE(p.getMaximalSubspace().empty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronParity)
{
  // x = 2y + 1 and x >= 3: the odd x >= 3, i.e. (3, 1) + Z>=0 (2, 1)
  IntegerPolyhedron p(constraints(2, {{1, -2, -1}}, {{1, 0, -3}}));
  ASSERT_EQ(vecs({{3, 1}}), p.getModuleGenerators());
  ASSERT_EQ(vecs({{2, 1}}), p.getHilbertBasis());
  ASSERT_TRUE(p.getMaximalSubspace().empty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronLine)
{
  // the example of the documentation of IntegerPolyhedron: x + y = 2
  IntegerPolyhedron p(constraints(2, {{1, 1, -2}}, {}));
  ASSERT_EQ(vecs({{0, 2}}), p.getModuleGenerators());
  ASSERT_TRUE(p.getHilbertBasis().empty());
  ASSERT_EQ(vecs({{1, -1}}), p.getMaximalSubspace());
  ASSERT_EQ(vecs({{1, -1}}), p.getRecessionMonoidGenerators());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronHalfplane)
{
  // x + y >= 0 is the cone Z>=0 (0, 1) + Z (1, -1)
  IntegerPolyhedron p(constraints(2, {}, {{1, 1, 0}}));
  ASSERT_EQ(vecs({{0, 0}}), p.getModuleGenerators());
  ASSERT_EQ(vecs({{0, 1}}), p.getHilbertBasis());
  ASSERT_EQ(vecs({{1, -1}}), p.getMaximalSubspace());
  ASSERT_EQ(vecs({{0, 1}, {1, -1}}), p.getRecessionMonoidGenerators());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronWholeSpace)
{
  // no constraints: Z^2 = 0 + Z (1, 0) + Z (0, 1)
  IntegerPolyhedron whole(constraints(2, {}, {}));
  ASSERT_EQ(vecs({{0, 0}}), whole.getModuleGenerators());
  ASSERT_TRUE(whole.getHilbertBasis().empty());
  ASSERT_EQ(vecs({{1, 0}, {0, 1}}), whole.getMaximalSubspace());
  // the nonnegative orthant: 0 + Z>=0 (1, 0) + Z>=0 (0, 1)
  LinearConstraints c(2);
  c.addNonnegativity();
  IntegerPolyhedron orthant(c);
  ASSERT_EQ(vecs({{0, 0}}), orthant.getModuleGenerators());
  ASSERT_EQ(vecs({{0, 1}, {1, 0}}), orthant.getHilbertBasis());
  ASSERT_TRUE(orthant.getMaximalSubspace().empty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronEmpty)
{
  // x >= 1 and x <= 0
  ASSERT_TRUE(
      IntegerPolyhedron(constraints(1, {}, {{1, -1}, {-1, 0}})).isEmpty());
  // false
  LinearConstraints c(1);
  c.addFalse();
  ASSERT_TRUE(IntegerPolyhedron(c).isEmpty());
  // x <= -1 has solutions, but no nonnegative ones
  LinearConstraints negative = constraints(1, {}, {{-1, -1}});
  ASSERT_FALSE(IntegerPolyhedron(negative).isEmpty());
  negative.addNonnegativity();
  ASSERT_TRUE(IntegerPolyhedron(negative).isEmpty());
}

TEST_F(TestLiaStarHilbertBasis, polyhedronEmptyLattice)
{
  // the example of the documentation of IntegerPolyhedron: x = 2z and
  // x = 2w + 1 over (x z w) have rational solutions but no integer one
  IntegerPolyhedron p(constraints(3, {{1, -2, 0, 0}, {1, 0, -2, -1}}, {}));
  ASSERT_TRUE(p.isEmpty());
  ASSERT_TRUE(p.getModuleGenerators().empty());
  ASSERT_TRUE(p.getHilbertBasis().empty());
  ASSERT_TRUE(p.getMaximalSubspace().empty());
  // 2x = 1 together with y >= 0, which has a nonzero recession direction
  ASSERT_TRUE(
      IntegerPolyhedron(constraints(2, {{2, 0, -1}}, {{0, 1, 0}})).isEmpty());
}

}  // namespace test
}  // namespace cvc5::internal

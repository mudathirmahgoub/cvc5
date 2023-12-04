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
 * Solver for the theory of nullables.
 */

#include "theory/nullables/nullables_solver.h"

#include "expr/skolem_manager.h"
#include "theory/nullables/inference_manager.h"
#include "theory/nullables/lift_op.h"
#include "theory/nullables/null.h"
#include "theory/nullables/solver_state.h"
#include "theory/nullables/term_registry.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullablesSolver::NullablesSolver(Env& env,
                                 SolverState& s,
                                 InferenceManagerBuffered& im)
    : EnvObj(env), d_state(s), d_im(&im)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

NullablesSolver::~NullablesSolver() {}

void NullablesSolver::checkBasicOperations()
{
  for (const auto& pair : d_state.getNullables())
  {
    Node eqc = pair.first;
    auto it = pair.second.cbegin();
    auto end = pair.second.cend();
    while (it != end)
    {
      Node n = (*it);
      it++;
      if (it == end)
      {
        continue;
      }
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::NULLABLE_SOME:
        {
          auto it2 = it;
          checkValue(n, it2, end);
          break;
        }
        case Kind::NULLABLE_NULL:
        {
          auto it2 = it;
          checkNull(n, it2, end);
          break;
        }
        default: break;
      }
    }
  }
}

bool NullablesSolver::checkSplit()
{
  // get the relevant term set, currently all nullable equivalence classes
  // in the equality engine
  eq::EqClassesIterator repIt =
      eq::EqClassesIterator(d_state.getEqualityEngine());
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    ++repIt;
    if (!eqc.getType().isNullable())
    {
      // we only care about nullable terms
      continue;
    }
    if (isNullOrValue(eqc))
    {
      // ignore terms that are equal to nullable.null or nullable.some
      continue;
    }
    // we need to split
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    TypeNode type = eqc.getType();
    Node null = nm->mkConst(Null(type));

    Node skolem = sm->mkSkolemFunction(
        SkolemFunId::NULLABLES_SPLIT, type.getNullableElementType(), {eqc});
    Node value = nm->mkNode(Kind::NULLABLE_SOME, skolem);
    Node equalNull = eqc.eqNode(null);
    Node equalValue = eqc.eqNode(value);
    Node lemma = equalNull.orNode(equalValue);
    d_im->addPendingLemma(lemma, InferenceId::NULLABLES_SPLIT);
    return true;
  }
  return false;
}

void NullablesSolver::checkValue(const Node& n1,
                                 std::vector<Node>::const_iterator it,
                                 std::vector<Node>::const_iterator end)
{
  Assert(n1.getKind() == Kind::NULLABLE_SOME);
  do
  {
    Node n2 = *it;
    it++;
    if (n2.getKind() == Kind::NULLABLE_SOME)
    {
      Node x = n1[0];
      Node y = n2[0];
      Node premise = n1.eqNode(n2);
      Node conclusion = x.eqNode(y);
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_INJECT);
    }
    if (n2.getKind() == Kind::NULLABLE_NULL)
    {
      Node premise = n1.eqNode(n2);
      Node conclusion = d_false;
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_CLASH);
    }
  } while (it != end);
}

void NullablesSolver::checkNull(const Node& n1,
                                std::vector<Node>::const_iterator it,
                                std::vector<Node>::const_iterator end)
{
  Assert(n1.getKind() == Kind::NULLABLE_NULL);
  do
  {
    Node n2 = *it;
    it++;
    if (n2.getKind() == Kind::NULLABLE_SOME)
    {
      Node premise = n1.eqNode(n2);
      Node conclusion = d_false;
      Node lemma = premise.notNode().orNode(conclusion);
      d_im->addPendingLemma(lemma, InferenceId::NULLABLES_INJECT);
    }
  } while (it != end);
}

bool NullablesSolver::isNullOrValue(Node eqc)
{
  eq::EqClassIterator it =
      eq::EqClassIterator(eqc, d_state.getEqualityEngine());
  while (!it.isFinished())
  {
    Node n = *it;
    ++it;
    if (n.getKind() == Kind::NULLABLE_NULL
        || n.getKind() == Kind::NULLABLE_SOME)
    {
      return true;
    }
  }
  return false;
}

Node NullablesSolver::getValue(Node eqc)
{
  eq::EqClassIterator it =
      eq::EqClassIterator(eqc, d_state.getEqualityEngine());
  while (!it.isFinished())
  {
    Node n = *it;
    ++it;
    if (n.getKind() == Kind::NULLABLE_SOME)
    {
      return n[0];
    }
  }
  return Node::null();
}

bool NullablesSolver::checkLift()
{
  // get the relevant term set, currently all nullable equivalence classes
  // in the equality engine
  eq::EqClassesIterator repIt =
      eq::EqClassesIterator(d_state.getEqualityEngine());
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    ++repIt;
    NodeManager* nm = NodeManager::currentNM();
    if (eqc.getKind() == Kind::NULLABLE_LIFT)
    {
      Kind liftKind = eqc.getOperator().getConst<LiftOp>().getKind();
      Trace("nullables-check")
          << "NullablesSolver::checkLift()::eqc: " << eqc << std::endl;
      std::vector<Node> args;
      std::vector<Node> premises;
      for (Node n : eqc)
      {
        Node childRep = d_state.getRepresentative(n);
        Trace("nullables-check")
            << "NullablesSolver::checkLift()::childRep: " << childRep
            << std::endl;
        Assert(d_state.hasTerm(childRep));
        if (childRep.getKind() == Kind::NULLABLE_NULL)
        {
          // the result is null
          Node null = nm->mkConst(Null(eqc.getType()));
          Node nullArgument = nm->mkConst(Null(n.getType()));
          Node premise = n.eqNode(nullArgument);
          Node conclusion = eqc.eqNode(null);
          Node lemma = premise.notNode().orNode(conclusion);
          d_im->addPendingLemma(lemma, InferenceId::NULLABLES_LIFT_NULL);
          return true;
        }
        Node value = getValue(childRep);
        if (value.isNull())
        {
          // keep looking, we may find a null argument
          continue;
        }
        args.push_back(value);
        premises.push_back(
            childRep.eqNode(nm->mkNode(Kind::NULLABLE_SOME, value)));
      }
      if (args.size() == eqc.getNumChildren())
      {
        Node premise = nm->mkAnd(premises);
        Trace("nullables-check")
            << "NullablesSolver::checkLift()::premise: " << eqc << std::endl;
        Trace("nullables-check")
            << "NullablesSolver::checkLift()::args: " << args << std::endl;
        Node result =
            nm->mkNode(Kind::NULLABLE_SOME, nm->mkNode(liftKind, args));
        Node conclusion = eqc.eqNode(result);
        Node lemma = premise.notNode().orNode(conclusion);
        d_im->addPendingLemma(lemma, InferenceId::NULLABLES_LIFT_SOME);
        return true;
      }
    }
  }
  return false;
}

bool NullablesSolver::checkLift(Node eqc) {}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

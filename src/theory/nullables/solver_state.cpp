/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of nullables state object.
 */

#include "theory/nullables/solver_state.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

SolverState::SolverState(Env& env, Valuation val)
    : TheoryState(env, val), d_partElementSkolems(env.getUserContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_nm = NodeManager::currentNM();
}

void SolverState::registerNullable(TNode n)
{
  Assert(n.getType().isNullable());
  d_nullables.insert(n);
}

void SolverState::registerCountTerm(Node nullable, Node element, Node skolem)
{
  Assert(nullable.getType().isNullable() && nullable == getRepresentative(nullable));
  Assert(element.getType() == nullable.getType().getNullableElementType()
         && element == getRepresentative(element));
  Assert(skolem.isVar() && skolem.getType().isInteger());
  std::pair<Node, Node> pair = std::make_pair(element, skolem);
  if (std::find(d_nullableElements[nullable].begin(), d_nullableElements[nullable].end(), pair)
      == d_nullableElements[nullable].end())
  {
    d_nullableElements[nullable].push_back(pair);
  }
}

void SolverState::registerGroupTerm(Node n)
{
  std::shared_ptr<context::CDHashSet<Node>> set =
      std::make_shared<context::CDHashSet<Node>>(d_env.getUserContext());
  d_partElementSkolems[n] = set;
}

void SolverState::registerCardinalityTerm(Node n, Node skolem)
{
  Assert(n.getKind() == Kind::NULLABLE_CARD);
  Assert(skolem.isVar());
  d_cardTerms[n] = skolem;
}

Node SolverState::getCardinalitySkolem(Node n)
{
  Assert(n.getKind() == Kind::NULLABLE_CARD);
  Node nullable = getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(Kind::NULLABLE_CARD, nullable);
  return d_cardTerms[cardTerm];
}

bool SolverState::hasCardinalityTerms() const { return !d_cardTerms.empty(); }

const std::set<Node>& SolverState::getNullables() { return d_nullables; }

const std::map<Node, Node>& SolverState::getCardinalityTerms()
{
  return d_cardTerms;
}

std::set<Node> SolverState::getElements(Node B)
{
  Node nullable = getRepresentative(B);
  std::set<Node> elements;
  std::vector<std::pair<Node, Node>> pairs = d_nullableElements[nullable];
  for (std::pair<Node, Node> pair : pairs)
  {
    elements.insert(pair.first);
  }
  return elements;
}

const std::vector<std::pair<Node, Node>>& SolverState::getElementCountPairs(
    Node n)
{
  Node nullable = getRepresentative(n);
  return d_nullableElements[nullable];
}

struct NullablesDeqAttributeId
{
};
typedef expr::Attribute<NullablesDeqAttributeId, Node> NullablesDeqAttribute;

void SolverState::collectDisequalNullableTerms()
{
  eq::EqClassIterator it = eq::EqClassIterator(d_false, d_ee);
  while (!it.isFinished())
  {
    Node n = (*it);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isNullable())
    {
      Trace("nullables-eqc") << "Disequal terms: " << n << std::endl;
      Node A = getRepresentative(n[0]);
      Node B = getRepresentative(n[1]);
      Node equal = A <= B ? A.eqNode(B) : B.eqNode(A);
      if (d_deq.find(equal) == d_deq.end())
      {
        TypeNode elementType = A.getType().getNullableElementType();
        SkolemManager* sm = d_nm->getSkolemManager();
        Node skolem = sm->mkSkolemFunction(
            SkolemFunId::NULLABLES_DEQ_DIFF, elementType, {A, B});
        d_deq[equal] = skolem;
      }
    }
    ++it;
  }
}

const std::map<Node, Node>& SolverState::getDisequalNullableTerms() { return d_deq; }

void SolverState::registerPartElementSkolem(Node group, Node skolemElement)
{
  Assert(group.getKind() == Kind::TABLE_GROUP);
  Assert(skolemElement.getType() == group[0].getType().getNullableElementType());
  d_partElementSkolems[group].get()->insert(skolemElement);
}

std::shared_ptr<context::CDHashSet<Node>> SolverState::getPartElementSkolems(
    Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  return d_partElementSkolems[n];
}

void SolverState::reset()
{
  d_nullableElements.clear();
  d_nullables.clear();
  d_deq.clear();
  d_cardTerms.clear();
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

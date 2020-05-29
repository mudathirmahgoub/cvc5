/*********************                                                        */
/*! \file solver_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of bags state object
 **/

#include "theory/bags/solver_state.h"

#include "expr/emptybag.h"
#include "theory/bags/theory_bags_private.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

SolverState::SolverState(TheoryBagsPrivate& p,
                         eq::EqualityEngine& e,
                         context::Context* c,
                         context::UserContext* u)
    : d_conflict(c), d_parent(p), d_ee(e)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void SolverState::reset()
{
  d_bag_eqc.clear();
  d_eqc_emptybag.clear();
}

void SolverState::registerEqc(TypeNode tn, Node r)
{
  if (tn.isBag())
  {
    d_bag_eqc.push_back(r);
  }
}

void SolverState::registerTerm(Node r, TypeNode tnn, Node n)
{
  Kind nk = n.getKind();
}

bool SolverState::areEqual(Node a, Node b) const
{
  if (a == b)
  {
    return true;
  }
  if (d_ee.hasTerm(a) && d_ee.hasTerm(b))
  {
    return d_ee.areEqual(a, b);
  }
  return false;
}

bool SolverState::areDisequal(Node a, Node b) const
{
  if (a == b)
  {
    return false;
  }
  else if (d_ee.hasTerm(a) && d_ee.hasTerm(b))
  {
    return d_ee.areDisequal(a, b, false);
  }
  return a.isConst() && b.isConst();
}

void SolverState::setConflict() { d_conflict = true; }
void SolverState::setConflict(Node conf)
{
  d_parent.getOutputChannel()->conflict(conf);
  d_conflict = true;
}

void SolverState::addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const
{
  if (a != b)
  {
    Assert(areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
}

Node SolverState::getEmptyBagEqClass(TypeNode tn) const
{
  std::map<TypeNode, Node>::const_iterator it = d_eqc_emptybag.find(tn);
  if (it != d_eqc_emptybag.end())
  {
    return it->second;
  }
  return Node::null();
}

bool SolverState::isEntailed(Node n, bool polarity) const
{
  if (n.getKind() == NOT)
  {
    return isEntailed(n[0], !polarity);
  }
  else if (n.getKind() == EQUAL)
  {
    if (polarity)
    {
      return areEqual(n[0], n[1]);
    }
    return areDisequal(n[0], n[1]);
  }

  return false;
}

bool SolverState::isBagDisequalityEntailed(Node r1, Node r2) const
{
  Assert(d_ee.hasTerm(r1) && d_ee.getRepresentative(r1) == r1);
  Assert(d_ee.hasTerm(r2) && d_ee.getRepresentative(r2) == r2);
  TypeNode tn = r1.getType();
  Node re = getEmptyBagEqClass(tn);
  for (unsigned e = 0; e < 2; e++)
  {
    Node a = e == 0 ? r1 : r2;
    Node b = e == 0 ? r2 : r1;
    if (isBagDisequalityEntailedInternal(a, b, re))
    {
      return true;
    }
  }
  return false;
}

bool SolverState::isBagDisequalityEntailedInternal(Node a,
                                                   Node b,
                                                   Node re) const
{
  return false;
}

Node SolverState::getEmptyBag(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_emptybag.find(tn);
  if (it != d_emptybag.end())
  {
    return it->second;
  }
  Node n = NodeManager::currentNM()->mkConst(EmptyBag(tn.toType()));
  d_emptybag[tn] = n;
  return n;
}

Node SolverState::getVariableBag(Node r) const
{
  std::map<Node, Node>::const_iterator it = d_var_bag.find(r);
  if (it != d_var_bag.end())
  {
    return it->second;
  }
  return Node::null();
}

const vector<Node> SolverState::getBagsEqClasses(const TypeNode& t) const
{
  vector<Node> representatives;
  for (const Node& eqc : getBagsEqClasses())
  {
    if (eqc.getType().getBagElementType() == t)
    {
      representatives.push_back(eqc);
    }
  }
  return representatives;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

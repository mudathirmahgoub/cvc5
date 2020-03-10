/*********************                                                        */
/*! \file theory_bags_type_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andrew Reynolds, Mudathir Mahgoub
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief bag enumerator implementation
 **
 ** bag enumerator implementation
 **/

#include "theory/sets/theory_bags_type_enumerator.h"

#include "expr/emptybag.h"
#include "theory_sets_type_enumerator.h"
namespace CVC4 {
namespace theory {
namespace sets {

BagEnumerator::BagEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<BagEnumerator>(type),
      d_nodeManager(NodeManager::currentNM()),
      d_pairsEnumerator(getPairsEnumerator(type, tep))
{
  d_currentBag = d_nodeManager->mkConst(EmptyBag(type.toType()));
}

SetEnumerator BagEnumerator::getPairsEnumerator(
    const TypeNode& type, TypeEnumeratorProperties* tep) const
{
  std::vector<TypeNode> pair;
  pair.push_back(type.getBagElementType());
  pair.push_back(d_nodeManager->integerType());
  TypeNode pairType = d_nodeManager->mkTupleType(pair);
  TypeNode setType = d_nodeManager->mkSetType(pairType);
  SetEnumerator setEnumerator(setType, tep);
  return setEnumerator;
}

BagEnumerator::BagEnumerator(const BagEnumerator& enumerator)
    : TypeEnumeratorBase<BagEnumerator>(enumerator.getType()),
      d_nodeManager(enumerator.d_nodeManager),
      d_pairsEnumerator(enumerator.d_pairsEnumerator),
      d_currentBag(enumerator.d_currentBag)
{
}

BagEnumerator::~BagEnumerator() {}

Node BagEnumerator::operator*()
{
  Trace("bag-type-enum") << "BagEnumerator::operator* d_currentBag = "
                         << d_currentBag << std::endl;

  return d_currentBag;
}

BagEnumerator& BagEnumerator::operator++()
{
  // get a new element from the set enumerator
  ++d_pairsEnumerator;
  d_currentBag = *d_pairsEnumerator;

  convertIntToNat(&d_currentBag);

  Assert(d_currentBag.isConst());
  Assert(d_currentBag == Rewriter::rewrite(d_currentBag));

  Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                         << d_currentBag << std::endl;
  return *this;
}

void BagEnumerator::convertIntToNat(Node * node)
{
  // 0 -> 1
  // n -> 2n
  // -n -> -2n + 1
}

bool BagEnumerator::isFinished()
{
  // bags sequence is infinite and it never ends
  return false;
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

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

#include "expr/datatype.h"
#include "expr/emptybag.h"
#include "theory_sets_type_enumerator.h"
//ToDo: refine this include
#include "theory/sets/theory_sets_private.h"


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
  Node node = *d_pairsEnumerator;
  d_currentBag = convertIntToNat(node);

  Assert(d_currentBag.isConst());
  Assert(d_currentBag == Rewriter::rewrite(d_currentBag));

  Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                         << d_currentBag << std::endl;
  return *this;
}

Node BagEnumerator::convertIntToNat(Node& node)
{
  if (node.getKind() == kind::UNION)
  {
    Node a = node[0];
    Node b = node[1];
    a = convertIntToNat(a);
    b = convertIntToNat(b);
    return d_nodeManager->mkNode(kind::UNION, a, b);
  }

  if (node.getKind() == kind::SINGLETON)
  {
    Node element = node[0][0];
    Node count = node[0][1];

    Rational rational = count.getConst<Rational>();

    if (rational == 0)
    {
      rational = rational + 1;
    }
    else
    {
      if (rational > 0)
      {
        rational = Rational(2) * rational;
      }
      else
      {
        rational = Rational(-2) * rational + Rational(1);
      }
    }
    count = d_nodeManager->mkConst(rational);

    const DType& dataType = d_pairsEnumerator.getType().getSetElementType().getDType();
    node = d_nodeManager->mkNode(
        kind::APPLY_CONSTRUCTOR, dataType[0].getConstructor(), element, count);
    node = d_nodeManager->mkNode(kind::SINGLETON, node);
    return node;
  }
  return node;
}

bool BagEnumerator::isFinished()
{
  // bags sequence is infinite and it never ends
  return false;
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

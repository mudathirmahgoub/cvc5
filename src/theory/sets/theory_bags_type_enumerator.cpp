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
// ToDo: refine this include
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

  std::map<Node, Rational> elementsMap;
  // skip if duplicates found
  while(!convertIntToNat(node, elementsMap))
  {
    ++d_pairsEnumerator;
    node = *d_pairsEnumerator;
    std::cout << node << std::endl;
  }

  const DType& dataType =
      d_pairsEnumerator.getType().getSetElementType().getDType();
  std::vector<Node> elements;
  for (std::pair<Node, Rational> pair : elementsMap)
  {
    Node count = d_nodeManager->mkConst(pair.second);
    Node n = d_nodeManager->mkNode(kind::APPLY_CONSTRUCTOR,
                                   dataType[0].getConstructor(),
                                   pair.first,
                                   count);
    elements.push_back(n);
  }

  d_currentBag = NormalForm::elementsToSet(
      std::set<TNode>(elements.begin(), elements.end()),
      d_pairsEnumerator.getType());
  Assert(d_currentBag.isConst());
  Assert(d_currentBag == Rewriter::rewrite(d_currentBag));

  Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                         << d_currentBag << std::endl;
  return *this;
}

bool BagEnumerator::convertIntToNat(Node& node,
                                    std::map<Node, Rational>& elementsMap)
{
  if (node.getKind() == kind::UNION)
  {
    Node a = node[0];
    Node b = node[1];
    return convertIntToNat(a, elementsMap) && convertIntToNat(b, elementsMap);
  }
  else if (node.getKind() == kind::SINGLETON)
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

    std::map<Node, Rational>::iterator it = elementsMap.find(element);
    if (it == elementsMap.end())
    {
      elementsMap[element] = rational;
      return true;
    }
    else
    {
      elementsMap[element] = elementsMap[element] + rational;
      return true;
    }
  }
  Assert(false) << "Expected Union or Singleton. Found " << node << std::endl;
}

bool BagEnumerator::isFinished()
{
  // bags sequence is infinite and it never ends
  return false;
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

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
namespace CVC4 {
namespace theory {
namespace sets {

BagEnumerator::BagEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<BagEnumerator>(type),
      d_nodeManager(NodeManager::currentNM()),
      d_elementEnumerator(type.getBagElementType(), tep),
      d_isFinished(false),
      d_currentBagIndex(0),
      d_currentBag()
{
  d_currentBag = d_nodeManager->mkConst(EmptyBag(type.toType()));
}

BagEnumerator::BagEnumerator(const BagEnumerator& enumerator)
    : TypeEnumeratorBase<BagEnumerator>(enumerator.getType()),
      d_nodeManager(enumerator.d_nodeManager),
      d_elementEnumerator(enumerator.d_elementEnumerator),
      d_isFinished(enumerator.d_isFinished),
      d_currentBagIndex(enumerator.d_currentBagIndex),
      d_currentBag(enumerator.d_currentBag)
{
}

BagEnumerator::~BagEnumerator() {}

Node BagEnumerator::operator*()
{
  if (d_isFinished)
  {
    throw NoMoreValuesException(getType());
  }

  Trace("bag-type-enum") << "BagEnumerator::operator* d_currentBag = "
                         << d_currentBag << std::endl;

  return d_currentBag;
}

BagEnumerator& BagEnumerator::operator++()
{
  if (d_isFinished)
  {
    Trace("bag-type-enum") << "BagEnumerator::operator++ finished!"
                           << std::endl;
    Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                           << d_currentBag << std::endl;
    return *this;
  }

  d_currentBagIndex++;

  // if the index is a power of 2, get a new element from d_elementEnumerator
  if (d_currentBagIndex == static_cast<unsigned>(1 << d_elementsSoFar.size()))
  {
    // if there are no more values from d_elementEnumerator, set d_isFinished
    // to true
    if (d_elementEnumerator.isFinished())
    {
      d_isFinished = true;

      Trace("bag-type-enum")
          << "BagEnumerator::operator++ finished!" << std::endl;
      Trace("bag-type-enum")
          << "BagEnumerator::operator++ d_currentBag = " << d_currentBag
          << std::endl;
      return *this;
    }

    // get a new element and return it as a singleton set
    Node element = *d_elementEnumerator;
    d_elementsSoFar.push_back(element);
    d_currentBag = d_nodeManager->mkNode(kind::SINGLETON, element);
    d_elementEnumerator++;
  }
  else
  {
    // determine which elements are included in the set
    BitVector indices = BitVector(d_elementsSoFar.size(), d_currentBagIndex);
    std::vector<Node> elements;
    for (unsigned i = 0; i < d_elementsSoFar.size(); i++)
    {
      // add the element to the set if its corresponding bit is set
      if (indices.isBitSet(i))
      {
        elements.push_back(d_elementsSoFar[i]);
      }
    }
    d_currentBag = NormalForm::elementsToSet(
        std::set<TNode>(elements.begin(), elements.end()), getType());
  }

  Assert(d_currentBag.isConst());
  Assert(d_currentBag == Rewriter::rewrite(d_currentBag));

  Trace("bag-type-enum") << "BagEnumerator::operator++ d_elementsSoFar = "
                         << d_elementsSoFar << std::endl;
  Trace("bag-type-enum") << "BagEnumerator::operator++ d_currentBag = "
                         << d_currentBag << std::endl;

  return *this;
}

bool BagEnumerator::isFinished()
{
  // bags sequence is infinite and it never ends
  return false;
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

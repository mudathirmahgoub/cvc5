/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Normal form for bag constants.
 **
 ** Normal form for bag constants.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__NORMAL_FORM_H
#define CVC4__THEORY__BAGS__NORMAL_FORM_H

namespace CVC4 {
namespace theory {
namespace bags {

class NormalForm
{
 public:
  static Node elementsToBag(const std::map<Node, Rational>& elements,
                            TypeNode bagType)
  {
    typedef typename std::map<Node, Rational>::const_iterator ElementsIterator;
    NodeManager* nm = NodeManager::currentNM();
    if (elements.size() == 0)
    {
      return nm->mkConst(EmptyBag(nm->toType(bagType)));
    }
    else if (elements.size() == 1)
    {
      ElementsIterator it = elements.begin();
      return nm->mkNode(
          kind::BAG_SINGLETON, it->first, nm->mkConst(it->second));
    }
    else
    {
      ElementsIterator it = elements.begin();
      Node node =
          nm->mkNode(kind::BAG_SINGLETON, it->first, nm->mkConst(it->second));
      while (++it != elements.end())
      {
        Node singleton =
            nm->mkNode(kind::BAG_SINGLETON, it->first, nm->mkConst(it->second));
        node = nm->mkNode(kind::DISJOINT_UNION, node, singleton);
      }
      return node;
    }
  }

  static bool checkNormalConstant(Node n)
  {
    Debug("bags-checknormal")
        << "[bags-checknormal] checkNormal " << n << " :" << std::endl;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return true;
    }
    else if (n.getKind() == kind::BAG_SINGLETON)
    {
      return n[0].isConst();
    }
    else if (n.getKind() != kind::DISJOINT_UNION)
    {
      return false;
    }

    // assuming (disjoint-union ... (disjoint-union {SmallestNodeID}
    // {BiggerNodeId}) ... {BiggestNodeId})

    // store BiggestNodeId in previousElement
    if (n[1].getKind() != kind::BAG_SINGLETON || !n[1].isConst())
    {
      return false;
    }

    TNode previousElement = n[1][0];

    // check intermediate nodes
    do
    {
      n = n[0];
      // the second node needs to be a constant singleton
      if (n[1].getKind() != kind::BAG_SINGLETON || !n[1].isConst())
      {
        return false;
      }
      if (n[1][0] >= previousElement)
      {
        return false;
      }
      previousElement = n[1][0];
    } while (n.getKind() == kind::DISJOINT_UNION);

    // check the last singleton
    if (n.getKind() != kind::BAG_SINGLETON)
    {
      return false;
    }
    if (!n[0].isConst())
    {
      return false;
    }
    Debug("bags-checknormal")
        << "last element = " << n[0] << " " << n[0].getId() << std::endl;
    if (n[0] >= previousElement)
    {
      return false;
    }
    return true;
  }

  static std::vector<Node> getElementsFromNormalConstant(TNode n)
  {
    Assert(n.isConst());
    std::vector<Node> elements;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return elements;
    }
    while (n.getKind() == kind::DISJOINT_UNION)
    {
      Assert(n[1].getKind() == kind::BAG_SINGLETON);
      elements.insert(elements.end(), n[1][0]);
      n = n[0];
    }
    Assert(n.getKind() == kind::BAG_SINGLETON);
    elements.push_back(n[0]);
    return elements;
  }

  static void getElementsFromBinaryOp(Kind k, Node n, std::vector<Node>& els)
  {
    if (n.getKind() == k)
    {
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        getElementsFromBinaryOp(k, n[i], els);
      }
    }
    else
    {
      if (std::find(els.begin(), els.end(), n) == els.end())
      {
        els.push_back(n);
      }
    }
  }
  static Node mkBinaryOp(Kind k,
                         std::vector<Node>& els,
                         TypeNode tn,
                         unsigned index = 0)
  {
    if (index >= els.size())
    {
      return NodeManager::currentNM()->mkConst(EmptyBag(tn.toType()));
    }
    else if (index == els.size() - 1)
    {
      return els[index];
    }
    else
    {
      return NodeManager::currentNM()->mkNode(
          k, els[index], mkBinaryOp(k, els, tn, index + 1));
    }
  }
};
}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif
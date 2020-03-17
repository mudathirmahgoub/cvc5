/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Normal form for set constants.
 **
 ** Normal form for set constants.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__NORMAL_FORM_H
#define CVC4__THEORY__BAGS__NORMAL_FORM_H

namespace CVC4 {
namespace theory {
namespace sets {

class BagsNormalForm
{
 public:
  template <bool ref_count>
  static Node elementsToBag(const std::vector<NodeTemplate<ref_count> >& elements,
                            TypeNode bagType)
  {
    typedef typename std::vector<NodeTemplate<ref_count> >::const_iterator
        ElementsIterator;
    NodeManager* nm = NodeManager::currentNM();
    if (elements.size() == 0)
    {
      return nm->mkConst(EmptyBag(nm->toType(bagType)));
    }
    else
    {
      ElementsIterator it = elements.begin();
      Node current = nm->mkConst(EmptyBag(nm->toType(bagType)));
      while (++it != elements.end())
      {
        current = nm->mkNode(kind::INSERT, current, *it);
      }
      return current;
    }
  }

  static bool checkNormalConstant(TNode n)
  {
    Debug("bags-checknormal")
        << "[bags-checknormal] checkNormal " << n << " :" << std::endl;
    if (n.getKind() == kind::EMPTYSET)
    {
      return true;
    }
    else if (n.getKind() == kind::SINGLETON)
    {
      return n[0].isConst();
    }
    else if (n.getKind() == kind::UNION)
    {
      // assuming (union ... (union {SmallestNodeID} {BiggerNodeId}) ...
      // {BiggestNodeId})

      // store BiggestNodeId in prvs
      if (n[1].getKind() != kind::SINGLETON) return false;
      if (!n[1][0].isConst()) return false;
      Debug("bags-checknormal")
          << "[bags-checknormal]              frst element = " << n[1][0] << " "
          << n[1][0].getId() << std::endl;
      TNode prvs = n[1][0];
      n = n[0];

      // check intermediate nodes
      while (n.getKind() == kind::UNION)
      {
        if (n[1].getKind() != kind::SINGLETON) return false;
        if (!n[1].isConst()) return false;
        Debug("bags-checknormal")
            << "[bags-checknormal]              element = " << n[1][0] << " "
            << n[1][0].getId() << std::endl;
        if (n[1][0] >= prvs) return false;
        prvs = n[1][0];
        n = n[0];
      }

      // check SmallestNodeID is smallest
      if (n.getKind() != kind::SINGLETON) return false;
      if (!n[0].isConst()) return false;
      Debug("bags-checknormal")
          << "[bags-checknormal]              lst element = " << n[0] << " "
          << n[0].getId() << std::endl;
      if (n[0] >= prvs) return false;

      // we made it
      return true;
    }
    else
    {
      return false;
    }
  }

  static bool checkBagNormalConstant(TNode n)
  {
    Debug("bags-checkBagNormalConstant")
        << "[bags-checkBagNormalConstant] checkNormal " << n << " :"
        << std::endl;
    if (n.getKind() == kind::EMPTYSET)
    {
      return true;
    }
    else if (n.getKind() == kind::SINGLETON)
    {
      return n[0].isConst();
    }
    else if (n.getKind() == kind::DISJOINTUNION)
    {
      // assuming (disjointunion ... (disjointunion {SmallestNodeID}
      // {BiggerNodeId}) ... {BiggestNodeId})

      // store BiggestNodeId in prvs
      if (n[1].getKind() != kind::SINGLETON) return false;
      if (!n[1][0].isConst()) return false;
      Debug("bags-checkBagNormalConstant")
          << "[bags-checkBagNormalConstant]              frst element = "
          << n[1][0] << " " << n[1][0].getId() << std::endl;
      TNode prvs = n[1][0];
      n = n[0];

      // check intermediate nodes
      while (n.getKind() == kind::DISJOINTUNION)
      {
        if (n[1].getKind() != kind::SINGLETON) return false;
        if (!n[1].isConst()) return false;
        Debug("bags-checkBagNormalConstant")
            << "[bags-checkBagNormalConstant]              element = "
            << n[1][0] << " " << n[1][0].getId() << std::endl;
        if (n[1][0] >= prvs) return false;
        TNode prvs = n[1][0];
        n = n[0];
      }

      // check SmallestNodeID is smallest
      if (n.getKind() != kind::SINGLETON) return false;
      if (!n[0].isConst()) return false;
      Debug("bags-checkBagNormalConstant")
          << "[bags-checkBagNormalConstant]              lst element = " << n[0]
          << " " << n[0].getId() << std::endl;
      if (n[0] >= prvs) return false;

      // we made it
      return true;
    }
    else
    {
      return false;
    }
  }

  static std::vector<Node> getElementsFromNormalConstant(TNode n)
  {
    Assert(n.isConst());
    std::vector<Node> ret;
    if (n.getKind() == kind::EMPTYSET)
    {
      return ret;
    }
    while (n.getKind() == kind::INSERT)
    {
      // (insert element bag)
      ret.insert(ret.begin(), n[0]);
      n = n[1];
    }
    Assert(n.getKind() == kind::EMPTYBAG);
    return ret;
  }

  // AJR

  static void getElementsFromBop(Kind k, Node n, std::vector<Node>& els)
  {
    if (n.getKind() == k)
    {
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        getElementsFromBop(k, n[i], els);
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
  static Node mkBop(Kind k,
                    std::vector<Node>& els,
                    TypeNode tn,
                    unsigned index = 0)
  {
    if (index >= els.size())
    {
      return NodeManager::currentNM()->mkConst(EmptySet(tn.toType()));
    }
    else if (index == els.size() - 1)
    {
      return els[index];
    }
    else
    {
      return NodeManager::currentNM()->mkNode(
          k, els[index], mkBop(k, els, tn, index + 1));
    }
  }
};
}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif

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
  template <bool ref_count>
  static Node elementsToBag(const std::set<NodeTemplate<ref_count> >& elements,
                            TypeNode bagType)
  {
    typedef typename std::set<NodeTemplate<ref_count> >::const_iterator
        ElementsIterator;
    NodeManager* nm = NodeManager::currentNM();
    if (elements.size() == 0)
    {
      return nm->mkConst(EmptyBag(nm->toType(bagType)));
    }
    else
    {
      ElementsIterator it = elements.begin();
      Node cur = nm->mkNode(kind::BAG_SINGLETON, *it);
      while (++it != elements.end())
      {
        cur = nm->mkNode(
            kind::DISJOINT_UNION, cur, nm->mkNode(kind::DISJOINT_UNION, *it));
      }
      return cur;
    }
  }

  static bool checkNormalConstant(TNode n)
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
    else if (n.getKind() == kind::DISJOINT_UNION)
    {
      // assuming (disjoint-union ... (disjoint-union {SmallestNodeID}
      // {BiggerNodeId}) ... {BiggestNodeId})

      // store BiggestNodeId in prvs
      if (n[1].getKind() != kind::SINGLETON)
      {
        return false;
      }
      if (!n[1][0].isConst())
      {
        return false;
      }
      Debug("bags-checknormal")
          << "[bags-checknormal]              frst element = " << n[1][0] << " "
          << n[1][0].getId() << std::endl;
      TNode prvs = n[1][0];
      n = n[0];

      // check intermediate nodes
      while (n.getKind() == kind::DISJOINT_UNION)
      {
        if (n[1].getKind() != kind::SINGLETON)
        {
          return false;
        }
        if (!n[1].isConst())
        {
          return false;
        }
        Debug("bags-checknormal")
            << "[bags-checknormal]              element = " << n[1][0] << " "
            << n[1][0].getId() << std::endl;
        if (n[1][0] >= prvs)
        {
          return false;
        }
        prvs = n[1][0];
        n = n[0];
      }

      // check SmallestNodeID is smallest
      if (n.getKind() != kind::BAG_SINGLETON)
      {
        return false;
      }
      if (!n[0].isConst())
      {
        return false;
      }
      Debug("bags-checknormal")
          << "[bags-checknormal]              lst element = " << n[0] << " "
          << n[0].getId() << std::endl;
      if (n[0] >= prvs)
      {
        return false;
      }

      // we made it
      return true;
    }
    else
    {
      return false;
    }
  }

  static std::set<Node> getElementsFromNormalConstant(TNode n)
  {
    Assert(n.isConst());
    std::set<Node> ret;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return ret;
    }
    while (n.getKind() == kind::DISJOINT_UNION)
    {
      Assert(n[1].getKind() == kind::BAG_SINGLETON);
      ret.insert(ret.begin(), n[1][0]);
      n = n[0];
    }
    Assert(n.getKind() == kind::BAG_SINGLETON);
    ret.insert(n[0]);
    return ret;
  }

  // AJR

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

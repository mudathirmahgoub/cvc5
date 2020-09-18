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
  /**
   * Constructs a bag of the form:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * from the bag { c1 ... cn }, also handles empty bag case, which is why
   * bagType is passed to this method.
   */
  template <bool ref_count>
  static Node elementsToBag(const std::set<NodeTemplate<ref_count> >& elements,
                            TypeNode bagType)
  {
    typedef typename std::set<NodeTemplate<ref_count> >::const_iterator
        ElementsIterator;
    NodeManager* nm = NodeManager::currentNM();
    if (elements.size() == 0)
    {
      return nm->mkConst(EmptyBag(bagType));
    }
    else
    {
      ElementsIterator it = elements.begin();
      Node cur = nm->mkNode(kind::SINGLETON, *it);
      while (++it != elements.end())
      {
        cur = nm->mkNode(kind::UNION, nm->mkNode(kind::SINGLETON, *it), cur);
      }
      return cur;
    }
  }

  /**
   * Returns true if n is considered a to be a (canonical) constant bag value.
   * A canonical bag value is one whose AST is:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * where c1 ... cn are constants and the node identifier of these constants
   * are such that:
   *   c1 > ... > cn.
   * Also handles the corner cases of empty bag and singleton bag.
   */
  static bool checkNormalConstant(TNode n)
  {
    Debug("bags-checknormal")
        << "[bags-checknormal] checkNormal " << n << " :" << std::endl;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return true;
    }
    else if (n.getKind() == kind::SINGLETON)
    {
      return n[0].isConst();
    }
    else if (n.getKind() == kind::UNION)
    {
      // assuming (union {SmallestNodeID} ... (union {BiggerNodeId} ...

      Node orig = n;
      TNode prvs;
      // check intermediate nodes
      while (n.getKind() == kind::UNION)
      {
        if (n[0].getKind() != kind::SINGLETON || !n[0][0].isConst())
        {
          // not a constant
          Trace("bags-isconst") << "bags::isConst: " << orig << " not due to "
                                << n[0] << std::endl;
          return false;
        }
        Debug("bags-checknormal")
            << "[bags-checknormal]              element = " << n[0][0] << " "
            << n[0][0].getId() << std::endl;
        if (!prvs.isNull() && n[0][0] >= prvs)
        {
          Trace("bags-isconst")
              << "bags::isConst: " << orig << " not due to compare " << n[0][0]
              << std::endl;
          return false;
        }
        prvs = n[0][0];
        n = n[1];
      }

      // check SmallestNodeID is smallest
      if (n.getKind() != kind::SINGLETON || !n[0].isConst())
      {
        Trace("bags-isconst") << "bags::isConst: " << orig
                              << " not due to final " << n << std::endl;
        return false;
      }
      Debug("bags-checknormal")
          << "[bags-checknormal]              lst element = " << n[0] << " "
          << n[0].getId() << std::endl;
      // compare last ID
      if (n[0] < prvs)
      {
        return true;
      }
      Trace("bags-isconst")
          << "bags::isConst: " << orig << " not due to compare final " << n[0]
          << std::endl;
    }
    return false;
  }

  /**
   * Converts a bag term to a std::set of its elements. This expects a bag of
   * the form:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * Also handles the corner cases of empty bag and singleton bag.
   */
  static std::set<Node> getElementsFromNormalConstant(TNode n)
  {
    Assert(n.isConst());
    std::set<Node> ret;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return ret;
    }
    while (n.getKind() == kind::UNION)
    {
      Assert(n[0].getKind() == kind::SINGLETON);
      ret.insert(ret.begin(), n[0][0]);
      n = n[1];
    }
    Assert(n.getKind() == kind::SINGLETON);
    ret.insert(n[0]);
    return ret;
  }

  static Node mkBop(Kind k,
                    std::vector<Node>& els,
                    TypeNode tn,
                    unsigned index = 0)
  {
    if (index >= els.size())
    {
      return NodeManager::currentNM()->mkConst(EmptyBag(tn));
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
}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__NORMAL_FORM_H */

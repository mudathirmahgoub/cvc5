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
  static bool checkNormalConstant(TNode n)
  {
    Debug("bags-checknormal")
        << "[bags-checknormal] checkNormal " << n << " :" << std::endl;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return true;
    }
    else if (n.getKind() == kind::INSERT)
    {
      // assuming (insert NodeN... Node1 emptybag)
      size_t size = n.getNumChildren();
      // check NodeN >= ... >= Node1

      for (size_t i = 1; i < size - 1; i++)
      {
        if (n[i] > n[i - 1])
        {
          Debug("bags-checknormal")
              << "n[i-1] = " << n[i - 1] << ", n[i] = " << n[i] << std::endl;
          return false;
        }
      }
      // we made it
      return true;
    }
    else
    {
      return false;
    }
  }

  static std::vector<Node> getInsertedElements(TNode n)
  {
    std::vector<Node> elements;
    if (n.getKind() == kind::EMPTYBAG)
    {
      return elements;
    }

    size_t size = n.getNumChildren();

    for (size_t i = size - 2; i >= 0; i--)
    {
      elements.push_back(n[i]);
    }

    return elements;
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
  static Node makeBag(std::vector<Node>& elements, TypeNode type)
  {
    std::sort(elements.begin(), elements.end());
    NodeManager* nm = NodeManager::currentNM();
    Node node = nm->mkConst(EmptyBag(type.toType()));
    for (size_t i = 0; i < elements.size(); i++)
    {
      node = nm->mkNode(kind::INSERT, elements[i], node);
    }
    return node;
  }
};
}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif

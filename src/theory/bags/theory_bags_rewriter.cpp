/*********************                                                        */
/*! \file theory_bags_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory rewriter.
 **
 ** Bags theory rewriter.
 **/

#include "theory/bags/theory_bags_rewriter.h"

#include "smt/logic_exception.h"
#include "theory/bags/normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

RewriteResponse TheoryBagsRewriter::postRewrite(TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();
  Trace("sets-postrewrite") << "Process: " << node << std::endl;

  if (node.isConst())
  {
    return RewriteResponse(REWRITE_DONE, node);
  }

  switch (kind)
  {
    case kind::DISJOINT_UNION:
    {
      // NOTE: case where it is CONST is taken care of at the top
      if (node[0] == node[1])
      {
        Trace("bags-postrewrite")
            << "Sets::postRewrite returning " << node[0] << std::endl;
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].getKind() == kind::EMPTYBAG)
      {
        return RewriteResponse(REWRITE_AGAIN, node[1]);
      }
      else if (node[1].getKind() == kind::EMPTYBAG)
      {
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        std::vector<Node> left =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::vector<Node> right =
            NormalForm::getElementsFromNormalConstant(node[1]);

        std::map<Node, Rational> newBag;
        // add the elements of the first child to the map
        for (Node element : left)
        {
          newBag[element[0]] = element[1].getConst<Rational>();
        }
        // add the elements of the second child to the map
        for (Node element : left)
        {
          if (newBag.find(element[0]) == newBag.end())
          {
            newBag[element[0]] = element[1].getConst<Rational>();
          }
          else
          {
            newBag[element[0]] += element[1].getConst<Rational>();
          }
        }

        Node newNode = NormalForm::elementsToBag(newBag, node.getType());
        Assert(newNode.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      else
      {
        std::stringstream message;
        message << "This case is not implemented yet";
        throw LogicException(message.str());
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBagsRewriter::preRewrite(TNode node)
{
  return RewriteResponse(REWRITE_DONE, node);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

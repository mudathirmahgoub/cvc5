/*********************                                                        */
/*! \file theory_sets_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory rewriter.
 **
 ** Bags theory rewriter.
 **/

#include "theory/bags/theory_bags_rewriter.h"

#include "expr/attribute.h"
#include "options/sets_options.h"
#include "theory/bags/normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

bool TheoryBagsRewriter::checkConstantMembership(TNode elementTerm,
                                                 TNode bagTerm)
{
  if (bagTerm.getKind() == kind::EMPTYBAG)
  {
    return false;
  }

  if (bagTerm.getKind() == kind::SINGLETON)
  {
    return elementTerm == bagTerm[0];
  }

  Assert(bagTerm.getKind() == kind::UNION
         && bagTerm[0].getKind() == kind::SINGLETON)
      << "kind was " << bagTerm.getKind() << ", term: " << bagTerm;

  return elementTerm == bagTerm[0][0]
         || checkConstantMembership(elementTerm, bagTerm[1]);
}

// static
RewriteResponse TheoryBagsRewriter::postRewrite(TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();
  Trace("bags-postrewrite") << "Process: " << node << std::endl;

  if (node.isConst())
  {
    Trace("bags-rewrite-nf")
        << "Bags::rewrite: no rewrite (constant) " << node << std::endl;
    // Dare you touch the const and mangle it to something else.
    return RewriteResponse(REWRITE_DONE, node);
  }

  switch (kind)
  {
    case kind::EQUAL:
    {
      // rewrite: t = t with true (t term)
      // rewrite: c = c' with c different from c' false (c, c' constants)
      // otherwise: sort them
      if (node[0] == node[1])
      {
        Trace("sets-postrewrite")
            << "Bags::postRewrite returning true" << std::endl;
        return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Trace("sets-postrewrite")
            << "Bags::postRewrite returning false" << std::endl;
        return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      }
      else if (node[0] > node[1])
      {
        Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
        Trace("sets-postrewrite")
            << "Bags::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default: break;
  }

  return RewriteResponse(REWRITE_DONE, node);
}

// static
RewriteResponse TheoryBagsRewriter::preRewrite(TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = node.getKind();
  if (k == kind::EQUAL)
  {
    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
  }

  return RewriteResponse(REWRITE_DONE, node);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

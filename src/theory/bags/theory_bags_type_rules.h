/*********************                                                        */
/*! \file theory_bags_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory type rules.
 **
 ** Bags theory type rules.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H

#include "theory/bags/normal_form.h"

namespace CVC4 {
namespace theory {
namespace bags {

struct BagsBinaryOperatorTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_UNION || n.getKind() == kind::DISJOINT_UNION
           || n.getKind() == kind::BAG_INTERSECTION
           || n.getKind() == kind::BAG_DIFFERENCE1
           || n.getKind() == kind::BAG_DIFFERENCE2);
    TypeNode bagType = n[0].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(
            n, "operator expects a bag, first argument is not");
      }
      TypeNode secondBagType = n[1].getType(check);
      if (secondBagType != bagType)
      {
        if (n.getKind() == kind::INTERSECTION)
        {
          bagType = TypeNode::mostCommonTypeNode(secondBagType, bagType);
        }
        else
        {
          bagType = TypeNode::leastCommonTypeNode(secondBagType, bagType);
        }
        if (bagType.isNull())
        {
          throw TypeCheckingExceptionPrivate(
              n, "operator expects two bags of comparable types");
        }
      }
    }
    return bagType;
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_UNION || n.getKind() == kind::DISJOINT_UNION
           || n.getKind() == kind::BAG_INTERSECTION
           || n.getKind() == kind::BAG_DIFFERENCE1
           || n.getKind() == kind::BAG_DIFFERENCE2);
    if (n.getKind() == kind::DISJOINT_UNION)
    {
      return NormalForm::checkNormalConstant(n);
    }
    else
    {
      return false;
    }
  }
}; /* struct BagsBinaryOperatorTypeRule */

struct BagsSubsetTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_SUBSET);
    TypeNode bagType= n[0].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(n,
                                           "bag subset operating on non-bag");
      }
      TypeNode secondBagType = n[1].getType(check);
      if (secondBagType != bagType)
      {
        if (!bagType.isComparableTo(secondBagType))
        {
          throw TypeCheckingExceptionPrivate(
              n, "bag subset operating on bags of different types");
        }
      }
    }
    return nodeManager->booleanType();
  }
}; /* struct BagsSubsetTypeRule */

struct BagsCountTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::COUNT);
    TypeNode bagType = n[1].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(
            n, "checking for membership in a non-bag");
      }
      TypeNode elementType = n[0].getType(check);
      // TODO : still need to be flexible here due to situations like:
      //
      // T : (Bag Int)
      // B : (Bag Real)
      // (= (as T (Bag Real)) B)
      // (= (count 0.5 B) 1)
      // ...where (count 0.5 T) is inferred
      //
      // or
      //
      // B : (Bag Real)
      // (not (count 0.5 B))
      // ( = (count 0.0 B) 1)
      // ...find model M where M( B ) = { (0.0, 1) }, check model will generate
      // (not (= (count 0.5 (singleton (0.0, 1) 1)))
      //
      if (!elementType.isComparableTo(bagType.getBagElementType()))
      {
        std::stringstream ss;
        ss << "member operating on bags of different types:\n"
           << "child type:  " << elementType << "\n"
           << "not subtype: " << bagType.getBagElementType() << "\n"
           << "in term : " << n;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return nodeManager->booleanType();
  }
}; /* struct BagsCountTypeRule */

struct BagsSingletonTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_SINGLETON);
    return nodeManager->mkSetType(n[0].getType(check));
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_SINGLETON);
    return n[0].isConst();
  }
}; /* struct BagsSingletonTypeRule */

struct EmptyBagTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::EMPTYBAG);
    EmptyBag emptyBag = n.getConst<EmptyBag>();
    Type bagType = emptyBag.getType();
    return TypeNode::fromType(bagType);
  }
}; /* struct EmptyBagTypeRule */

struct BagsCardTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_CARD);
    TypeNode bagType= n[0].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(
            n, "cardinality operates on a bag, non-bag object found");
      }
    }
    return nodeManager->integerType();
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_CARD);
    return false;
  }
}; /* struct BagsCardTypeRule */

struct BagsChooseTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_CHOOSE);
    TypeNode bagType= n[0].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(
            n, "CHOOSE operator expects a bag, a non-bag is found");
      }
    }
    return bagType.getBagElementType();
  }
  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_CHOOSE);
    // choose nodes should be expanded
    return false;
  }
}; /* struct BagsChooseTypeRule */

struct BagsInsertTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_INSERT);
    size_t numChildren = n.getNumChildren();
    Assert(numChildren >= 2);
    TypeNode bagType= n[numChildren - 1].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(n, "inserting into a non-bag");
      }
      for (size_t i = 0; i < numChildren - 1; ++i)
      {
        TypeNode elementType = n[i].getType(check);
        if (elementType != bagType.getBagElementType())
        {
          throw TypeCheckingExceptionPrivate(
              n,
              "type of element should be same as element type of bag being "
              "inserted into");
        }
      }
    }
    return bagType;
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_INSERT);
    return false;
  }
}; /* struct BagsInsertTypeRule */

struct BagsProperties
{
  inline static Cardinality computeCardinality(TypeNode type)
  {
    //ToDo: review this
    return Cardinality::UNKNOWN_CARD;
  }

  inline static bool isWellFounded(TypeNode type)
  {
    return type[0].isWellFounded();
  }

  inline static Node mkGroundTerm(TypeNode type)
  {
    Assert(type.isBag());
    return NodeManager::currentNM()->mkConst(EmptySet(type.toType()));
  }
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */

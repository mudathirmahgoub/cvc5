/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bags proof checker.
 */

#include "theory/bags/proof_checker.h"

#include "expr/skolem_manager.h"
#include "theory/bags/bags_utils.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

BagsProofRuleChecker::BagsProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void BagsProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::BAGS_COUNT_NON_NEG, this);
  pc->registerChecker(ProofRule::BAGS_COUNT_DEF, this);
  pc->registerChecker(ProofRule::BAGS_MAKE_SPLIT, this);
  pc->registerChecker(ProofRule::BAGS_EXT, this);
  pc->registerChecker(ProofRule::BAGS_FILTER_UP, this);
  pc->registerChecker(ProofRule::BAGS_FILTER_DOWN, this);
  pc->registerChecker(ProofRule::BAGS_MAP_UP, this);
}

Node BagsProofRuleChecker::checkInternal(ProofRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (id == ProofRule::BAGS_COUNT_NON_NEG)
  {
    // (>= (bag.count e A) 0)
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::BAG_COUNT)
    {
      return Node::null();
    }
    return nm->mkNode(Kind::GEQ, args[0], nm->mkConstInt(Rational(0)));
  }
  else if (id == ProofRule::BAGS_COUNT_DEF)
  {
    // (= (bag.count e t) r), where r is given by BagsUtils::mkCountDef
    Assert(children.empty());
    Assert(args.size() == 1);
    Node def = BagsUtils::mkCountDef(nm, args[0]);
    if (def.isNull())
    {
      return Node::null();
    }
    return args[0].eqNode(def);
  }
  else if (id == ProofRule::BAGS_MAKE_SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::BAG_MAKE)
    {
      return Node::null();
    }
    return BagsUtils::mkBagMakeSplit(nm, args[0]);
  }
  else if (id == ProofRule::BAGS_EXT)
  {
    // (not (= A B)) => (not (= (bag.count k A) (bag.count k B)))
    Assert(children.size() == 1);
    Assert(args.empty());
    Node deq = children[0];
    if (deq.getKind() != Kind::NOT || deq[0].getKind() != Kind::EQUAL
        || !deq[0][0].getType().isBag())
    {
      return Node::null();
    }
    Node a = deq[0][0];
    Node b = deq[0][1];
    SkolemManager* sm = nm->getSkolemManager();
    Node k = sm->mkSkolemFunction(SkolemId::BAGS_DEQ_DIFF, {a, b});
    Node ca = nm->mkNode(Kind::BAG_COUNT, k, a);
    Node cb = nm->mkNode(Kind::BAG_COUNT, k, b);
    return ca.eqNode(cb).notNode();
  }
  else if (id == ProofRule::BAGS_FILTER_UP)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return BagsUtils::mkFilterUp(nm, args[0]);
  }
  else if (id == ProofRule::BAGS_FILTER_DOWN)
  {
    // (>= (bag.count e (bag.filter P A)) 1) => (and (P e) (= ... ))
    Assert(children.size() == 1);
    Assert(args.empty());
    Node mem = children[0];
    if (mem.getKind() != Kind::GEQ || !mem[1].isConst()
        || mem[1].getConst<Rational>() != Rational(1))
    {
      return Node::null();
    }
    return BagsUtils::mkFilterDown(nm, mem[0]);
  }
  else if (id == ProofRule::BAGS_MAP_UP)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    if (args[0].getKind() != Kind::BAG_MAP
        || args[1].getType() != args[0][1].getType().getBagElementType())
    {
      return Node::null();
    }
    return BagsUtils::mkMapUp(nm, args[0], args[1]);
  }
  // no rule
  return Node::null();
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

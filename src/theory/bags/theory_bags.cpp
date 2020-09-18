/*********************                                                        */
/*! \file theory_bags.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **
 ** Bags theory.
 **/

#include "theory/bags/theory_bags.h"

#include "options/sets_options.h"
#include "theory/bags/theory_bags_private.h"
#include "theory/bags/theory_bags_rewriter.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TheoryBags::TheoryBags(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_BAGS, c, u, out, valuation, logicInfo, pnm),
      d_skCache(),
      d_state(c, u, valuation, d_skCache),
      d_im(*this, d_state, pnm),
      d_internal(new TheoryBagsPrivate(*this, d_state, d_im, d_skCache)),
      d_notify(*d_internal.get())
{
  // use the official theory state and inference manager objects
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryBags::~TheoryBags() {}

TheoryRewriter* TheoryBags::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

bool TheoryBags::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::bags::ee";
  return true;
}

void TheoryBags::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // choice is used to eliminate witness
  d_valuation.setUnevaluatedKind(WITNESS);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(BAG_SINGLETON);
  d_equalityEngine->addFunctionKind(BAG_UNION);
  d_equalityEngine->addFunctionKind(DISJOINT_UNION);
  d_equalityEngine->addFunctionKind(BAG_INTERSECTION);
  d_equalityEngine->addFunctionKind(BAG_DIFFERENCE1);
  d_equalityEngine->addFunctionKind(BAG_DIFFERENCE2);
  d_equalityEngine->addFunctionKind(BAG_COUNT);
  d_equalityEngine->addFunctionKind(BAG_IS_INCLUDED);

  // we do congruence over cardinality
  d_equalityEngine->addFunctionKind(BAG_CARD);

  // finish initialization internally
  d_internal->finishInit();
}

void TheoryBags::postCheck(Effort level) { d_internal->postCheck(level); }

void TheoryBags::notifyFact(TNode atom,
                            bool polarity,
                            TNode fact,
                            bool isInternal)
{
  d_internal->notifyFact(atom, polarity, fact);
}

bool TheoryBags::collectModelValues(TheoryModel* m,
                                    const std::set<Node>& termBag)
{
  return d_internal->collectModelValues(m, termBag);
}

TrustNode TheoryBags::explain(TNode node)
{
  Node exp = d_internal->explain(node);
  return TrustNode::mkTrustPropExp(node, exp, nullptr);
}

Node TheoryBags::getModelValue(TNode node) { return Node::null(); }

void TheoryBags::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);
}

TrustNode TheoryBags::expandDefinition(Node n)
{
  return d_internal->expandDefinition(n);
}

void TheoryBags::presolve() { d_internal->presolve(); }

bool TheoryBags::isEntailed(Node n, bool pol)
{
  return d_internal->isEntailed(n, pol);
}

/**************************** eq::NotifyClass *****************************/

bool TheoryBags::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                       bool value)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyTriggerPredicate: predicate = "
                   << predicate << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(predicate);
  }
  return d_theory.propagate(predicate.notNode());
}

bool TheoryBags::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag,
                                                          TNode t1,
                                                          TNode t2,
                                                          bool value)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyTriggerTermEquality: tag = " << tag
                   << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value
                   << std::endl;
  d_theory.propagate(value ? t1.eqNode(t2) : t1.eqNode(t2).negate());
  return true;
}

void TheoryBags::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyConstantTermMerge "
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

void TheoryBags::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyNewClass:"
                   << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheoryBags::NotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyMerge(t1, t2);
}

void TheoryBags::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyDisequal:"
                   << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

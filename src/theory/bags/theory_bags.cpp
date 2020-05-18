/*********************                                                        */
/*! \file theory_bags.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **
 ** Bags theory.
 **/

#include "theory/bags/theory_bags.h"

#include "theory/bags/theory_bags_private.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TheoryBags::TheoryBags(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo)
    : Theory(THEORY_BAGS, c, u, out, valuation, logicInfo),
      d_internal(new TheoryBagsPrivate(*this, c, u))
{
  // Do not move me to the header.
  // The constructor + destructor are not in the header as d_internal is a
  // unique_ptr<TheoryBagsPrivate> and TheoryBagsPrivate is an opaque type in
  // the header (Pimpl). See https://herbsutter.com/gotw/_100/ .
}

TheoryBags::~TheoryBags()
{
  // Do not move me to the header. See explanation in the constructor.
}

TheoryRewriter* TheoryBags::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

void TheoryBags::finishInit()
{
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
}

void TheoryBags::addSharedTerm(TNode n) { d_internal->addSharedTerm(n); }

void TheoryBags::check(Effort e)
{
  if (done() && e < Theory::EFFORT_FULL)
  {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);
  d_internal->check(e);
}

bool TheoryBags::collectModelInfo(TheoryModel* m)
{
  return d_internal->collectModelInfo(m);
}

Node TheoryBags::explain(TNode node) { return d_internal->explain(node); }

EqualityStatus TheoryBags::getEqualityStatus(TNode a, TNode b)
{
  return d_internal->getEqualityStatus(a, b);
}

Node TheoryBags::getModelValue(TNode node) { return Node::null(); }

void TheoryBags::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);
}

Node TheoryBags::expandDefinition(Node n)
{
  return d_internal->expandDefinition(n);
}

Theory::PPAssertStatus TheoryBags::ppAssert(TNode in,
                                            SubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryBags::presolve() { d_internal->presolve(); }

void TheoryBags::propagate(Effort e) { d_internal->propagate(e); }

void TheoryBags::setMasterEqualityEngine(eq::EqualityEngine* eq)
{
  d_internal->setMasterEqualityEngine(eq);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

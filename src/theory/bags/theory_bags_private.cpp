/*********************                                                        */
/*! \file theory_bags_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory implementation.
 **
 ** Bags theory implementation.
 **/

#include "theory/bags/theory_bags_private.h"

#include "theory/bags/theory_bags.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TheoryBagsPrivate::TheoryBagsPrivate(TheoryBags& external,
                                     context::Context* c,
                                     context::UserContext* u)
    : d_external(external)
{
}
void TheoryBagsPrivate::setMasterEqualityEngine(eq::EqualityEngine* eq) {}
void TheoryBagsPrivate::addSharedTerm(TNode) {}
void TheoryBagsPrivate::check(Theory::Effort) {}
bool TheoryBagsPrivate::collectModelInfo(TheoryModel* m) { return true; }
Node TheoryBagsPrivate::explain(TNode) { return CVC4::Node(); }
EqualityStatus TheoryBagsPrivate::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_FALSE_IN_MODEL;
}
void TheoryBagsPrivate::preRegisterTerm(TNode node) {}
Node TheoryBagsPrivate::expandDefinition(Node n) { return n; }
Theory::PPAssertStatus TheoryBagsPrivate::ppAssert(
    TNode in, SubstitutionMap& outSubstitutions)
{
  return Theory::PP_ASSERT_STATUS_CONFLICT;
}
void TheoryBagsPrivate::presolve() {}
void TheoryBagsPrivate::propagate(Theory::Effort) {}
OutputChannel* TheoryBagsPrivate::getOutputChannel() { return nullptr; }
Valuation& TheoryBagsPrivate::getValuation() { return d_external.d_valuation; }

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

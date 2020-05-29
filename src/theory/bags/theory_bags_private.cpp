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
    : d_external(external),
      d_notify(*this),
      d_equalityEngine(d_notify, c, "theory::bags::ee", true),
      d_state(*this, d_equalityEngine, c, u),
      d_deq(c),
      d_im(
          *external.d_out,
          [=](bool polarity, TNode& atom) {
            this->assertFactPrivate(polarity, atom);
          },
          d_state,
          d_equalityEngine,
          c,
          u)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}
void TheoryBagsPrivate::setMasterEqualityEngine(eq::EqualityEngine* eq)
{
  d_equalityEngine.setMasterEqualityEngine(eq);
}
void TheoryBagsPrivate::addSharedTerm(TNode) {}

void TheoryBagsPrivate::check(Theory::Effort level)
{
  Trace("bags-check") << "Bags check effort " << level << std::endl;
  if (level == Theory::EFFORT_LAST_CALL)
  {
    return;
  }
  while (!d_external.done() && !d_state.isInConflict())
  {
    // Get all the assertions
    Assertion assertion = d_external.get();
    TNode fact = assertion.d_assertion;
    Trace("bags-assert") << "Assert from input " << fact << std::endl;
    // assert the fact
    assertFact(fact, fact);
  }

  // check bags disequalities
  checkDisequalities();

  Trace("bags-check") << "Bags finished assertions effort " << level
                      << std::endl;
  // invoke full effort check, relations check
  if (!d_state.isInConflict())
  {
  }
  Trace("bags-check") << "Bags finish Check effort " << level << std::endl;
}

void TheoryBagsPrivate::checkDisequalities()
{
  // disequalities
  Trace("bags") << "TheorySetsPrivate: check disequalities..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (NodeBoolMap::const_iterator it = d_deq.begin(); it != d_deq.end(); ++it)
  {
    if (!(*it).second)
    {
      // not active
      continue;
    }
    Node deq = (*it).first;
    // check if it is already satisfied
    Assert(d_equalityEngine.hasTerm(deq[0])
           && d_equalityEngine.hasTerm(deq[1]));
    Node r1 = d_equalityEngine.getRepresentative(deq[0]);
    Node r2 = d_equalityEngine.getRepresentative(deq[1]);
    bool is_sat = d_state.isBagDisequalityEntailed(r1, r2);
    Trace("bags-debug") << "Check disequality " << deq
                        << ", is_sat = " << is_sat << std::endl;
    // will process regardless of sat/processed/unprocessed
    d_deq[deq] = false;

    if (is_sat)
    {
      // already satisfied
      continue;
    }
    if (d_termProcessed.find(deq) != d_termProcessed.end())
    {
      // already added lemma
      continue;
    }
    d_termProcessed.insert(deq);
    d_termProcessed.insert(deq[1].eqNode(deq[0]));
    Trace("bags") << "Process Disequality : " << deq.negate() << std::endl;
    TypeNode elementType = deq[0].getType().getBagElementType();
    Node x = d_state.getSkolemCache().mkTypedSkolemCached(
        elementType, deq[0], deq[1], SkolemCache::SK_DISEQUAL, "sde");
    Node count1 = nm->mkNode(COUNT, x, deq[0]);
    Node count2 = nm->mkNode(COUNT, x, deq[1]);
    Node lem = nm->mkNode(EQUAL, count1, count2).negate();
    lem = Rewriter::rewrite(lem);

    d_im.assertInference(lem, d_true, "diseq", 1);
    d_im.flushPendingLemmas();
    if (d_im.hasProcessed())
    {
      return;
    }
  }
}

bool TheoryBagsPrivate::assertFact(Node fact, Node exp)
{
  Trace("bags-assert") << "TheoryBags::assertFact : " << fact
                       << ", exp = " << exp << std::endl;
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if (!d_state.isEntailed(atom, polarity))
  {
    if (atom.getKind() == kind::EQUAL)
    {
      d_equalityEngine.assertEquality(atom, polarity, exp);
    }
    else
    {
      d_equalityEngine.assertPredicate(atom, polarity, exp);
    }
    if (!d_state.isInConflict())
    {
      assertFactPrivate(polarity, atom);
    }
    return true;
  }
  else
  {
    return false;
  }
}
void TheoryBagsPrivate::assertFactPrivate(bool polarity, TNode& atom) {}

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
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}
void TheoryBagsPrivate::presolve() {}
void TheoryBagsPrivate::propagate(Theory::Effort) {}
OutputChannel* TheoryBagsPrivate::getOutputChannel()
{
  return d_external.d_out;
}

Valuation& TheoryBagsPrivate::getValuation() { return d_external.d_valuation; }

bool TheoryBagsPrivate::propagate(TNode literal)
{
  Debug("sets-prop") << " propagate(" << literal << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_state.isInConflict())
  {
    Debug("sets-prop") << "TheoryUF::propagate(" << literal
                       << "): already in conflict" << std::endl;
    return false;
  }

  // Propagate out
  bool ok = d_external.d_out->propagate(literal);
  if (!ok)
  {
    d_state.setConflict();
  }

  return ok;
}

void TheoryBagsPrivate::eqNotifyNewClass(TNode t) {}

void TheoryBagsPrivate::eqNotifyPreMerge(TNode t1, TNode t2) {}

void TheoryBagsPrivate::eqNotifyPostMerge(TNode t1, TNode t2) {}

void TheoryBagsPrivate::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  if (t1.getType().isBag())
  {
    Node eq = t1.eqNode(t2);
    if (d_deq.find(eq) == d_deq.end())
    {
      d_deq[eq] = true;
    }
  }
}

/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/

bool TheoryBagsPrivate::NotifyClass::eqNotifyTriggerEquality(TNode equality,
                                                             bool value)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyTriggerEquality: equality = "
                   << equality << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(equality);
  }
  else
  {
    // We use only literal triggers so taking not is safe
    return d_theory.propagate(equality.notNode());
  }
}

bool TheoryBagsPrivate::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                              bool value)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyTriggerPredicate: predicate = "
                   << predicate << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(predicate);
  }
  else
  {
    return d_theory.propagate(predicate.notNode());
  }
}

bool TheoryBagsPrivate::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag,
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

void TheoryBagsPrivate::NotifyClass::eqNotifyConstantTermMerge(TNode t1,
                                                               TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyConstantTermMerge "
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

void TheoryBagsPrivate::conflict(TNode a, TNode b)
{
  Node conf = explain(a.eqNode(b));
  d_state.setConflict(conf);
  Debug("bags") << "[bags] conflict: " << a << " iff " << b << ", explanation "
                << conf << std::endl;
  Trace("bags-lemma") << "Equality Conflict : " << conf << std::endl;
}

void TheoryBagsPrivate::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyNewClass:"
                   << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheoryBagsPrivate::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyPreMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPreMerge(t1, t2);
}

void TheoryBagsPrivate::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyPostMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPostMerge(t1, t2);
}

void TheoryBagsPrivate::NotifyClass::eqNotifyDisequal(TNode t1,
                                                      TNode t2,
                                                      TNode reason)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyDisequal:"
                   << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

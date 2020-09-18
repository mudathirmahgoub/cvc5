/*********************                                                        */
/*! \file theory_bags_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory implementation.
 **
 ** Bags theory implementation.
 **/

#include "theory/bags/theory_bags_private.h"

#include <algorithm>

#include "expr/emptybag.h"
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bags/normal_form.h"
#include "theory/bags/theory_bags.h"
#include "theory/theory_model.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TheoryBagsPrivate::TheoryBagsPrivate(TheoryBags& external,
                                     SolverState& state,
                                     InferenceManager& im,
                                     SkolemCache& skc)
    : d_deq(state.getSatContext()),
      d_termProcessed(state.getUserContext()),
      d_full_check_incomplete(false),
      d_external(external),
      d_state(state),
      d_im(im),
      d_skCache(skc),
      d_treg(state, im, skc)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
}

TheoryBagsPrivate::~TheoryBagsPrivate()
{
  for (std::pair<const Node, EqcInfo*>& current_pair : d_eqc_info)
  {
    delete current_pair.second;
  }
}

void TheoryBagsPrivate::finishInit()
{
  d_equalityEngine = d_external.getEqualityEngine();
  Assert(d_equalityEngine != nullptr);
}

void TheoryBagsPrivate::eqNotifyNewClass(TNode t)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::eqNotifyMerge(TNode t1, TNode t2)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

TheoryBagsPrivate::EqcInfo::EqcInfo(context::Context* c) : d_singleton(c) {}

TheoryBagsPrivate::EqcInfo* TheoryBagsPrivate::getOrMakeEqcInfo(TNode n,
                                                                bool doMake)
{
  std::map<Node, EqcInfo*>::iterator eqc_i = d_eqc_info.find(n);
  if (eqc_i == d_eqc_info.end())
  {
    EqcInfo* ei = NULL;
    if (doMake)
    {
      ei = new EqcInfo(d_external.getSatContext());
      d_eqc_info[n] = ei;
    }
    return ei;
  }
  else
  {
    return eqc_i->second;
  }
}

void TheoryBagsPrivate::fullEffortReset()
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::fullEffortCheck()
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::checkSubtypes()
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::checkDisequalities()
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

//--------------------------------- standard check

void TheoryBagsPrivate::postCheck(Theory::Effort level)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::notifyFact(TNode atom, bool polarity, TNode fact)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}
//--------------------------------- end standard check

/************************ Sharing ************************/
/************************ Sharing ************************/
/************************ Sharing ************************/

/******************** Model generation ********************/
/******************** Model generation ********************/
/******************** Model generation ********************/

bool TheoryBagsPrivate::collectModelValues(TheoryModel* m,
                                           const std::set<Node>& termBag)
{
  //ToDo: complete this
  // Assert(false)<<"Not implemented yet"<<std::endl;
  return true;
}

/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

bool TheoryBagsPrivate::propagate(TNode literal)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
} /* TheoryBagsPrivate::propagate(TNode) */

OutputChannel* TheoryBagsPrivate::getOutputChannel()
{
  return d_external.d_out;
}

Valuation& TheoryBagsPrivate::getValuation() { return d_external.d_valuation; }

void TheoryBagsPrivate::conflict(TNode a, TNode b)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

Node TheoryBagsPrivate::explain(TNode literal)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

void TheoryBagsPrivate::preRegisterTerm(TNode node)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}

TrustNode TheoryBagsPrivate::expandDefinition(Node node)
{
  //ToDo: expand bag nodes here
}

void TheoryBagsPrivate::presolve() { d_state.reset(); }

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

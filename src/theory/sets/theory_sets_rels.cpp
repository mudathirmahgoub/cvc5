/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extension to Sets theory.
 */

#include "theory/sets/theory_sets_rels.h"

#include <algorithm>
#include <functional>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/sets_options.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/decision_manager.h"
#include "theory/incomplete_id.h"
#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/valuation.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
namespace theory {
namespace sets {

namespace {
/** PROTOTYPE: decides l <= 2, l <= 3, ... for the length l of a witness */
class CycleLenDecisionStrategy : public DecisionStrategyFmf
{
 public:
  /**
   * maxLen, if set, returns the largest k for which l <= k may be decided
   * (--rels-cycle-len-decide-bound); it may grow during the search.
   */
  CycleLenDecisionStrategy(Env& env,
                           Valuation valuation,
                           Node l,
                           std::function<size_t()> maxLen)
      : DecisionStrategyFmf(env, valuation), d_len(l), d_maxLen(maxLen)
  {
  }
  Node mkLiteral(unsigned i) override
  {
    // literal i is l <= i + 2; a null literal is not cached, so it is asked
    // for again once the bound has grown
    if (d_maxLen && i + 2 > d_maxLen())
    {
      return Node::null();
    }
    NodeManager* nm = nodeManager();
    return nm->mkNode(Kind::LEQ, d_len, nm->mkConstInt(Rational(i + 2)));
  }
  std::string identify() const override { return "sets_cycle_len"; }

 private:
  Node d_len;
  std::function<size_t()> d_maxLen;
};
}  // namespace

typedef std::map<Node, std::vector<Node> >::iterator MEM_IT;
typedef context::CDHashMap<std::vector<Node>,
                           std::pair<std::vector<Node>, Node>,
                           VectorNodeHashFunction>::iterator CYC_IT;
typedef std::map<Kind, std::vector<Node> >::iterator KIND_TERM_IT;
typedef std::map<Node, std::unordered_set<Node> >::iterator TC_GRAPH_IT;
typedef std::map<Node, std::map<Kind, std::vector<Node> > >::iterator TERM_IT;
typedef std::map<Node, std::map<Node, std::unordered_set<Node> > >::iterator
    TC_IT;

TheorySetsRels::TheorySetsRels(Env& env,
                               SolverState& s,
                               InferenceManager& im,
                               SkolemCache& skc,
                               TermRegistry& treg)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_skCache(skc),
      d_treg(treg),
      d_shared_terms(userContext()),
      // the cycle witnesses depend on the SAT context: they are rolled back
      // on backtracking (unlike d_shared_terms)
      d_cycle_sequences(context()),
      d_cyclePrefixes(userContext())
{
  d_trueNode = nodeManager()->mkConst(true);
  d_falseNode = nodeManager()->mkConst(false);
}

TheorySetsRels::~TheorySetsRels() {}

void TheorySetsRels::check(Theory::Effort level)
{
  Trace("rels") << "\n[sets-rels] ******************************* Start the "
                   "relational solver, effort = "
                << level << " *******************************\n"
                << std::endl;
  if (Theory::fullEffort(level))
  {
    // This is the first relational step of a full-effort check: drop what the
    // previous check collected and collect the current relational terms and
    // memberships. This is the only collectRelsInfo/clearCaches pair per check;
    // the caches stay live for the transitive-closure steps that follow in this
    // pass, which consume them.
    clearCaches();
    collectRelsInfo();
    check();
    d_im.doPendingLemmas();
  }
  Assert(!d_im.hasPendingLemma());
  Trace("rels") << "\n[sets-rels] ******************************* Done with "
                   "the relational solver *******************************\n"
                << std::endl;
}

void TheorySetsRels::check()
{
  MEM_IT m_it = d_rReps_memberReps_cache.begin();

  while (m_it != d_rReps_memberReps_cache.end())
  {
    Node rel_rep = m_it->first;

    for (unsigned int i = 0; i < m_it->second.size(); i++)
    {
      Node mem = d_rReps_memberReps_cache[rel_rep][i];
      Node exp = d_rReps_memberReps_exp_cache[rel_rep][i];
      std::map<Kind, std::vector<Node> >& kind_terms = d_terms_cache[rel_rep];

      if (kind_terms.find(Kind::RELATION_TRANSPOSE) != kind_terms.end())
      {
        std::vector<Node>& tp_terms = kind_terms[Kind::RELATION_TRANSPOSE];
        if (tp_terms.size() > 0)
        {
          applyTransposeRule(tp_terms);
          applyTransposeRule(tp_terms[0], rel_rep, exp);
        }
      }
      if (kind_terms.find(Kind::RELATION_JOIN) != kind_terms.end())
      {
        std::vector<Node>& join_terms = kind_terms[Kind::RELATION_JOIN];
        for (unsigned int j = 0; j < join_terms.size(); j++)
        {
          applyJoinRule(join_terms[j], rel_rep, exp);
        }
      }
      if (kind_terms.find(Kind::RELATION_TABLE_JOIN) != kind_terms.end())
      {
        std::vector<Node>& joinTerms = kind_terms[Kind::RELATION_TABLE_JOIN];
        for (size_t j = 0; j < joinTerms.size(); j++)
        {
          applyTableJoinRule(joinTerms[j], rel_rep, exp);
        }
      }
      if (kind_terms.find(Kind::RELATION_PRODUCT) != kind_terms.end())
      {
        std::vector<Node>& product_terms = kind_terms[Kind::RELATION_PRODUCT];
        for (unsigned int j = 0; j < product_terms.size(); j++)
        {
          applyProductRule(product_terms[j], rel_rep, exp);
        }
      }
      // Note: the transitive-closure DOWN rule (applyTCRule) is not applied
      // here. It introduces fresh skolem elements and can do so unboundedly, so
      // it is run as its own step (checkTransitiveClosure), at most once per
      // postCheck. The UP rule (doTCInference, below) still runs here, using
      // the TC graph built by buildTCGraphForRel. The AcyclicDown rule is
      // still applied here for every asserted TC membership.
      if (kind_terms.find(Kind::RELATION_TCLOSURE) != kind_terms.end())
      {
        // mem     = (tuple a b) (representatives), a member of the class of
        //           rel_rep
        // exp     = (set.member (tuple a' b') S), S ~ rel_rep, a' ~ a, b' ~ b
        // tc_term = (rel.tclosure R) in the class of rel_rep
        for (const Node& tc_term : kind_terms[Kind::RELATION_TCLOSURE])
        {
          applyAcyclicDownRule(mem, tc_term, exp);
        }
      }
      if (kind_terms.find(Kind::RELATION_JOIN_IMAGE) != kind_terms.end())
      {
        std::vector<Node>& join_image_terms =
            kind_terms[Kind::RELATION_JOIN_IMAGE];
        for (unsigned int j = 0; j < join_image_terms.size(); j++)
        {
          applyJoinImageRule(mem, join_image_terms[j], exp);
        }
      }
      if (kind_terms.find(Kind::RELATION_IDEN) != kind_terms.end())
      {
        std::vector<Node>& iden_terms = kind_terms[Kind::RELATION_IDEN];
        for (unsigned int j = 0; j < iden_terms.size(); j++)
        {
          applyIdenRule(mem, iden_terms[j], exp);
        }
      }
    }
    ++m_it;
  }

  applyFunctionalRules();

  TERM_IT t_it = d_terms_cache.begin();
  while (t_it != d_terms_cache.end())
  {
    // check the terms in this equivalence class for e.g. upwards closure
    // (computeMembersForBinOpRel / computeMembersForUnaryOpRel). This is
    // done regardless of whether we have initialized
    // d_rReps_memberReps_cache for this equivalence class.
    Trace("rels-debug") << "[sets-rels] Check equivalence class: "
                        << t_it->first << std::endl;
    KIND_TERM_IT k_t_it = t_it->second.begin();

    while (k_t_it != t_it->second.end())
    {
      Trace("rels-debug") << "[sets-rels] Check " << k_t_it->second.size()
                          << " terms of kind " << k_t_it->first << std::endl;
      std::vector<Node>::iterator term_it = k_t_it->second.begin();
      if (k_t_it->first == Kind::RELATION_JOIN
          || k_t_it->first == Kind::RELATION_PRODUCT
          || k_t_it->first == Kind::RELATION_TABLE_JOIN)
      {
        while (term_it != k_t_it->second.end())
        {
          computeMembersForBinOpRel(*term_it);
          ++term_it;
        }
      }
      else if (k_t_it->first == Kind::RELATION_TRANSPOSE)
      {
        while (term_it != k_t_it->second.end())
        {
          computeMembersForUnaryOpRel(*term_it);
          ++term_it;
        }
      }
      else if (k_t_it->first == Kind::RELATION_JOIN_IMAGE)
      {
        while (term_it != k_t_it->second.end())
        {
          computeMembersForJoinImageTerm(*term_it);
          ++term_it;
        }
      }
      else if (k_t_it->first == Kind::RELATION_IDEN)
      {
        while (term_it != k_t_it->second.end())
        {
          computeMembersForIdenTerm(*term_it);
          ++term_it;
        }
      }
      ++k_t_it;
    }
    ++t_it;
  }
  // Note: the transitive-closure rules run as their own steps
  // (checkTransitiveClosureDown / checkTransitiveClosureUp) and consume the
  // caches collected above, so they are not cleared here.
}

void TheorySetsRels::clearCaches()
{
  d_tuple_reps.clear();
  d_rReps_memberReps_exp_cache.clear();
  d_terms_cache.clear();
  d_membership_trie.clear();
  d_rel_nodes.clear();
  d_rReps_memberReps_cache.clear();
  d_functional_cache.clear();
  d_rRep_tcGraph.clear();
  d_tcr_tcGraph_exps.clear();
  d_tcr_tcGraph.clear();
  d_acyclic_cache.clear();
}

void TheorySetsRels::checkAcyclicity()
{
  Trace("rels")
      << "\n[sets-rels] *********** Start acyclicity check ***********\n"
      << std::endl;
  // The cycle-witness sequences of the asserted (rel.cyclic R)
  // constraints were created (applyInstCycleRule) by collectRelsInfo, which
  // check(Theory::Effort) ran earlier in this pass. Here we unroll each of
  // them by one element and apply the split/minimality rules.
  doCycleInference();
  d_im.doPendingLemmas();
  Assert(!d_im.hasPendingLemma());
  Trace("rels")
      << "\n[sets-rels] *********** Done with acyclicity check ***********\n"
      << std::endl;
}

void TheorySetsRels::checkTransitiveClosureLastCall(bool cardinalityUsed)
{
  Trace("rels") << "\n[sets-rels] *********** Start transitive closure "
                   "last call ***********\n"
                << std::endl;
  // This runs at last-call effort, outside the full-effort pass whose caches
  // check(Theory::Effort) collected, so (re)collect from a clean slate.
  clearCaches();
  collectRelsInfo();
  for (MEM_IT m_it = d_rReps_memberReps_cache.begin();
       m_it != d_rReps_memberReps_cache.end();
       ++m_it)
  {
    Node rel_rep = m_it->first;
    std::map<Kind, std::vector<Node> >& kind_terms = d_terms_cache[rel_rep];
    if (kind_terms.find(Kind::RELATION_TCLOSURE) == kind_terms.end())
    {
      continue;
    }
    std::vector<Node>& tc_terms = kind_terms[Kind::RELATION_TCLOSURE];
    for (size_t i = 0, nmems = m_it->second.size(); i < nmems; ++i)
    {
      // mem = (tuple a b), a member of the class of rel_rep (representatives)
      // exp = (set.member (tuple a' b') S), S ~ rel_rep, a' ~ a, b' ~ b
      Node mem = d_rReps_memberReps_cache[rel_rep][i];
      Node exp = d_rReps_memberReps_exp_cache[rel_rep][i];
      // tc_rel = (rel.tclosure R) in the class of rel_rep
      for (const Node& tc_rel : tc_terms)
      {
        ensureTCGraphBuilt(tc_rel);
        if (!isTCReachable(mem, tc_rel))
        {
          if (options().sets.relsTcDownLazy)
          {
            // Lazy TC down: send the deferred case split now, for exactly the
            // memberships that are still unexplained.
            d_tcLastCall = true;
            applyTCRule(mem, tc_rel, rel_rep, exp);
            d_tcLastCall = false;
          }
          else if (cardinalityUsed)
          {
            // Cardinality-driven model completion can later introduce a fresh
            // member that would justify mem. We cannot confirm nor refute this
            // TC membership in this case, so report incompleteness.
            d_im.setModelUnsound(
                IncompleteId::SETS_RELS_TCLOSURE_GROUNDING_UNKNOWN);
          }
          else
          {
            applyTCGroundingConflict(mem, tc_rel, exp);
          }
        }
      }
    }
  }
  // don't flush pending lemmas
  clearCaches();
  Trace("rels") << "\n[sets-rels] *********** Done with transitive closure "
                   "last call ***********\n"
                << std::endl;
}

void TheorySetsRels::checkProductLastCall()
{
  // PROTOTYPE (--rels-product-lazy): products are not composed at full
  // effort; before a model is accepted every product must contain the pairs
  // of the members of its arguments.
  clearCaches();
  collectRelsInfo();
  // Composing every product here would send a quadratic number of lemmas at
  // every last call of an unsat search. Instead, check that every product
  // contains the pairs of the members of its arguments; if not, the model
  // is not sound (answer unknown, as for the hammer).
  for (auto& term_it : d_terms_cache)
  {
    auto pit = term_it.second.find(Kind::RELATION_PRODUCT);
    if (pit == term_it.second.end())
    {
      continue;
    }
    for (const Node& prod : pit->second)
    {
      Node aRep = getRepresentative(prod[0]);
      Node bRep = getRepresentative(prod[1]);
      auto ait = d_rReps_memberReps_cache.find(aRep);
      auto bit = d_rReps_memberReps_cache.find(bRep);
      if (ait == d_rReps_memberReps_cache.end()
          || bit == d_rReps_memberReps_cache.end())
      {
        continue;
      }
      auto trie = d_membership_trie.find(getRepresentative(prod));
      for (const Node& ma : ait->second)
      {
        for (const Node& mb : bit->second)
        {
          std::vector<Node> reps;
          for (const Node& m : {ma, mb})
          {
            for (size_t i = 0, n = m.getType().getTupleLength(); i < n; i++)
            {
              reps.push_back(
                  getRepresentative(TupleUtils::nthElementOfTuple(m, i)));
            }
          }
          if (trie == d_membership_trie.end()
              || trie->second.existsTerm(reps).isNull())
          {
            if (options().sets.relsProductLazyCompose)
            {
              // compose the members of this product (known ones are skipped
              // under --rels-tc-up-skip-known)
              composeMembersForRels(prod);
              goto next_product;
            }
            d_im.setModelUnsound(IncompleteId::SETS_RELS_PRODUCT_LAZY);
            clearCaches();
            return;
          }
        }
      }
    next_product:;
    }
  }
  // don't flush pending lemmas
  clearCaches();
}

void TheorySetsRels::checkJoinLastCall(bool cardinalityUsed)
{
  Trace("rels") << "\n[sets-rels] *********** Start join "
                   "last call ***********\n"
                << std::endl;
  // This runs at last-call effort, outside the full-effort pass whose caches
  // check(Theory::Effort) collected, so (re)collect from a clean slate.
  clearCaches();
  collectRelsInfo();
  for (MEM_IT m_it = d_rReps_memberReps_cache.begin();
       m_it != d_rReps_memberReps_cache.end();
       ++m_it)
  {
    Node rel_rep = m_it->first;
    std::map<Kind, std::vector<Node> >& kind_terms = d_terms_cache[rel_rep];
    if (kind_terms.find(Kind::RELATION_JOIN) == kind_terms.end())
    {
      continue;
    }
    std::vector<Node>& join_terms = kind_terms[Kind::RELATION_JOIN];
    for (size_t i = 0, nmems = m_it->second.size(); i < nmems; ++i)
    {
      // mem = (tuple x z), a member of the class of rel_rep (representatives)
      // exp = (set.member (tuple x' z') S), S ~ rel_rep, x' ~ x, z' ~ z
      Node mem = d_rReps_memberReps_cache[rel_rep][i];
      Node exp = d_rReps_memberReps_exp_cache[rel_rep][i];
      // join_rel = (rel.join A B) in the class of rel_rep
      for (const Node& join_rel : join_terms)
      {
        if (!isJoinReachable(mem, join_rel))
        {
          if (cardinalityUsed)
          {
            // Cardinality-driven model completion can later introduce a fresh
            // member that would justify mem. We cannot confirm nor refute this
            // join membership in this case, so report incompleteness.
            d_im.setModelUnsound(
                IncompleteId::SETS_RELS_JOIN_GROUNDING_UNKNOWN);
          }
          else
          {
            applyJoinGroundingConflict(mem, join_rel, exp);
          }
        }
      }
    }
  }
  // don't flush pending lemmas
  clearCaches();
  Trace("rels") << "\n[sets-rels] *********** Done with join "
                   "last call ***********\n"
                << std::endl;
}

void TheorySetsRels::checkTransitiveClosureDown()
{
  Trace("rels") << "\n[sets-rels] *********** Start transitive closure down "
                   "***********\n"
                << std::endl;
  // Seed the closure graph of every TC term with the members of its base
  // relation. This is the only place the graph is built during a check: the
  // down rule below and the up rule only add edges to it.
  for (TERM_IT t_it = d_terms_cache.begin(); t_it != d_terms_cache.end();
       ++t_it)
  {
    KIND_TERM_IT k_t_it = t_it->second.find(Kind::RELATION_TCLOSURE);
    if (k_t_it != t_it->second.end())
    {
      for (const Node& tc_term : k_t_it->second)
      {
        ensureTCGraphBuilt(tc_term);
      }
    }
  }
  // DOWN rule: for every (member, TC term) pair, apply applyTCRule. This both
  // emits the down-rule split (introducing fresh skolems) and adds the TC
  // membership as an edge of d_tcr_tcGraph, which the UP rule (doTCInference)
  // consumes. A single sweep over the current members is performed (no fixpoint
  // loop), so only finitely many fresh elements are introduced per call.
  for (MEM_IT m_it = d_rReps_memberReps_cache.begin();
       m_it != d_rReps_memberReps_cache.end();
       ++m_it)
  {
    Node rel_rep = m_it->first;
    std::map<Kind, std::vector<Node> >& kind_terms = d_terms_cache[rel_rep];
    if (kind_terms.find(Kind::RELATION_TCLOSURE) == kind_terms.end())
    {
      continue;
    }
    std::vector<Node>& tc_terms = kind_terms[Kind::RELATION_TCLOSURE];
    for (unsigned int i = 0; i < m_it->second.size(); i++)
    {
      Node mem = d_rReps_memberReps_cache[rel_rep][i];
      Node exp = d_rReps_memberReps_exp_cache[rel_rep][i];
      for (unsigned int j = 0; j < tc_terms.size(); j++)
      {
        applyTCRule(mem, tc_terms[j], rel_rep, exp);
      }
    }
  }
  Trace("rels") << "\n[sets-rels] *********** Done with transitive closure "
                   "down ***********\n"
                << std::endl;
}

void TheorySetsRels::checkTransitiveClosureUp()
{
  Trace("rels") << "\n[sets-rels] *********** Start transitive closure up "
                   "***********\n"
                << std::endl;
  // UP rule: chain the edges of the graph seeded by the base relation's
  // members and extended by the down rule. The caches are cleared at the start
  // of the next check, not here.
  doTCInference();
  d_im.doPendingLemmas();
  Assert(!d_im.hasPendingLemma());
  Trace("rels") << "\n[sets-rels] *********** Done with transitive closure up "
                   "***********\n"
                << std::endl;
}

/*
 * Populate relational terms data structure
 */

void TheorySetsRels::collectRelsInfo()
{
  Trace("rels") << "[sets-rels] Start collecting relational terms..."
                << std::endl;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    Node eqc_rep = (*eqcs_i);
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc_rep, ee);

    TypeNode erType = eqc_rep.getType();
    Trace("rels-ee") << "[sets-rels-ee] Eqc term representative: " << eqc_rep
                     << " with type " << eqc_rep.getType() << std::endl;

    while (!eqc_i.isFinished())
    {
      Node eqc_node = (*eqc_i);

      Trace("rels-ee") << "  term : " << eqc_node << std::endl;

      if (erType.isBoolean() && eqc_rep.isConst())
      {
        // eqc_node = (rel.is-functional R), asserted true or false
        if (eqc_node.getKind() == Kind::RELATION_IS_FUNCTIONAL)
        {
          if (eqc_rep.getConst<bool>())
          {
            d_functional_cache[getRepresentative(eqc_node[0])].push_back(
                eqc_node);
          }
          else
          {
            applyNotFunctionalRule(eqc_node);
          }
        }
        bool is_true_eq = eqc_rep.getConst<bool>();
        Node reason = is_true_eq ? eqc_node : eqc_node.negate();

        // collect membership info
        if (eqc_node.getKind() == Kind::SET_MEMBER
            && eqc_node[1].getType().getSetElementType().isTuple())
        {
          Node tup_rep = getRepresentative(eqc_node[0]);
          Node rel_rep = getRepresentative(eqc_node[1]);

          if (eqc_node[0].isVar())
          {
            reduceTupleVar(eqc_node);
          }

          if (is_true_eq)
          {
            if (safelyAddToMap(d_rReps_memberReps_cache, rel_rep, tup_rep))
            {
              d_rReps_memberReps_exp_cache[rel_rep].push_back(reason);
              computeTupleReps(tup_rep);
              d_membership_trie[rel_rep].addTerm(tup_rep,
                                                 d_tuple_reps[tup_rep]);
            }
          }
        }
        // collect cyclicity info
        else if (eqc_node.getKind() == Kind::RELATION_CYCLIC)
        {
          // eqc_node = (rel.cyclic u), asserted false (u is acyclic) or true
          if (!is_true_eq)
          {
            // (not (rel.cyclic u)): u is acyclic. The literal is cached under
            // the representative of u, where the acyclic-down rule looks for
            // it when it processes a membership in TC(u).
            Node u = eqc_node[0];
            d_acyclic_cache[getRepresentative(u)].push_back(eqc_node.negate());
            // The acyclic-down rule only sees the memberships of TC(u) if u
            // and TC(u) are registered terms, which they are not if the input
            // does not mention TC(u): e.g. for (not (rel.cyclic u)) with
            // (a, b) and (b, a) in u, the cycle would go unnoticed. The lemma
            // (not (rel.cyclic u)) => u subset TC(u), which is valid and is
            // not rewritten away (unlike TC(u) = TC(u)), registers them.
            // tc  = (rel.tclosure u)
            // reg = (set.subset u (rel.tclosure u)), rewritten to
            //       (= (rel.tclosure u) (set.union u (rel.tclosure u)))
            // lemma: (not (rel.cyclic u)) => reg
            Node tc = nodeManager()->mkNode(Kind::RELATION_TCLOSURE, u);
            Node reg = nodeManager()->mkNode(Kind::SET_SUBSET, u, tc);
            sendInfer(
                reg, InferenceId::SETS_RELS_ACYCLIC_DOWN, eqc_node.negate());
          }
          else
          {
            applyInstCycleRule(eqc_node);
          }
        }
        // collect relational terms info
      }
      else if (erType.isSet() && erType.getSetElementType().isTuple())
      {
        if (eqc_node.getKind() == Kind::RELATION_TRANSPOSE
            || eqc_node.getKind() == Kind::RELATION_JOIN
            || eqc_node.getKind() == Kind::RELATION_TABLE_JOIN
            || eqc_node.getKind() == Kind::RELATION_PRODUCT
            || eqc_node.getKind() == Kind::RELATION_TCLOSURE
            || eqc_node.getKind() == Kind::RELATION_JOIN_IMAGE
            || eqc_node.getKind() == Kind::RELATION_IDEN)
        {
          d_terms_cache[eqc_rep][eqc_node.getKind()].push_back(eqc_node);
        }
        // need to add all tuple elements as shared terms
      }
      else if (erType.isTuple() && !eqc_node.isConst() && !eqc_node.isVar())
      {
        std::vector<TypeNode> tupleTypes = erType.getTupleTypes();
        for (unsigned i = 0, tlen = erType.getTupleLength(); i < tlen; i++)
        {
          Node element = TupleUtils::nthElementOfTuple(eqc_node, i);
          if (!element.isConst())
          {
            makeSharedTerm(element);
          }
        }
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
  Trace("rels-debug") << "[Theory::Rels] Done with collecting relational terms!"
                      << std::endl;
}

/* RELATION_JOIN-IMAGE UP:
 *   (x, x1) IS_IN R, ..., (x, xn) IS_IN R  (R RELATION_JOIN_IMAGE n)
 *   ----------------------------------------------------------------
 *   x IS_IN (R RELATION_JOIN_IMAGE n) || NOT DISTINCT(x1, ... , xn)
 */

void TheorySetsRels::computeMembersForJoinImageTerm(Node join_image_term)
{
  Trace("rels-debug")
      << "\n[Theory::Rels] *********** Compute members for JoinImage Term = "
      << join_image_term << std::endl;
  MEM_IT rel_mem_it =
      d_rReps_memberReps_cache.find(getRepresentative(join_image_term[0]));

  if (rel_mem_it == d_rReps_memberReps_cache.end())
  {
    return;
  }
  NodeManager* nm = nodeManager();

  Node join_image_rel = join_image_term[0];
  std::unordered_set<Node> hasChecked;
  Node join_image_rel_rep = getRepresentative(join_image_rel);
  std::vector<Node>::iterator mem_rep_it = (*rel_mem_it).second.begin();
  MEM_IT rel_mem_exp_it = d_rReps_memberReps_exp_cache.find(join_image_rel_rep);
  std::vector<Node>::iterator mem_rep_exp_it = (*rel_mem_exp_it).second.begin();
  unsigned int min_card =
      join_image_term[1].getConst<Rational>().getNumerator().getUnsignedInt();

  while (mem_rep_it != (*rel_mem_it).second.end())
  {
    Node fst_mem_rep = TupleUtils::nthElementOfTuple(*mem_rep_it, 0);

    if (hasChecked.find(fst_mem_rep) != hasChecked.end())
    {
      ++mem_rep_it;
      ++mem_rep_exp_it;
      continue;
    }
    hasChecked.insert(fst_mem_rep);

    const DType& dt = join_image_term.getType().getSetElementType().getDType();
    Node new_membership = nm->mkNode(
        Kind::SET_MEMBER,
        nm->mkNode(
            Kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), fst_mem_rep),
        join_image_term);
    if (d_state.isEntailed(new_membership, true))
    {
      ++mem_rep_it;
      ++mem_rep_exp_it;
      continue;
    }

    std::vector<Node> reasons;
    std::vector<Node> existing_members;
    std::vector<Node>::iterator mem_rep_exp_it_snd =
        (*rel_mem_exp_it).second.begin();

    while (mem_rep_exp_it_snd != (*rel_mem_exp_it).second.end())
    {
      Node fst_element_snd_mem =
          TupleUtils::nthElementOfTuple((*mem_rep_exp_it_snd)[0], 0);

      if (areEqual(fst_mem_rep, fst_element_snd_mem))
      {
        bool notExist = true;
        std::vector<Node>::iterator existing_mem_it = existing_members.begin();
        Node snd_element_snd_mem =
            TupleUtils::nthElementOfTuple((*mem_rep_exp_it_snd)[0], 1);

        while (existing_mem_it != existing_members.end())
        {
          if (areEqual((*existing_mem_it), snd_element_snd_mem))
          {
            notExist = false;
            break;
          }
          ++existing_mem_it;
        }

        if (notExist)
        {
          existing_members.push_back(snd_element_snd_mem);
          reasons.push_back(*mem_rep_exp_it_snd);
          if (fst_mem_rep != fst_element_snd_mem)
          {
            reasons.push_back(nodeManager()->mkNode(
                Kind::EQUAL, fst_mem_rep, fst_element_snd_mem));
          }
          if (join_image_rel != (*mem_rep_exp_it_snd)[1])
          {
            reasons.push_back(nodeManager()->mkNode(
                Kind::EQUAL, (*mem_rep_exp_it_snd)[1], join_image_rel));
          }
          if (existing_members.size() == min_card)
          {
            if (min_card >= 2)
            {
              new_membership = nodeManager()->mkNode(
                  Kind::OR,
                  new_membership,
                  nodeManager()->mkNode(
                      Kind::NOT,
                      nodeManager()->mkNode(Kind::DISTINCT, existing_members)));
            }
            Assert(reasons.size() >= 1);
            sendInfer(new_membership,
                      InferenceId::SETS_RELS_JOIN_IMAGE_UP,
                      reasons.size() > 1 ? nm->mkNode(Kind::AND, reasons)
                                         : reasons[0]);
            break;
          }
        }
      }
      ++mem_rep_exp_it_snd;
    }
    ++mem_rep_it;
    ++mem_rep_exp_it;
  }
  Trace("rels-debug") << "\n[Theory::Rels] *********** Done with computing "
                         "members for JoinImage Term"
                      << join_image_term << "*********** " << std::endl;
}

/* RELATION_JOIN-IMAGE DOWN:
 *   (x) IS_IN (R RELATION_JOIN_IMAGE n)
 *   ------------------------------------------------------------
 *   (x, x1) IS_IN R .... (x, xn) IS_IN R  DISTINCT(x1, ... , xn)
 *
 */
void TheorySetsRels::applyJoinImageRule(Node mem_rep,
                                        Node join_image_term,
                                        Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** applyJoinImageRule on "
                      << join_image_term << " with mem_rep = " << mem_rep
                      << " and exp = " << exp << std::endl;
  if (d_rel_nodes.find(join_image_term) == d_rel_nodes.end())
  {
    computeMembersForJoinImageTerm(join_image_term);
    d_rel_nodes.insert(join_image_term);
  }

  Node join_image_rel = join_image_term[0];
  Node join_image_rel_rep = getRepresentative(join_image_rel);
  MEM_IT rel_mem_it = d_rReps_memberReps_cache.find(join_image_rel_rep);
  unsigned int min_card =
      join_image_term[1].getConst<Rational>().getNumerator().getUnsignedInt();

  if (rel_mem_it != d_rReps_memberReps_cache.end())
  {
    if (d_membership_trie.find(join_image_rel_rep) != d_membership_trie.end())
    {
      computeTupleReps(mem_rep);
      if (d_membership_trie[join_image_rel_rep]
              .findSuccessors(d_tuple_reps[mem_rep])
              .size()
          >= min_card)
      {
        return;
      }
    }
  }
  NodeManager* nm = nodeManager();
  Node reason = exp;
  Node conclusion = d_trueNode;
  std::vector<Node> distinct_skolems;
  Node fst_mem_element = TupleUtils::nthElementOfTuple(exp[0], 0);

  if (exp[1] != join_image_term)
  {
    reason = nm->mkNode(
        Kind::AND, reason, nm->mkNode(Kind::EQUAL, exp[1], join_image_term));
  }
  for (unsigned int i = 0; i < min_card; i++)
  {
    Node skolem = NodeManager::mkDummySkolem(
        "jig", join_image_rel.getType()[0].getTupleTypes()[0]);
    distinct_skolems.push_back(skolem);
    conclusion = nm->mkNode(
        Kind::AND,
        conclusion,
        nm->mkNode(
            Kind::SET_MEMBER,
            RelsUtils::constructPair(join_image_rel, fst_mem_element, skolem),
            join_image_rel));
  }
  if (distinct_skolems.size() >= 2)
  {
    conclusion = nm->mkNode(
        Kind::AND, conclusion, nm->mkNode(Kind::DISTINCT, distinct_skolems));
  }
  sendInfer(conclusion, InferenceId::SETS_RELS_JOIN_IMAGE_DOWN, reason);
  Trace("rels-debug")
      << "\n[Theory::Rels] *********** Done with applyJoinImageRule ***********"
      << std::endl;
}

/* IDENTITY-DOWN  : (x, y) IS_IN RELATION_IDEN(R)
 *               -------------------------------------------------------
 *                   x = y,  (x IS_IN R)
 *
 */

void TheorySetsRels::applyIdenRule(Node mem_rep, Node iden_term, Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** applyIdenRule on "
                      << iden_term << " with mem_rep = " << mem_rep
                      << " and exp = " << exp << std::endl;
  NodeManager* nm = nodeManager();
  if (d_rel_nodes.find(iden_term) == d_rel_nodes.end())
  {
    computeMembersForIdenTerm(iden_term);
    d_rel_nodes.insert(iden_term);
  }
  Node reason = exp;
  Node fst_mem = TupleUtils::nthElementOfTuple(exp[0], 0);
  Node snd_mem = TupleUtils::nthElementOfTuple(exp[0], 1);
  const DType& dt = iden_term[0].getType().getSetElementType().getDType();
  Node fact = nm->mkNode(
      Kind::SET_MEMBER,
      nm->mkNode(Kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), fst_mem),
      iden_term[0]);

  if (exp[1] != iden_term)
  {
    reason = nodeManager()->mkNode(
        Kind::AND,
        reason,
        nodeManager()->mkNode(Kind::EQUAL, exp[1], iden_term));
  }
  sendInfer(
      nm->mkNode(Kind::AND, fact, nm->mkNode(Kind::EQUAL, fst_mem, snd_mem)),
      InferenceId::SETS_RELS_IDENTITY_DOWN,
      reason);
  Trace("rels-debug")
      << "\n[Theory::Rels] *********** Done with applyIdenRule on " << iden_term
      << std::endl;
}

/*
 * RELATION_IS_FUNCTIONAL, mode uf (default):
 *
 *   (rel.is-functional R)    (x, y) IS_IN R
 *   ---------------------------------------
 *              y = f_R(x)
 *
 * where f_R is a fresh function symbol for R. Sound: if R is functional, then
 * f_R can be interpreted as the function that maps every x in the domain of R
 * to its unique image (and arbitrarily elsewhere). Complete: two members
 * (x1, y1), (x2, y2) with x1 = x2 in a model have y1 = f_R(x1) = f_R(x2) = y2
 * by congruence, which theory combination enforces for the shared terms x1, x2.
 * The number of lemmas is linear in the number of members of R.
 *
 * Mode pairs:
 *
 *   (rel.is-functional R)    (x1, y1) IS_IN R    (x2, y2) IS_IN R
 *   -------------------------------------------------------------
 *                    x1 = x2 => y1 = y2
 *
 * Quadratic in the number of members of R, but introduces no symbol.
 */
void TheorySetsRels::applyFunctionalRules()
{
  NodeManager* nm = nodeManager();
  options::RelsFunctionalMode mode = options().sets.relsFunctionalMode;
  if (mode == options::RelsFunctionalMode::UF
      && !logicInfo().isTheoryEnabled(THEORY_UF))
  {
    mode = options::RelsFunctionalMode::PAIRS;
  }
  for (const auto& fc : d_functional_cache)
  {
    Node relRep = fc.first;
    // Any of the constraints in this equivalence class can be used; use the
    // first one.
    Node atom = fc.second[0];
    // atom = (rel.is-functional R), asserted true
    // rel  = R, a relation of type (Relation T1 T2)
    Node rel = atom[0];
    TypeNode tupleType = rel.getType().getSetElementType();
    std::vector<TypeNode> types = tupleType.getTupleTypes();
    Assert(types.size() == 2);
    MEM_IT mit = d_rReps_memberReps_exp_cache.find(relRep);
    if (mit == d_rReps_memberReps_exp_cache.end())
    {
      continue;
    }
    // exps: the asserted memberships (set.member (tuple x y) S), S ~ R;
    // memReason adds (set.member (tuple x y) S) and (= S R)
    const std::vector<Node>& exps = mit->second;
    // the reason for a membership: the constraint, the membership, and the
    // equality between the relation of the membership and rel
    auto memReason = [&](const Node& exp, std::vector<Node>& reason) {
      reason.push_back(exp);
      if (exp[1] != rel)
      {
        reason.push_back(exp[1].eqNode(rel));
      }
    };
    if (mode == options::RelsFunctionalMode::UF)
    {
      // f: a fresh function of type (-> T1 T2), cached by R
      Node f =
          d_skCache.mkTypedSkolemCached(nm->mkFunctionType(types[0], types[1]),
                                        rel,
                                        SkolemCache::SK_FUNCTIONAL,
                                        "rfun");
      for (const Node& exp : exps)
      {
        // Conclude on the tuple of the explanation, not on its representative,
        // since the lemma is context-independent.
        Node x = TupleUtils::nthElementOfTuple(exp[0], 0);
        Node y = TupleUtils::nthElementOfTuple(exp[0], 1);
        std::vector<Node> reason{atom};
        memReason(exp, reason);
        // conc   = (= y (f x))
        // reason = (and (rel.is-functional R)
        //               (set.member (tuple x y) S)
        //               (= S R))
        Node conc = y.eqNode(nm->mkNode(Kind::APPLY_UF, f, x));
        sendInfer(conc, InferenceId::SETS_RELS_FUNCTIONAL, nm->mkAnd(reason));
      }
      continue;
    }
    Assert(mode == options::RelsFunctionalMode::PAIRS);
    for (size_t i = 0, nexps = exps.size(); i < nexps; i++)
    {
      Node x1 = TupleUtils::nthElementOfTuple(exps[i][0], 0);
      Node y1 = TupleUtils::nthElementOfTuple(exps[i][0], 1);
      for (size_t j = i + 1; j < nexps; j++)
      {
        Node x2 = TupleUtils::nthElementOfTuple(exps[j][0], 0);
        Node y2 = TupleUtils::nthElementOfTuple(exps[j][0], 1);
        if (areEqual(y1, y2) || d_state.areDisequal(x1, x2))
        {
          // nothing to infer in the current context
          continue;
        }
        std::vector<Node> reason{atom};
        memReason(exps[i], reason);
        memReason(exps[j], reason);
        // conc   = (or (not (= x1 x2)) (= y1 y2)), or (= y1 y2) if x1 is x2
        // reason = (and (rel.is-functional R)
        //               (set.member (tuple x1 y1) S1) (= S1 R)
        //               (set.member (tuple x2 y2) S2) (= S2 R))
        Node conc = y1.eqNode(y2);
        if (x1 != x2)
        {
          conc = nm->mkNode(Kind::OR, x1.eqNode(x2).negate(), conc);
        }
        sendInfer(
            conc, InferenceId::SETS_RELS_FUNCTIONAL_PAIR, nm->mkAnd(reason));
      }
    }
  }
}

/*
 * NOT RELATION_IS_FUNCTIONAL:
 *
 *             not (rel.is-functional R)
 *   -----------------------------------------------
 *   (k1, k2) IS_IN R ^ (k1, k3) IS_IN R ^ k2 != k3
 *
 * for fresh k1, k2, k3, sent once per constraint.
 */
void TheorySetsRels::applyNotFunctionalRule(Node atom)
{
  if (!d_notFunctionalSent.insert(atom).second)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  // atom = (rel.is-functional R), asserted false; rel = R
  Node rel = atom[0];
  std::vector<TypeNode> types =
      rel.getType().getSetElementType().getTupleTypes();
  Assert(types.size() == 2);
  Node k1 = d_skCache.mkTypedSkolemCached(
      types[0], rel, SkolemCache::SK_NOT_FUNCTIONAL1, "rnf1");
  Node k2 = d_skCache.mkTypedSkolemCached(
      types[1], rel, SkolemCache::SK_NOT_FUNCTIONAL2, "rnf2");
  Node k3 = d_skCache.mkTypedSkolemCached(
      types[1], rel, SkolemCache::SK_NOT_FUNCTIONAL3, "rnf3");
  // conc   = (and (set.member (tuple k1 k2) R)
  //               (set.member (tuple k1 k3) R)
  //               (not (= k2 k3)))
  // reason = (not (rel.is-functional R))
  Node conc = nm->mkNode(
      Kind::AND,
      nm->mkNode(Kind::SET_MEMBER, RelsUtils::constructPair(rel, k1, k2), rel),
      nm->mkNode(Kind::SET_MEMBER, RelsUtils::constructPair(rel, k1, k3), rel),
      k2.eqNode(k3).negate());
  sendInfer(conc, InferenceId::SETS_RELS_NOT_FUNCTIONAL, atom.negate());
}

/* RELATION_IDEN UP  : (x) IS_IN R        RELATION_IDEN(R) IN T
 *             --------------------------------
 *                   (x, x) IS_IN RELATION_IDEN(R)
 *
 */

void TheorySetsRels::computeMembersForIdenTerm(Node iden_term)
{
  Trace("rels-debug")
      << "\n[Theory::Rels] *********** Compute members for Iden Term = "
      << iden_term << std::endl;
  Node iden_term_rel = iden_term[0];
  Node iden_term_rel_rep = getRepresentative(iden_term_rel);

  if (d_rReps_memberReps_cache.find(iden_term_rel_rep)
      == d_rReps_memberReps_cache.end())
  {
    return;
  }
  NodeManager* nm = nodeManager();

  MEM_IT rel_mem_exp_it = d_rReps_memberReps_exp_cache.find(iden_term_rel_rep);
  std::vector<Node>::iterator mem_rep_exp_it = (*rel_mem_exp_it).second.begin();

  while (mem_rep_exp_it != (*rel_mem_exp_it).second.end())
  {
    Node reason = *mem_rep_exp_it;
    Node fst_exp_mem = TupleUtils::nthElementOfTuple((*mem_rep_exp_it)[0], 0);
    Node new_mem =
        RelsUtils::constructPair(iden_term, fst_exp_mem, fst_exp_mem);

    if ((*mem_rep_exp_it)[1] != iden_term_rel)
    {
      reason = nodeManager()->mkNode(
          Kind::AND,
          reason,
          nodeManager()->mkNode(
              Kind::EQUAL, (*mem_rep_exp_it)[1], iden_term_rel));
    }
    sendInfer(nm->mkNode(Kind::SET_MEMBER, new_mem, iden_term),
              InferenceId::SETS_RELS_IDENTITY_UP,
              reason);
    ++mem_rep_exp_it;
  }
  Trace("rels-debug") << "\n[Theory::Rels] *********** Done with computing "
                         "members for Iden Term = "
                      << iden_term << std::endl;
}

/*
 * Construct transitive closure graph for tc_rep based on the members of
 * tc_r_rep
 */

/*
 * RELATION_TCLOSURE RELATION_TCLOSURE(x) = x | x.x | x.x.x | ... (| is union)
 *
 * RELATION_TCLOSURE-UP I:   (a, b) IS_IN x            RELATION_TCLOSURE(x) in
 * T
 *              ---------------------------------------------
 *                              (a, b) IS_IN RELATION_TCLOSURE(x)
 *
 *
 *
 * RELATION_TCLOSURE-UP II : (a, b) IS_IN RELATION_TCLOSURE(x)  (b, c) IS_IN
 * RELATION_TCLOSURE(x)
 *              -----------------------------------------------------------
 *                            (a, c) IS_IN RELATION_TCLOSURE(x)
 *
 */
void TheorySetsRels::ensureTCGraphBuilt(Node tc_rel)
{
  if (d_rel_nodes.find(tc_rel) == d_rel_nodes.end())
  {
    buildTCGraphForRel(tc_rel);
    d_rel_nodes.insert(tc_rel);
  }
}

void TheorySetsRels::applyTCRule(Node mem_rep,
                                 Node tc_rel,
                                 Node tc_rel_rep,
                                 Node exp)
{
  Trace("rels-debug") << "[Theory::Rels] *********** Applying "
                         "RELATION_TCLOSURE rule on a tc term = "
                      << tc_rel << ", its representative = " << tc_rel_rep
                      << " with member rep = " << mem_rep
                      << " and explanation = " << exp << std::endl;
  // mem_rep = (tuple a b) (representatives)
  // tc_rel  = (rel.tclosure R)
  // exp     = (set.member (tuple a' b') S), S ~ tc_rel, a' ~ a, b' ~ b
  // The closure graph of tc_rel is normally already seeded with the members
  // of its base relation by checkTransitiveClosureDown; this is a no-op then.
  ensureTCGraphBuilt(tc_rel);

  // Unconditionally add the TC edge to the graph. Only the later TClos-Down
  // split is guarded by `reachable`.
  bool reachable = isTCReachable(mem_rep, tc_rel);
  if (reachable)
  {
    Trace("rels-tcgraph")
        << "  isTCReachable (add edge, no split) for mem_rep = " << mem_rep
        << " in " << tc_rel << std::endl;
  }

  // Record the asserted closure membership as an edge of the graph of tc_rel.
  // Always overwrite the edge's explanation with the TC membership exp, so
  // doTCInference chains the forced TC unit rather than the withdrawable base
  // grounding.
  Node fst_element_rep =
      getRepresentative(TupleUtils::nthElementOfTuple(mem_rep, 0));
  Node snd_element_rep =
      getRepresentative(TupleUtils::nthElementOfTuple(mem_rep, 1));
  addTCEdge(tc_rel, fst_element_rep, snd_element_rep, exp, true);

  // Closure induction: the pair is also in every transitive superset of the
  // base relation (see applyTCSubsetRules). This does not introduce elements
  // and is applied whether or not the membership is reachable.
  if (options().sets.relsTcSubset)
  {
    applyTCSubsetRules(tc_rel, exp);
  }

  // The TC edge has now been added above. If the membership was already
  // reachable, skip the TClos-Down case split.
  if (reachable) return;

  if (options().sets.relsAcyclicHammer)
  {
    // The TCLOSURE_DOWN case split is disabled: the TC edge above is still
    // recorded for doTCInference (TCLOSURE_UP) to consume; only this
    // case-split lemma is skipped.
    return;
  }
  if (options().sets.relsTcDownLazy && !d_tcLastCall)
  {
    // Lazy mode: the split, which introduces fresh elements, is deferred to
    // the last-call check (checkTransitiveClosureLastCall), where it is sent
    // only for memberships that the base relation's members still do not
    // explain.
    Trace("rels-tcgraph") << "  deferring TClos-Down split for " << exp
                          << std::endl;
    return;
  }
  sendTCDownSplit(tc_rel, exp);
}

void TheorySetsRels::sendTCDownSplit(Node tc_rel, Node exp)
{
  NodeManager* nm = nodeManager();
  // tc_rel = (rel.tclosure R), tc_rel[0] = R
  // exp    = (set.member (tuple a b) S), S ~ tc_rel
  //          exp[0] = (tuple a b), exp[1] = S
  // sk_1, sk_2: fresh elements
  Node fst_element = TupleUtils::nthElementOfTuple(exp[0], 0);
  Node snd_element = TupleUtils::nthElementOfTuple(exp[0], 1);
  Node sk_1 = d_skCache.mkTypedSkolemCached(fst_element.getType(),
                                            exp[0],
                                            tc_rel[0],
                                            SkolemCache::SK_TCLOSURE_DOWN1,
                                            "stc1");
  Node sk_2 = d_skCache.mkTypedSkolemCached(fst_element.getType(),
                                            exp[0],
                                            tc_rel[0],
                                            SkolemCache::SK_TCLOSURE_DOWN2,
                                            "stc2");
  // mem_of_r = (set.member (tuple a b) R)
  // sk_eq    = (= sk_1 sk_2)
  // reason   = (and exp (= (rel.tclosure R) S)), or exp if S is tc_rel
  Node mem_of_r = nm->mkNode(Kind::SET_MEMBER, exp[0], tc_rel[0]);
  Node sk_eq = nm->mkNode(Kind::EQUAL, sk_1, sk_2);
  Node reason = exp;

  if (tc_rel != exp[1])
  {
    reason =
        nm->mkNode(Kind::AND, reason, nm->mkNode(Kind::EQUAL, tc_rel, exp[1]));
  }

  // conc = (or (set.member (tuple a b) R)
  //            (and (set.member (tuple a sk_1) R)
  //                 (set.member (tuple sk_2 b) R)
  //                 (or (= sk_1 sk_2)
  //                     (set.member (tuple sk_1 sk_2) (rel.tclosure R)))))
  Node conc = nm->mkNode(
      Kind::OR,
      mem_of_r,
      nm->mkNode(
          Kind::AND,
          {nm->mkNode(Kind::SET_MEMBER,
                      RelsUtils::constructPair(tc_rel, fst_element, sk_1),
                      tc_rel[0]),
           nm->mkNode(Kind::SET_MEMBER,
                      RelsUtils::constructPair(tc_rel, sk_2, snd_element),
                      tc_rel[0]),
           nm->mkNode(Kind::OR,
                      sk_eq,
                      nm->mkNode(Kind::SET_MEMBER,
                                 RelsUtils::constructPair(tc_rel, sk_1, sk_2),
                                 tc_rel))}));

  sendInfer(conc, InferenceId::SETS_RELS_TCLOSURE_DOWN, reason);
}

/*
 * RELATION_TCLOSURE_SUBSET (closure induction, --rels-tc-subset):
 *
 *     (a,b) IN TC(R)      R SUBSET S      S;S SUBSET S
 *     -------------------------------------------------
 *                       (a,b) IN S
 *
 * TC(R) is the least transitive relation containing R (by induction on the
 * length of an R-path from a to b, every prefix of the path is in S). The
 * supersets S, numbered as in the code below:
 *  (1) S = TC(X), R syntactically in TC(X), e.g. R = TC(po) ∩ loc, S = TC(po);
 *  (2) R SUBSET S asserted (the rewritten (set.union R S) = S) and S
 *      transitive (isTransitiveClass), e.g. S = A x B or S = J;J^T with
 *      (rel.is-functional J);
 *  (3) S = R, R transitive, e.g. (rel.join R R) SUBSET R: then TC(R) = R;
 *  (4) S = R, R = A x B or R SUBSET A x B with A ∩ B = empty: no two edges
 *      compose, so TC(R) = R, e.g. fr from reads to writes;
 *  (2a) S = X for R = X ∩ Y or R = X \ Y, X transitive.
 * No fresh element is introduced: where a rule applies, one lemma replaces
 * an unbounded sequence of TCLOSURE_DOWN splits.
 */
void TheorySetsRels::applyTCSubsetRules(Node tc_rel, Node exp)
{
  NodeManager* nm = nodeManager();
  // tc_rel = (rel.tclosure R), r = R
  // exp    = (set.member (tuple a b) S), S ~ tc_rel. exp is a positive
  //          membership literal (collectRelsInfo caches only those), so
  //          exp[0] = (tuple a b) and exp[1] = S exist; tup = exp[0]
  // baseReason = exp, and (= (rel.tclosure R) S) if S is not tc_rel
  Node r = tc_rel[0];
  Node tup = exp[0];
  if (options().sets.relsTcSubsetSplit && r.getKind() == Kind::RELATION_JOIN)
  {
    // PROTOTYPE: r = (rel.join x y) with x transitive, e.g. x = co,
    // y = sm (a restriction of the identity): if r subset x holds, closure
    // induction gives TC(r) subset x. The atom is decided, true first; when
    // it is false the sets solver looks for a member of r outside x.
    // target = x if x is known to be transitive, TC(x) otherwise (always
    // transitive): r subset target gives TC(r) subset target by closure
    // induction, and the existing rules reduce TC(x) to x where they can
    // (e.g. TC(fr) = fr for fr subset Read x Write, Read and Write disjoint)
    Node x = r[0];
    std::vector<Node> why;
    bool trans = isTransitiveClass(getRepresentative(x), x, why);
    Node target = trans ? x : nm->mkNode(Kind::RELATION_TCLOSURE, x);
    if (d_subsetSplitSent.insert(std::make_pair(r, target)).second)
    {
      Node sub = rewrite(nm->mkNode(Kind::SET_SUBSET, r, target));
      if (!sub.isConst())
      {
        // a decision strategy makes the SAT solver decide the atom (true
        // first), even though no clause contains it
        d_cycleLenStrategies.emplace_back(new DecisionStrategySingleton(
            d_env, "sets_tc_subset_split", sub, d_state.getValuation()));
        d_im.getDecisionManager()->registerStrategy(
            DecisionManager::STRAT_SETS_CYCLE_LEN,
            d_cycleLenStrategies.back().get(),
            DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
        Trace("rels-cycles") << "TCSubsetSplit: " << sub << std::endl;
      }
    }
  }
  std::vector<Node> baseReason{exp};
  if (tc_rel != exp[1])
  {
    baseReason.push_back(nm->mkNode(Kind::EQUAL, tc_rel, exp[1]));
  }
  // send(P, extra):
  //   conc   = (set.member (tuple a b) P)
  //   reason = (and baseReason extra)
  auto send = [&](Node target, const std::vector<Node>& extra) {
    Node conc = nm->mkNode(Kind::SET_MEMBER, tup, target);
    if (d_state.isEntailed(conc, true))
    {
      return;
    }
    std::vector<Node> rs = baseReason;
    rs.insert(rs.end(), extra.begin(), extra.end());
    Node reason = rs.size() == 1 ? rs[0] : nm->mkNode(Kind::AND, rs);
    Trace("rels-cycles") << "TCSubset: " << conc << " from " << reason
                         << std::endl;
    sendInfer(conc, InferenceId::SETS_RELS_TCLOSURE_SUBSET, reason);
  };

  // (1) closures that syntactically include R
  for (const auto& te : d_terms_cache)
  {
    auto it = te.second.find(Kind::RELATION_TCLOSURE);
    if (it == te.second.end())
    {
      continue;
    }
    // tcx  = (rel.tclosure X) (unary, so tcx[0] = X exists); if R is
    //        syntactically in TC(X):
    // conc = (set.member (tuple a b) (rel.tclosure X)), reason = baseReason
    for (const Node& tcx : it->second)
    {
      Node x = tcx[0];
      if (tcx == tc_rel || x == r || !isSyntacticallyInTC(r, x))
      {
        continue;
      }
      send(tcx, {});
    }
  }

  Node rRep = getRepresentative(r);
  // (3) R itself transitive
  {
    std::vector<Node> extra;
    if (isTransitiveClass(rRep, r, extra))
    {
      send(r, extra);
    }
  }
  // (4) R = A x B with A and B disjoint, or R subset A x B asserted with A, B
  // disjoint: no two edges of R compose, so TC(R) = R. Disjointness is
  // (set.inter A B) = empty in the current context.
  {
    std::vector<std::pair<Node, std::vector<Node> > > products;  // product, why
    auto productsOf = [&](Node rep) {
      std::vector<Node> res;
      auto it = d_terms_cache.find(rep);
      if (it != d_terms_cache.end())
      {
        auto kIt = it->second.find(Kind::RELATION_PRODUCT);
        if (kIt != it->second.end()) res = kIt->second;
      }
      return res;
    };
    // pt  = (rel.product A B) in the class of R
    // why = (= pt R)
    for (const Node& pt : productsOf(rRep))
    {
      std::vector<Node> why;
      if (pt != r) why.push_back(nm->mkNode(Kind::EQUAL, pt, r));
      products.emplace_back(pt, why);
    }
    // The union index maps rep(u[0]) -> rep(u[1]) -> u for the terms
    //   u = (set.union u[0] u[1])
    // (for a congruent duplicate: u[0] -> u[1] -> u). Only the binary
    // set.union, set.inter and set.minus are indexed, so u[0] and u[1] exist.
    // A union with an operand R' ~ R that is equal to its other operand P is
    // the rewritten form of (set.subset R P).
    const std::map<Node, std::map<Node, Node> >& uidx2 =
        d_state.getBinaryOpIndex(Kind::SET_UNION);
    for (const auto& e1 : uidx2)
    {
      for (const auto& e2 : e1.second)
      {
        Node u = e2.second;
        Node uRep = getRepresentative(u);
        Node pside, rside;
        // u = (set.union R' P), R' ~ R, u ~ P   (first case)
        // u = (set.union P R'), R' ~ R, u ~ P   (second case)
        if (e1.first == rRep && uRep == e2.first)
        {
          rside = u[0];
          pside = u[1];
        }
        else if (e2.first == rRep && uRep == e1.first)
        {
          rside = u[1];
          pside = u[0];
        }
        else
        {
          continue;
        }
        for (const Node& pt : productsOf(getRepresentative(pside)))
        {
          std::vector<Node> why;
          // pt  = (rel.product A B) in the class of P
          // why = (= u P), (= R' R), (= pt P), each only if the terms differ
          why.push_back(nm->mkNode(Kind::EQUAL, u, pside));
          if (rside != r) why.push_back(nm->mkNode(Kind::EQUAL, rside, r));
          if (pt != pside) why.push_back(nm->mkNode(Kind::EQUAL, pt, pside));
          products.emplace_back(pt, why);
          break;
        }
      }
    }
    const std::map<Node, std::map<Node, Node> >& iidx =
        d_state.getBinaryOpIndex(Kind::SET_INTER);
    for (const auto& [pt, why] : products)
    {
      // pt    = (rel.product A B) (binary): pt[0] = A, pt[1] = B
      // inter = (set.inter A' B') or (set.inter B' A'), A' ~ A, B' ~ B,
      //         from the intersection index (binary, so inter[0] and
      //         inter[1] exist)
      Node a = getRepresentative(pt[0]);
      Node b = getRepresentative(pt[1]);
      Node inter;
      auto it1 = iidx.find(a);
      if (it1 != iidx.end())
      {
        auto it2 = it1->second.find(b);
        if (it2 != it1->second.end()) inter = it2->second;
      }
      if (inter.isNull())
      {
        auto it3 = iidx.find(b);
        if (it3 != iidx.end())
        {
          auto it4 = it3->second.find(a);
          if (it4 != it3->second.end()) inter = it4->second;
        }
      }
      if (inter.isNull()) continue;
      Node interRep = getRepresentative(inter);
      // disjoint: (= (set.inter A' B') (as set.empty (Set (Tuple T))))
      if (interRep.getKind() != Kind::SET_EMPTY) continue;
      // extra = why, (= inter empty), (= inter[0] A), (= inter[1] B), the
      //         last two only if the terms differ
      // conc  = (set.member (tuple a b) R)
      std::vector<Node> extra = why;
      extra.push_back(nm->mkNode(Kind::EQUAL, inter, interRep));
      if (inter[0] != pt[0])
        extra.push_back(nm->mkNode(Kind::EQUAL, inter[0], pt[0]));
      if (inter[1] != pt[1])
        extra.push_back(nm->mkNode(Kind::EQUAL, inter[1], pt[1]));
      // Swapped operands: inter = (set.inter B' A') was found as
      // iidx[b][a], which is only reached if a != b (otherwise it is the
      // lookup iidx[a][b]). Then inter[0] ~ b and pt[0] ~ a differ, and so
      // do inter[1] ~ a and pt[1] ~ b: both equalities above were pushed,
      // and the two pop_backs remove them.
      if (getRepresentative(inter[0]) != a)
      {
        extra.pop_back();
        extra.pop_back();
        if (inter[1] != pt[0])
          extra.push_back(nm->mkNode(Kind::EQUAL, inter[1], pt[0]));
        if (inter[0] != pt[1])
          extra.push_back(nm->mkNode(Kind::EQUAL, inter[0], pt[1]));
      }
      send(r, extra);
      break;
    }
  }
  // (2a) syntactic supersets: R = (set.inter X Y) is included in X and in Y,
  // R = (set.minus X Y) in X
  {
    std::vector<Node> syn;
    // r = (set.inter X Y): R is a subset of X and of Y
    // r = (set.minus X Y): R is a subset of X
    // (the kind is checked before r[0] and r[1] are read)
    // conc = (set.member (tuple a b) X) if X is transitive
    if (r.getKind() == Kind::SET_INTER)
    {
      syn.push_back(r[0]);
      syn.push_back(r[1]);
    }
    else if (r.getKind() == Kind::SET_MINUS)
    {
      syn.push_back(r[0]);
    }
    for (const Node& x : syn)
    {
      std::vector<Node> extra;
      if (isTransitiveClass(getRepresentative(x), x, extra))
      {
        send(x, extra);
      }
    }
  }
  // (2) asserted supersets: (set.union R' P) = P or (set.union P R') = P
  const std::map<Node, std::map<Node, Node> >& uidx =
      d_state.getBinaryOpIndex(Kind::SET_UNION);
  for (const auto& e1 : uidx)
  {
    for (const auto& e2 : e1.second)
    {
      Node u = e2.second;
      Node uRep = getRepresentative(u);
      // u = (set.union R' P) or (set.union P R'), R' ~ R, u ~ P: the rewritten
      // (set.subset R P); unions are binary, so u[0] and u[1] exist
      Node p, rPrime;
      if (e1.first == rRep && uRep == e2.first)
      {
        rPrime = u[0];
        p = u[1];
      }
      else if (e2.first == rRep && uRep == e1.first)
      {
        rPrime = u[1];
        p = u[0];
      }
      else
      {
        continue;
      }
      if (getRepresentative(p) == rRep)
      {
        continue;  // R subset R, handled by (3)
      }
      std::vector<Node> extra;
      // extra = (= u P), (= R' R), and why P is transitive (isTransitiveClass)
      // conc  = (set.member (tuple a b) P)
      extra.push_back(nm->mkNode(Kind::EQUAL, u, p));
      if (rPrime != r)
      {
        extra.push_back(nm->mkNode(Kind::EQUAL, rPrime, r));
      }
      if (isTransitiveClass(getRepresentative(p), p, extra))
      {
        send(p, extra);
      }
    }
  }
}

bool TheorySetsRels::isTransitiveClass(Node pRep,
                                       Node p,
                                       std::vector<Node>& reason)
{
  NodeManager* nm = nodeManager();
  // a product, closure or identity relation in the class (relational terms
  // are indexed by this solver's term cache, not by the set solver state)
  auto tcIt = d_terms_cache.find(pRep);
  if (tcIt != d_terms_cache.end())
  {
    for (Kind k :
         {Kind::RELATION_PRODUCT, Kind::RELATION_TCLOSURE, Kind::RELATION_IDEN})
    {
      auto kIt = tcIt->second.find(k);
      if (kIt == tcIt->second.end() || kIt->second.empty())
      {
        continue;
      }
      // pt = (rel.product A B), (rel.tclosure X) or (rel.iden A) in the
      //      class of p (the vector is not empty, checked above)
      // reason: (= pt p)
      Node pt = kIt->second[0];
      if (pt != p)
      {
        reason.push_back(nm->mkNode(Kind::EQUAL, pt, p));
      }
      return true;
    }
  }
  const std::map<Node, std::map<Node, Node> >& uidx =
      d_state.getBinaryOpIndex(Kind::SET_UNION);
  // J ; J^T with J functional: the class of p contains (rel.join P Q) where
  // one of P, Q is the transpose of the other, so that (rel.join P Q) is
  // P;P^T modulo equality, and (rel.is-functional P') is asserted for some
  // P' ~ P. Then (P;P^T);(P;P^T) = P;(P^T;P);P^T, and P^T;P only relates
  // equal elements, so this is a subset of P;P^T.
  if (tcIt != d_terms_cache.end())
  {
    auto jIt = tcIt->second.find(Kind::RELATION_JOIN);
    if (jIt != tcIt->second.end())
    {
      for (const Node& sj : jIt->second)
      {
        // sj = (rel.join P Q) in the class of p (joins are binary)
        Node P = sj[0], Q = sj[1];
        // pt: P = (rel.transpose Q'), Q' ~ Q,
        //     so sj = (rel.join (rel.transpose Q') Q)
        // qt: Q = (rel.transpose P'), P' ~ P,
        //     so sj = (rel.join P (rel.transpose P'))
        // P[0] and Q[0] are only read after their kind is checked (&& is
        // short-circuit)
        bool pt = P.getKind() == Kind::RELATION_TRANSPOSE
                  && getRepresentative(P[0]) == getRepresentative(Q);
        bool qt = Q.getKind() == Kind::RELATION_TRANSPOSE
                  && getRepresentative(Q[0]) == getRepresentative(P);
        if (!pt && !qt)
        {
          continue;
        }
        auto fcIt = d_functional_cache.find(getRepresentative(P));
        if (fcIt == d_functional_cache.end())
        {
          continue;
        }
        // atom   = (rel.is-functional P''), P'' ~ P (the vectors of
        //          d_functional_cache are never empty)
        // reason = atom, (= P'' P), (= sj p), and (= Q' Q) or (= P' P),
        //          each only if the terms differ
        Node atom = fcIt->second[0];
        reason.push_back(atom);
        if (atom[0] != P) reason.push_back(atom[0].eqNode(P));
        if (sj != p) reason.push_back(sj.eqNode(p));
        if (pt && P[0] != Q) reason.push_back(P[0].eqNode(Q));
        if (qt && Q[0] != P) reason.push_back(Q[0].eqNode(P));
        return true;
      }
    }
  }
  // (rel.join p p) subset p asserted: a join term j of two relations in the
  // class of p, and (set.union j p) = p in the current context
  for (const auto& te : d_terms_cache)
  {
    auto it = te.second.find(Kind::RELATION_JOIN);
    if (it == te.second.end())
    {
      continue;
    }
    for (const Node& j : it->second)
    {
      // j = (rel.join J1 J2) (binary), J1 ~ J2 ~ p
      if (getRepresentative(j[0]) != pRep || getRepresentative(j[1]) != pRep)
      {
        continue;
      }
      // u = (set.union j' p') or (set.union p' j'), j' ~ j, p' ~ p, u ~ p: the
      // rewritten (set.subset (rel.join p p) p)
      Node jRep = getRepresentative(j);
      Node u;
      auto it1 = uidx.find(jRep);
      if (it1 != uidx.end())
      {
        auto it2 = it1->second.find(pRep);
        if (it2 != it1->second.end() && getRepresentative(it2->second) == pRep)
        {
          u = it2->second;
        }
      }
      if (u.isNull())
      {
        auto it3 = uidx.find(pRep);
        if (it3 != uidx.end())
        {
          auto it4 = it3->second.find(jRep);
          if (it4 != it3->second.end()
              && getRepresentative(it4->second) == pRep)
          {
            u = it4->second;
          }
        }
      }
      if (u.isNull())
      {
        continue;
      }
      // the asserted subset literal and the equalities tying its operands to
      // j and p
      // pSide = p', jSide = j'
      // reason: (= u p'), (= p' p), (= j' j), (= J1 p), (= J2 p), each only if
      //         the terms differ
      Node pSide = getRepresentative(u[0]) == jRep ? u[1] : u[0];
      Node jSide = pSide == u[1] ? u[0] : u[1];
      reason.push_back(nm->mkNode(Kind::EQUAL, u, pSide));
      if (pSide != p) reason.push_back(nm->mkNode(Kind::EQUAL, pSide, p));
      if (jSide != j) reason.push_back(nm->mkNode(Kind::EQUAL, jSide, j));
      if (j[0] != p) reason.push_back(nm->mkNode(Kind::EQUAL, j[0], p));
      if (j[1] != p) reason.push_back(nm->mkNode(Kind::EQUAL, j[1], p));
      return true;
    }
  }
  return false;
}

void TheorySetsRels::applyTCGroundingConflict(Node mem_rep,
                                              Node tc_rel,
                                              Node exp)
{
  Trace("rels-debug") << "[Theory::Rels] *********** Applying "
                         "RELATION_TCLOSURE grounding conflict on a tc term "
                         "= "
                      << tc_rel << " with member rep = " << mem_rep
                      << " and explanation = " << exp << std::endl;

  NodeManager* nm = nodeManager();
  // tc_rel  = (rel.tclosure R), rel = R
  // mem_rep = (tuple a b) (representatives)
  // exp     = (set.member (tuple a' b') S), S ~ tc_rel
  Node rel = tc_rel[0];
  Node rel_rep = getRepresentative(rel);

  // Build the set containing exactly rel's currently-known positive
  // members, and collect each component of each member of R and their
  // representatives.
  Node relValue;
  std::map<Node, Node> memMap;   // original term -> representative
  std::set<Node> memComponents;  // representatives of the member components
  MEM_IT mem_it = d_rReps_memberReps_cache.find(rel_rep);
  if (mem_it != d_rReps_memberReps_cache.end())
  {
    for (const Node& m : mem_it->second)
    {
      // m        = (tuple x y), a known member of R
      // relValue = (set.union (set.union (set.singleton m1) (set.singleton m2))
      //                       ...)
      Node singleton = nm->mkNode(Kind::SET_SINGLETON, m);
      relValue = relValue.isNull()
                     ? singleton
                     : nm->mkNode(Kind::SET_UNION, relValue, singleton);
      Node srcTerm = TupleUtils::nthElementOfTuple(m, 0);
      Node srcRep = getRepresentative(srcTerm);
      Node sinkTerm = TupleUtils::nthElementOfTuple(m, 1);
      Node sinkRep = getRepresentative(sinkTerm);
      memMap.emplace(srcTerm, srcRep);
      memMap.emplace(sinkTerm, sinkRep);
      memComponents.insert(srcRep);
      memComponents.insert(sinkRep);
    }
  }
  if (relValue.isNull())
  {
    // no known member: relValue = (as set.empty (Relation T T))
    relValue = d_treg.getEmptySet(rel.getType());
  }

  // encode the model into the lemma's antecedent. Include the tc(R)-membership,
  // the known members of R, and assert equality between each member component
  // and its representative. Also assert that the representatives of the member
  // components are distinct.
  // lemma: (and exp (= R relValue) (= a0 rep(a0)) ... (distinct reps)) => false
  // e.g.   (and (set.member (tuple a c) (rel.tclosure R))
  //             (= R (set.singleton (tuple a b)))
  //             (distinct a b c))
  //        => false
  Node a0 = TupleUtils::nthElementOfTuple(mem_rep, 0);
  Node aRep = getRepresentative(a0);
  Node b0 = TupleUtils::nthElementOfTuple(mem_rep, 1);
  Node bRep = getRepresentative(b0);
  std::vector<Node> reasonConjuncts;
  reasonConjuncts.push_back(exp);
  reasonConjuncts.push_back(nm->mkNode(Kind::EQUAL, rel, relValue));
  if (a0 != aRep)
  {
    reasonConjuncts.push_back(nm->mkNode(Kind::EQUAL, a0, aRep));
  }
  if (b0 != bRep)
  {
    reasonConjuncts.push_back(nm->mkNode(Kind::EQUAL, b0, bRep));
  }
  for (const auto& [memTerm, memRep] : memMap)
  {
    if (memTerm != memRep)
    {
      reasonConjuncts.push_back(nm->mkNode(Kind::EQUAL, memTerm, memRep));
    }
  }
  memComponents.insert(aRep);
  memComponents.insert(bRep);

  if (memComponents.size() >= 2)
  {
    std::vector<Node> distinctReps(memComponents.begin(), memComponents.end());
    reasonConjuncts.push_back(nm->mkNode(Kind::DISTINCT, distinctReps));
  }

  Node reason = reasonConjuncts.size() == 1
                    ? reasonConjuncts[0]
                    : nm->mkNode(Kind::AND, reasonConjuncts);

  Trace("rels-cycles") << "TCGroundingConflict: " << reason << " => false"
                       << std::endl;

  sendInfer(
      d_falseNode, InferenceId::SETS_RELS_TCLOSURE_GROUNDING_CONFLICT, reason);
}

void TheorySetsRels::applyJoinGroundingConflict(Node mem_rep,
                                                Node join_rel,
                                                Node exp)
{
  Trace("rels-debug") << "[Theory::Rels] *********** Applying "
                         "RELATION_JOIN grounding conflict on a join term "
                         "= "
                      << join_rel << " with member rep = " << mem_rep
                      << " and explanation = " << exp << std::endl;

  NodeManager* nm = nodeManager();
  // the components of a tuple with their representatives
  std::map<Node, Node> compMap;
  std::set<Node> compReps;
  auto addComponents = [&](const Node& tup) {
    for (size_t i = 0, n = tup.getType().getTupleLength(); i < n; i++)
    {
      Node t = TupleUtils::nthElementOfTuple(tup, i);
      Node r = getRepresentative(t);
      compMap.emplace(t, r);
      compReps.insert(r);
    }
  };
  // the set of the currently known members of rel
  // knownValue(A) = (set.union ... (set.singleton m1) ... (set.singleton mn))
  //                 for the known members mi = (tuple ...) of A, or
  //                 (as set.empty ...) if there is none
  auto knownValue = [&](Node rel) {
    Node value;
    MEM_IT mem_it = d_rReps_memberReps_cache.find(getRepresentative(rel));
    if (mem_it != d_rReps_memberReps_cache.end())
    {
      for (const Node& m : mem_it->second)
      {
        addComponents(m);
        Node singleton = nm->mkNode(Kind::SET_SINGLETON, m);
        value = value.isNull() ? singleton
                               : nm->mkNode(Kind::SET_UNION, value, singleton);
      }
    }
    return value.isNull() ? d_treg.getEmptySet(rel.getType()) : value;
  };
  // join_rel = (rel.join A B), r1 = A, r2 = B
  // exp      = (set.member (tuple x z) S), S ~ join_rel
  // mem_rep  = (tuple x z) (representatives)
  // lemma: (and exp (= A knownValue(A)) (= B knownValue(B))
  //             (= t rep(t)) ... (distinct reps))
  //        => false
  Node r1 = join_rel[0];
  Node r2 = join_rel[1];
  std::vector<Node> conj{exp,
                         nm->mkNode(Kind::EQUAL, r1, knownValue(r1)),
                         nm->mkNode(Kind::EQUAL, r2, knownValue(r2))};
  addComponents(mem_rep);
  // As in applyTCGroundingConflict, the elements must be distinct: otherwise
  // a later merge of two of them (e.g. b = d for (a, c) in A;B with
  // A = {(a, b)} and B = {(d, c)}) justifies the membership.
  for (const auto& [t, r] : compMap)
  {
    if (t != r)
    {
      conj.push_back(nm->mkNode(Kind::EQUAL, t, r));
    }
  }
  if (compReps.size() >= 2)
  {
    conj.push_back(nm->mkNode(
        Kind::DISTINCT, std::vector<Node>(compReps.begin(), compReps.end())));
  }
  Node reason = nm->mkNode(Kind::AND, conj);

  Trace("rels-cycles") << "JoinGroundingConflict: " << reason << " => false"
                       << std::endl;

  sendInfer(
      d_falseNode, InferenceId::SETS_RELS_JOIN_GROUNDING_CONFLICT, reason);
}

bool TheorySetsRels::isJoinReachable(Node mem_rep, Node join_rel)
{
  // join_rel = (rel.join A B), A of arity n, B of arity m
  // mem_rep  = (tuple x1 ... x(n-1) z1 ... z(m-1)) (representatives)
  // Reachable if, for some y, the known members of A and B contain
  //   (tuple x1 ... x(n-1) y) and (tuple y z1 ... z(m-1))
  Node r1 = join_rel[0];
  Node r2 = join_rel[1];
  Node r1_rep = getRepresentative(r1);
  Node r2_rep = getRepresentative(r2);

  size_t s1_len = r1.getType().getSetElementType().getTupleLength();
  size_t tup_len = join_rel.getType().getSetElementType().getTupleLength();

  computeTupleReps(mem_rep);
  std::vector<Node>& mem_reps = d_tuple_reps[mem_rep];

  MEM_IT r1_mem_it = d_rReps_memberReps_cache.find(r1_rep);
  if (r1_mem_it == d_rReps_memberReps_cache.end())
  {
    return false;
  }
  for (const Node& r1_mem : r1_mem_it->second)
  {
    computeTupleReps(r1_mem);
    std::vector<Node>& r1_mem_reps = d_tuple_reps[r1_mem];
    // r1_mem must agree with mem_rep on the join_rel[0]-side prefix (all of
    // r1_mem's components except its last, the candidate shared element).
    bool prefixMatches = true;
    for (size_t k = 0; k + 1 < s1_len; ++k)
    {
      if (r1_mem_reps[k] != mem_reps[k])
      {
        prefixMatches = false;
        break;
      }
    }
    if (!prefixMatches)
    {
      continue;
    }
    Node shared_cand = r1_mem_reps[s1_len - 1];
    std::vector<Node> r2_pattern;
    r2_pattern.push_back(shared_cand);
    for (size_t k = s1_len - 1; k < tup_len; ++k)
    {
      r2_pattern.push_back(mem_reps[k]);
    }
    if (d_membership_trie[r2_rep].existsTerm(r2_pattern) != Node::null())
    {
      return true;
    }
  }
  return false;
}

bool TheorySetsRels::isTCReachable(Node mem_rep, Node tc_rel)
{
  MEM_IT mem_it = d_rReps_memberReps_cache.find(getRepresentative(tc_rel[0]));

  if (mem_it != d_rReps_memberReps_cache.end()
      && std::find((mem_it->second).begin(), (mem_it->second).end(), mem_rep)
             != (mem_it->second).end())
  {
    return true;
  }

  TC_IT tc_it = d_rRep_tcGraph.find(getRepresentative(tc_rel[0]));
  if (tc_it != d_rRep_tcGraph.end())
  {
    bool isReachable = false;
    std::unordered_set<Node> seen;
    // Use mem_rep_0 and mem_rep_1 to ensure deterministic node ID assignments
    Node mem_rep_0 =
        getRepresentative(TupleUtils::nthElementOfTuple(mem_rep, 0));
    Node mem_rep_1 =
        getRepresentative(TupleUtils::nthElementOfTuple(mem_rep, 1));
    isTCReachable(getRepresentative(mem_rep_0),
                  getRepresentative(mem_rep_1),
                  seen,
                  tc_it->second,
                  isReachable);
    return isReachable;
  }
  return false;
}

void TheorySetsRels::isTCReachable(
    Node start,
    Node dest,
    std::unordered_set<Node>& hasSeen,
    std::map<Node, std::unordered_set<Node> >& tc_graph,
    bool& isReachable)
{
  if (hasSeen.find(start) == hasSeen.end())
  {
    hasSeen.insert(start);
  }

  TC_GRAPH_IT pair_set_it = tc_graph.find(start);

  if (pair_set_it != tc_graph.end())
  {
    if (pair_set_it->second.find(dest) != pair_set_it->second.end())
    {
      isReachable = true;
      return;
    }
    else
    {
      std::unordered_set<Node>::iterator set_it = pair_set_it->second.begin();

      while (set_it != pair_set_it->second.end())
      {
        // need to check if *set_it has been looked already
        if (hasSeen.find(*set_it) == hasSeen.end())
        {
          isTCReachable(*set_it, dest, hasSeen, tc_graph, isReachable);
        }
        ++set_it;
      }
    }
  }
}

void TheorySetsRels::addTCEdge(
    Node tc_rel, Node fst_rep, Node snd_rep, Node exp, bool overwriteExp)
{
  // A closure graph only ever grows: an edge and its explanation are added if
  // the edge is new, and nothing is removed, so the memberships that
  // applyTCRule and buildTCGraphForRel contribute for the same term accumulate
  // instead of one discarding the other. An edge already in the graph keeps
  // the explanation it was added with, unless overwriteExp is set (applyTCRule
  // does this so that an asserted TC membership takes precedence over the
  // base-relation membership that seeded the same edge).
  d_tcr_tcGraph[tc_rel][fst_rep].insert(snd_rep);
  // edge = (tuple fst_rep snd_rep), for tc_rel = (rel.tclosure R)
  // exp  = (set.member (tuple a b) S), S ~ R or S ~ tc_rel
  Node edge = RelsUtils::constructPair(tc_rel, fst_rep, snd_rep);
  if (overwriteExp)
  {
    d_tcr_tcGraph_exps[tc_rel][edge] = exp;
  }
  else
  {
    d_tcr_tcGraph_exps[tc_rel].emplace(edge, exp);
  }
}

void TheorySetsRels::buildTCGraphForRel(Node tc_rel)
{
  Node rel_rep = getRepresentative(tc_rel[0]);
  MEM_IT mem_it = d_rReps_memberReps_cache.find(rel_rep);
  if (mem_it == d_rReps_memberReps_cache.end())
  {
    // the base relation has no asserted members, so there is nothing to add
    return;
  }
  const std::vector<Node>& members = mem_it->second;
  const std::vector<Node>& exps = d_rReps_memberReps_exp_cache[rel_rep];
  // collectRelsInfo maintains these two as parallel vectors
  Assert(members.size() == exps.size());

  std::map<Node, std::unordered_set<Node> >& rel_tc_graph =
      d_rRep_tcGraph[rel_rep];
  for (size_t i = 0, msize = members.size(); i < msize; i++)
  {
    Node fst_element_rep =
        getRepresentative(TupleUtils::nthElementOfTuple(members[i], 0));
    Node snd_element_rep =
        getRepresentative(TupleUtils::nthElementOfTuple(members[i], 1));
    // the members of the base relation are edges of the closure graph, and are
    // tracked per base relation as well for isTCReachable
    rel_tc_graph[fst_element_rep].insert(snd_element_rep);
    addTCEdge(tc_rel, fst_element_rep, snd_element_rep, exps[i]);
  }
}

void TheorySetsRels::doTCInference(
    std::map<Node, std::unordered_set<Node> > rel_tc_graph,
    std::map<Node, Node> rel_tc_graph_exps,
    Node tc_rel)
{
  Trace("rels-debug") << "[Theory::Rels] ****** doTCInference !" << std::endl;
  for (TC_GRAPH_IT tc_graph_it = rel_tc_graph.begin();
       tc_graph_it != rel_tc_graph.end();
       ++tc_graph_it)
  {
    for (std::unordered_set<Node>::iterator snd_elements_it =
             tc_graph_it->second.begin();
         snd_elements_it != tc_graph_it->second.end();
         ++snd_elements_it)
    {
      std::vector<Node> reasons;
      std::unordered_set<Node> seen;
      Node tuple =
          RelsUtils::constructPair(tc_rel,
                                   getRepresentative(tc_graph_it->first),
                                   getRepresentative(*snd_elements_it));
      Assert(rel_tc_graph_exps.find(tuple) != rel_tc_graph_exps.end());
      Node exp = rel_tc_graph_exps.find(tuple)->second;

      reasons.push_back(exp);
      seen.insert(tc_graph_it->first);
      doTCInference(tc_rel,
                    reasons,
                    rel_tc_graph,
                    rel_tc_graph_exps,
                    tc_graph_it->first,
                    *snd_elements_it,
                    seen);
    }
  }
  Trace("rels-debug") << "[Theory::Rels] ****** Done with doTCInference !"
                      << std::endl;
}

void TheorySetsRels::doTCInference(
    Node tc_rel,
    std::vector<Node> reasons,
    std::map<Node, std::unordered_set<Node> >& tc_graph,
    std::map<Node, Node>& rel_tc_graph_exps,
    Node start_node_rep,
    Node cur_node_rep,
    std::unordered_set<Node>& seen)
{
  NodeManager* nm = nodeManager();
  // Use reasons_front_0 and reasons_back_1 to ensure deterministic node ID
  // assignments
  Node reasons_front_0 = TupleUtils::nthElementOfTuple((reasons.front())[0], 0);
  Node reasons_back_1 = TupleUtils::nthElementOfTuple((reasons.back())[0], 1);
  Node tc_mem =
      RelsUtils::constructPair(tc_rel, reasons_front_0, reasons_back_1);
  std::vector<Node> all_reasons(reasons);

  // reasons[i] = (set.member (tuple ai bi) Si), the explanation of the i-th
  //              edge of the path, Si ~ R or Si ~ tc_rel = (rel.tclosure R)
  // tc_mem     = (tuple a1 bn)
  // conclusion = (set.member (tuple a1 bn) (rel.tclosure R))
  // reason     = the edges, (= bi a(i+1)), and the equalities of addSetEq
  // The edges of the TC graph are memberships either in (a term equal to)
  // the base relation tc_rel[0] or in (a term equal to) tc_rel itself (TC
  // memberships are added as edges by applyTCRule). For an explanation whose
  // set is syntactically neither, we must add the equality that actually
  // holds in the current context. Previously tc_rel[0] = S was always added;
  // when S was in fact a (purified) term equal to tc_rel, that antecedent was
  // false, the forward lemma could never fire, and cycles in the base relation
  // went undetected (wrong "sat" answers against acyclicity constraints).
  auto addSetEq = [&](Node s) {
    if (s == tc_rel || s == tc_rel[0])
    {
      return;
    }
    if (areEqual(s, tc_rel) && !areEqual(s, tc_rel[0]))
    {
      all_reasons.push_back(nodeManager()->mkNode(Kind::EQUAL, tc_rel, s));
    }
    else
    {
      all_reasons.push_back(nodeManager()->mkNode(Kind::EQUAL, tc_rel[0], s));
    }
  };
  for (unsigned int i = 0; i < reasons.size() - 1; i++)
  {
    Node fst_element_end = TupleUtils::nthElementOfTuple(reasons[i][0], 1);
    Node snd_element_begin =
        TupleUtils::nthElementOfTuple(reasons[i + 1][0], 0);
    if (fst_element_end != snd_element_begin)
    {
      all_reasons.push_back(nodeManager()->mkNode(
          Kind::EQUAL, fst_element_end, snd_element_begin));
    }
    addSetEq(reasons[i][1]);
  }
  addSetEq(reasons.back()[1]);
  // PROTOTYPE (--rels-tc-up-skip-known): the pair is already a member of the
  // closure in the current context: the lemma would only add another
  // explanation of a known fact
  bool known = false;
  if (options().sets.relsTcUpSkipKnown)
  {
    Node tcRep = getRepresentative(tc_rel);
    auto trie = d_membership_trie.find(tcRep);
    if (trie != d_membership_trie.end())
    {
      std::vector<Node> pairReps{getRepresentative(reasons_front_0),
                                 getRepresentative(reasons_back_1)};
      known = !trie->second.existsTerm(pairReps).isNull();
    }
  }
  if (known)
  {
    // nothing to send
  }
  else if (all_reasons.size() > 1)
  {
    // Use andReasons to ensure deterministic node ID assignments
    Node andReasons = nm->mkNode(Kind::AND, all_reasons);
    sendInfer(nm->mkNode(Kind::SET_MEMBER, tc_mem, tc_rel),
              InferenceId::SETS_RELS_TCLOSURE_UP,
              andReasons);
  }
  else
  {
    sendInfer(nm->mkNode(Kind::SET_MEMBER, tc_mem, tc_rel),
              InferenceId::SETS_RELS_TCLOSURE_UP,
              all_reasons.front());
  }

  // check if cur_node has been traversed or not
  if (seen.find(cur_node_rep) != seen.end())
  {
    return;
  }
  seen.insert(cur_node_rep);
  TC_GRAPH_IT cur_set = tc_graph.find(cur_node_rep);
  if (cur_set != tc_graph.end())
  {
    for (std::unordered_set<Node>::iterator set_it = cur_set->second.begin();
         set_it != cur_set->second.end();
         ++set_it)
    {
      Node new_pair = RelsUtils::constructPair(tc_rel, cur_node_rep, *set_it);
      std::vector<Node> new_reasons(reasons);
      new_reasons.push_back(rel_tc_graph_exps.find(new_pair)->second);
      doTCInference(tc_rel,
                    new_reasons,
                    tc_graph,
                    rel_tc_graph_exps,
                    start_node_rep,
                    *set_it,
                    seen);
    }
  }
}

/*  product-split rule:  (a, b) IS_IN (X RELATION_PRODUCT Y)
 *                     ----------------------------------
 *                       a IS_IN X  && b IS_IN Y
 *
 *  product-compose rule: (a, b) IS_IN X    (c, d) IS_IN Y
 *                        ---------------------------------
 *                        (a, b, c, d) IS_IN (X RELATION_PRODUCT Y)
 */

void TheorySetsRels::applyProductRule(Node pt_rel, Node pt_rel_rep, Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_PRODUCT rule on producted term = "
                      << pt_rel << ", its representative = " << pt_rel_rep
                      << " with explanation = " << exp << std::endl;

  if (d_rel_nodes.find(pt_rel) == d_rel_nodes.end())
  {
    Trace("rels-debug")
        << "\n[Theory::Rels] Apply RELATION_PRODUCT-COMPOSE rule on term: "
        << pt_rel << " with explanation: " << exp << std::endl;

    computeMembersForBinOpRel(pt_rel);
    d_rel_nodes.insert(pt_rel);
  }

  Node mem = exp[0];
  std::vector<Node> r1_element;
  std::vector<Node> r2_element;
  const DType& dt1 = pt_rel[0].getType().getSetElementType().getDType();
  unsigned int s1_len =
      pt_rel[0].getType().getSetElementType().getTupleLength();
  unsigned int tup_len = pt_rel.getType().getSetElementType().getTupleLength();

  r1_element.push_back(dt1[0].getConstructor());

  unsigned int i = 0;
  for (; i < s1_len; ++i)
  {
    r1_element.push_back(TupleUtils::nthElementOfTuple(mem, i));
  }
  const DType& dt2 = pt_rel[1].getType().getSetElementType().getDType();
  r2_element.push_back(dt2[0].getConstructor());
  for (; i < tup_len; ++i)
  {
    r2_element.push_back(TupleUtils::nthElementOfTuple(mem, i));
  }
  Node reason = exp;
  Node mem1 = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, r1_element);
  Node mem2 = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, r2_element);
  Node fact_1 = nodeManager()->mkNode(Kind::SET_MEMBER, mem1, pt_rel[0]);
  Node fact_2 = nodeManager()->mkNode(Kind::SET_MEMBER, mem2, pt_rel[1]);

  if (pt_rel != exp[1])
  {
    reason = nodeManager()->mkNode(
        Kind::AND, exp, nodeManager()->mkNode(Kind::EQUAL, pt_rel, exp[1]));
  }
  sendInfer(fact_1, InferenceId::SETS_RELS_PRODUCT_SPLIT, reason);
  sendInfer(fact_2, InferenceId::SETS_RELS_PRODUCT_SPLIT, reason);
}

/* join-split rule:           (a, b) IS_IN (X RELATION_JOIN Y)
 *                  --------------------------------------------
 *                  exists z | (a, z) IS_IN X  && (z, b) IS_IN Y
 *
 *
 * join-compose rule: (a, b) IS_IN X    (b, c) IS_IN Y  NOT (t, u) IS_IN (X
 * RELATION_JOIN Y)
 *                    -------------------------------------------------------------
 *                                      (a, c) IS_IN (X RELATION_JOIN Y)
 */

void TheorySetsRels::applyJoinRule(Node join_rel, Node join_rel_rep, Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_JOIN rule on joined term = "
                      << join_rel << ", its representative = " << join_rel_rep
                      << " with explanation = " << exp << std::endl;
  if (d_rel_nodes.find(join_rel) == d_rel_nodes.end())
  {
    Trace("rels-debug")
        << "\n[Theory::Rels] Apply RELATION_JOIN-COMPOSE rule on term: "
        << join_rel << " with explanation: " << exp << std::endl;

    computeMembersForBinOpRel(join_rel);
    d_rel_nodes.insert(join_rel);
  }

  Node mem = exp[0];
  std::vector<Node> r1_element;
  std::vector<Node> r2_element;
  Node r1_rep = getRepresentative(join_rel[0]);
  Node r2_rep = getRepresentative(join_rel[1]);
  TypeNode shared_type =
      r2_rep.getType().getSetElementType().getTupleTypes()[0];
  Node shared_x = d_skCache.mkTypedSkolemCached(
      shared_type, mem, join_rel, SkolemCache::SK_JOIN, "srj");
  const DType& dt1 = join_rel[0].getType().getSetElementType().getDType();
  unsigned int s1_len =
      join_rel[0].getType().getSetElementType().getTupleLength();
  unsigned int tup_len =
      join_rel.getType().getSetElementType().getTupleLength();

  unsigned int i = 0;
  r1_element.push_back(dt1[0].getConstructor());
  for (; i < s1_len - 1; ++i)
  {
    r1_element.push_back(TupleUtils::nthElementOfTuple(mem, i));
  }
  r1_element.push_back(shared_x);
  const DType& dt2 = join_rel[1].getType().getSetElementType().getDType();
  r2_element.push_back(dt2[0].getConstructor());
  r2_element.push_back(shared_x);
  for (; i < tup_len; ++i)
  {
    r2_element.push_back(TupleUtils::nthElementOfTuple(mem, i));
  }
  Node mem1 = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, r1_element);
  Node mem2 = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, r2_element);

  computeTupleReps(mem1);
  computeTupleReps(mem2);

  std::vector<Node> elements =
      d_membership_trie[r1_rep].findTerms(d_tuple_reps[mem1]);

  for (unsigned int j = 0; j < elements.size(); j++)
  {
    std::vector<Node> new_tup;
    new_tup.push_back(elements[j]);
    new_tup.insert(new_tup.end(),
                   d_tuple_reps[mem2].begin() + 1,
                   d_tuple_reps[mem2].end());
    if (d_membership_trie[r2_rep].existsTerm(new_tup) != Node::null())
    {
      return;
    }
  }
  Node reason = exp;
  if (join_rel != exp[1])
  {
    reason = nodeManager()->mkNode(
        Kind::AND,
        reason,
        nodeManager()->mkNode(Kind::EQUAL, join_rel, exp[1]));
  }
  // join_rel = (rel.join A B)
  // exp      = (set.member (tuple x z) S), S ~ join_rel
  // reason   = (and exp (= join_rel S))
  // k        = shared_x, a fresh element
  // facts    = (set.member (tuple x k) A), (set.member (tuple k z) B)
  if (!options().sets.relsAcyclicHammer)
  {
    Node fact = nodeManager()->mkNode(Kind::SET_MEMBER, mem1, join_rel[0]);
    sendInfer(fact, InferenceId::SETS_RELS_JOIN_SPLIT_1, reason);
    fact = nodeManager()->mkNode(Kind::SET_MEMBER, mem2, join_rel[1]);
    sendInfer(fact, InferenceId::SETS_RELS_JOIN_SPLIT_2, reason);
    // Only needed because shared_x was just asserted into the facts above:
    // under --rels-acyclic-hammer, those facts are never sent, so shared_x is
    // never asserted to be a member of anything and there is nothing to
    // share. Registering it anyway (as this used to do unconditionally) would
    // leave a fresh, permanently-live, totally unconstrained element of
    // shared_type sitting in the equality engine for every unjustified join
    // membership, for no benefit.
    makeSharedTerm(shared_x);
  }
}

void TheorySetsRels::applyTableJoinRule(Node n, Node nRep, Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_TABLE_JOIN rule on joined term = "
                      << n << ", its representative = " << nRep
                      << " with explanation = " << exp << std::endl;
  if (d_rel_nodes.find(n) == d_rel_nodes.end())
  {
    Trace("rels-debug")
        << "\n[Theory::Rels] Apply RELATION_TABLE_JOIN-COMPOSE rule on term: "
        << n << " with explanation: " << exp << std::endl;

    computeMembersForBinOpRel(n);
    d_rel_nodes.insert(n);
  }
  NodeManager* nm = nodeManager();
  Node A = n[0];
  Node B = n[1];
  Node e = exp[0];

  Node repA = getRepresentative(A);
  Node repB = getRepresentative(B);

  TypeNode tupleAType = A.getType().getSetElementType();
  TypeNode tupleBType = B.getType().getSetElementType();
  size_t tupleALength = tupleAType.getTupleLength();
  size_t productTupleLength = n.getType().getSetElementType().getTupleLength();

  std::vector<Node> elements = TupleUtils::getTupleElements(e);
  Node a = TupleUtils::constructTupleFromElements(
      tupleAType, elements, 0, tupleALength - 1);
  Node b = TupleUtils::constructTupleFromElements(
      tupleBType, elements, tupleALength, productTupleLength - 1);

  computeTupleReps(a);
  computeTupleReps(b);

  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();
  Node joinConstraints = d_trueNode;
  for (size_t i = 0; i < indices.size(); i += 2)
  {
    Node x = elements[indices[i]];
    Node y = elements[tupleALength + indices[i + 1]];
    Node equal = x.eqNode(y);
    joinConstraints = joinConstraints.andNode(equal);
  }

  Node fact1 = nm->mkNode(Kind::SET_MEMBER, a, A);
  Node fact2 = nm->mkNode(Kind::SET_MEMBER, b, B);
  Node premise = exp;
  if (n != exp[1])
  {
    premise = premise.andNode(n.eqNode(exp[1]));
  }
  Node conclusion = fact1.andNode(fact2).andNode(joinConstraints);
  sendInfer(conclusion, InferenceId::SETS_RELS_TABLE_JOIN_DOWN, premise);
}

/*
 * transpose-occur rule:    (a, b) IS_IN X   (RELATION_TRANSPOSE X) in T
 *                         ---------------------------------------
 *                            (b, a) IS_IN (RELATION_TRANSPOSE X)
 *
 * transpose-reverse rule:    (a, b) IS_IN (RELATION_TRANSPOSE X)
 *                         ---------------------------------------
 *                            (b, a) IS_IN X
 *
 */
void TheorySetsRels::applyTransposeRule(std::vector<Node> tp_terms)
{
  if (tp_terms.size() < 1)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  for (unsigned int i = 1; i < tp_terms.size(); i++)
  {
    Trace("rels-debug")
        << "\n[Theory::Rels] *********** Applying RELATION_TRANSPOSE-Equal "
           "rule on transposed term = "
        << tp_terms[0] << " and " << tp_terms[i] << std::endl;
    // Use fact to ensure deterministic node ID assignments
    Node fact = nm->mkNode(Kind::EQUAL, tp_terms[0][0], tp_terms[i][0]);
    sendInfer(fact,
              InferenceId::SETS_RELS_TRANSPOSE_EQ,
              nm->mkNode(Kind::EQUAL, tp_terms[0], tp_terms[i]));
  }
}

void TheorySetsRels::applyTransposeRule(Node tp_rel, Node tp_rel_rep, Node exp)
{
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_TRANSPOSE rule on transposed term = "
                      << tp_rel << ", its representative = " << tp_rel_rep
                      << " with explanation = " << exp << std::endl;
  NodeManager* nm = nodeManager();

  if (d_rel_nodes.find(tp_rel) == d_rel_nodes.end())
  {
    Trace("rels-debug")
        << "\n[Theory::Rels] Apply RELATION_TRANSPOSE-Compose rule on term: "
        << tp_rel << " with explanation: " << exp << std::endl;

    computeMembersForUnaryOpRel(tp_rel);
    d_rel_nodes.insert(tp_rel);
  }

  Node reason = exp;
  Node reversed_mem = TupleUtils::reverseTuple(exp[0]);

  if (tp_rel != exp[1])
  {
    reason = nodeManager()->mkNode(
        Kind::AND, reason, nodeManager()->mkNode(Kind::EQUAL, tp_rel, exp[1]));
  }
  sendInfer(nm->mkNode(Kind::SET_MEMBER, reversed_mem, tp_rel[0]),
            InferenceId::SETS_RELS_TRANSPOSE_REV,
            reason);
}

Node TheorySetsRels::cyclicAtom(const std::vector<Node>& rels) const
{
  auto it = d_cycleAtoms.find(rels);
  Assert(it != d_cycleAtoms.end());
  return it->second;
}

Node TheorySetsRels::mkRelUnion(const std::vector<Node>& rels)
{
  Assert(!rels.empty());
  // rels = [R1, ..., Rk]: (set.union (set.union R1 R2) ... Rk), rewritten
  Node u = rels[0];
  for (size_t i = 1, n = rels.size(); i < n; i++)
  {
    u = nodeManager()->mkNode(Kind::SET_UNION, u, rels[i]);
  }
  return rewrite(u);
}

/*
 * RELATION_INST_CYCLE, for an asserted (rel.cyclic R) and fresh s, s1, l:
 *   R not a union:      (rel.cyclic R) => (s, s) in TC(R)
 *   R = R1 U ... U Rk:  (rel.cyclic R) => 1 < l
 * In the second case s1, ..., sl with sl = s1 is the cycle witness, unrolled
 * one element per check by RELATION_UNROLL_CYCLE. Example: (rel.cyclic
 * (rf U po)) has the witness s1 -> s2 -> ... -> sl with each edge in TC(rf)
 * or TC(po).
 */
void TheorySetsRels::applyInstCycleRule(Node atom)
{
  Assert(atom.getKind() == Kind::RELATION_CYCLIC);
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_INST_CYCLE rule on "
                      << atom << std::endl;
  // (rel.cyclic R) holds iff R has a cycle. If R is a union R1 U ... U Rk, a
  // cycle of R is a cycle of the list (R1, ..., Rk); the witness below is
  // built over the operands, which gives it its alternating structure. The
  // operands are the d_cycle_sequences key, and the atom is the reason of
  // every lemma about the witness.
  // atom = (rel.cyclic R)
  // rels = the operands of the nested unions of R, e.g. [rf, po, co] for
  //        (set.union rf (set.union po co)), or [R] if R is not a union
  std::vector<Node> rels;
  if (options().sets.relsCycleFlattenTop
      && atom[0].getKind() == Kind::SET_UNION)
  {
    // PROTOTYPE: only the top-level union, e.g. [ppo, com] for
    // (set.union ppo com) even if ppo is itself a union
    rels.push_back(atom[0][0]);
    rels.push_back(atom[0][1]);
  }
  else if (options().sets.relsCycleFlattenKeepTc
           && atom[0].getKind() == Kind::SET_UNION)
  {
    // PROTOTYPE: flatten, but keep a nested union X whose closure TC(X) is a
    // term (e.g. ppo, used as ppo+ by other constraints) as one operand, so
    // that the witness edges are in that very closure
    std::vector<Node> todo{atom[0][1], atom[0][0]};
    while (!todo.empty())
    {
      Node r = todo.back();
      todo.pop_back();
      Node tc = nodeManager()->mkNode(Kind::RELATION_TCLOSURE, r);
      if (r.getKind() == Kind::SET_UNION && !d_state.hasTerm(tc))
      {
        todo.push_back(r[1]);
        todo.push_back(r[0]);
      }
      else if (r.getKind() == Kind::RELATION_JOIN
               && r[0].getKind() == Kind::SET_UNION && !d_state.hasTerm(tc))
      {
        // (A U B);C = A;C U B;C: the closure of each part is simpler, e.g.
        // (rfe U fr U co);sm gives rfe;sm, fr;sm and co;sm
        NodeManager* nm = nodeManager();
        todo.push_back(nm->mkNode(Kind::RELATION_JOIN, r[0][1], r[1]));
        todo.push_back(nm->mkNode(Kind::RELATION_JOIN, r[0][0], r[1]));
      }
      else
      {
        rels.push_back(r);
      }
    }
  }
  else
  {
    collectUnionOperands(atom[0], rels);
  }
  auto ins = d_cycleAtoms.emplace(rels, atom);
  if (ins.first->second != atom)
  {
    // Another atom has the same operands, with the unions nested differently
    // (e.g. A U (B U C) and (A U B) U C). The two unions are equal, so the two
    // atoms are equivalent. The witness of these operands is built for the
    // first atom, which is the reason of its lemmas; reduce this atom to it.
    // conc  = (rel.cyclic R0), the first atom with these operands
    // lemma: atom => conc
    Node conc = ins.first->second;
    Trace("rels-cycles") << "CyclicSameOperands: " << conc << " from " << atom
                         << std::endl;
    sendInfer(conc, InferenceId::SETS_RELS_INST_CYCLE, atom);
    return;
  }
  Node exp = cyclicAtom(rels);
  if (d_cycle_sequences.find(rels) != d_cycle_sequences.end())
  {
    return;
  }

  NodeManager* nm = nodeManager();

  if (rels.size() == 1)
  {
    // RELATION_CYCLIC (definition): (rel.cyclic R) iff some (s,s) IN TC(R).
    // For a relation that is not a union, the definition is applied directly:
    // a fresh s with (s,s) IN TC(R); the closure rules do the rest. The
    // anchor rules still apply to it (doCycleInference).
    if (d_selfLoops.find(rels) != d_selfLoops.end())
    {
      return;
    }
    Node rel = rels[0];
    TypeNode tt = rel.getType().getSetElementType();
    TypeNode elementType = tt.getTupleTypes()[0];
    Node s1 = d_skCache.mkTypedSkolemCached(elementType,
                                            rel,
                                            nm->mkConstInt(Rational(1)),
                                            SkolemCache::SK_CYCLE_ELEM,
                                            "cyc");
    // loop = (tuple s1 s1)
    // conc = (set.member (tuple s1 s1) (rel.tclosure R)), reason = atom
    Node loop = TupleUtils::constructTupleFromElements(tt, {s1, s1}, 0, 1);
    Node conc = nm->mkNode(
        Kind::SET_MEMBER, loop, nm->mkNode(Kind::RELATION_TCLOSURE, rel));
    d_selfLoops[rels] = s1;
    Trace("rels-cycles") << "SelfLoop: exp = " << exp << ", conc = " << conc
                         << std::endl;
    sendInfer(conc, InferenceId::SETS_RELS_ACYCLIC_SELF_LOOP, exp);
    // A self-loop witness is complete: its only edge is (s1, s1), so the
    // branching anchor lemma can be sent at once (it has one disjunct).
    applyAcyclicAnchorRules(rels, {s1, s1}, exp, 2);
    return;
  }

  // Key both skolems on the cyclic relation. s1 is the first element of the
  // cycle.
  // relUnion = (set.union R1 ... Rk): only the cache key of the skolems s1 (an
  //            element) and l (an Int)
  Node relUnion = mkRelUnion(rels);
  TypeNode elementType =
      relUnion.getType().getSetElementType().getTupleTypes()[0];
  Node s1 = d_skCache.mkTypedSkolemCached(elementType,
                                          relUnion,
                                          nm->mkConstInt(Rational(1)),
                                          SkolemCache::SK_CYCLE_ELEM,
                                          "cyc");
  // l is the symbolic eventual length of the cycle. Register l as a
  // shared term so that checkAcyclicityLastCall can query its model value.
  Node l = d_skCache.mkTypedSkolemCached(
      nm->integerType(), relUnion, SkolemCache::SK_CYCLE_LEN, "cyclen");
  makeSharedTerm(l);
  if (options().sets.relsCycleLenDecide)
  {
    // PROTOTYPE (--rels-cycle-len-decide-bound): decide l <= k only up to one
    // more than the number of unrolled elements. Otherwise, when every
    // decision l <= k is refuted during propagation, the strategy decides
    // l <= k + 1, l <= k + 2, ... forever and the full-effort check, which
    // unrolls the witness, is never reached.
    std::function<size_t()> maxLen;
    if (options().sets.relsCycleLenDecideBound)
    {
      maxLen = [this, rels]() {
        size_t n = 1;
        auto it = d_cycle_sequences.find(rels);
        if (it != d_cycle_sequences.end())
        {
          n = std::max(n, (*it).second.first.size());
        }
        auto pit = d_cyclePrefixes.find(rels);
        if (pit != d_cyclePrefixes.end())
        {
          n = std::max(n, (*pit).second.size());
        }
        return n + 1;
      };
    }
    d_cycleLenStrategies.emplace_back(
        new CycleLenDecisionStrategy(d_env, d_state.getValuation(), l, maxLen));
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_SETS_CYCLE_LEN,
        d_cycleLenStrategies.back().get(),
        DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
  }

  // PROTOTYPE (--rels-cycle-keep-prefix): restart from the longest prefix
  // unrolled so far; its elements are the same cached skolems and its lemmas
  // are permanent.
  std::vector<Node> start{s1};
  if (options().sets.relsCycleKeepPrefix)
  {
    auto pit = d_cyclePrefixes.find(rels);
    if (pit != d_cyclePrefixes.end())
    {
      start = pit->second;
    }
  }
  d_cycle_sequences.insert(rels, std::make_pair(start, l));

  // conc = (< 1 l), reason = atom
  Node conc = nm->mkNode(Kind::LT, nm->mkConstInt(Rational(1)), l);

  Trace("rels-cycles") << "InstCycleRule: exp = " << exp << ", conc = " << conc
                       << std::endl;

  sendInfer(conc, InferenceId::SETS_RELS_INST_CYCLE, exp);

  if (options().sets.relsCycleDefUnion)
  {
    // PROTOTYPE: the definition of rel.cyclic for the union itself, on the
    // first element of the witness:
    // conc = (set.member (tuple s1 s1) (rel.tclosure R)), R = exp[0]
    Node rel = exp[0];
    TypeNode tt = rel.getType().getSetElementType();
    Node loop = TupleUtils::constructTupleFromElements(tt, {s1, s1}, 0, 1);
    Node def = nm->mkNode(
        Kind::SET_MEMBER, loop, nm->mkNode(Kind::RELATION_TCLOSURE, rel));
    sendInfer(def, InferenceId::SETS_RELS_ACYCLIC_SELF_LOOP, exp);
  }
}

/*
 * RELATION_SPLIT_CYCLE_LEN, for the witness s1, ..., s_cnt of (rel.cyclic R):
 *   (rel.cyclic R) /\ cnt <= l  =>  cnt < l \/ (l = cnt /\ s_cnt = s1)
 * e.g. for cnt = 3: the witness has more elements, or it is s1 -> s2 -> s1.
 */
void TheorySetsRels::applySplitCycleLenRule(const std::vector<Node>& rels,
                                            const std::vector<Node>& s,
                                            Node l)
{
  size_t cnt = s.size();
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_SPLIT_CYCLE_LEN rule, cnt = "
                      << cnt << ", l = " << l << std::endl;

  NodeManager* nm = nodeManager();

  Node cnt_node = nm->mkConstInt(Rational(cnt));

  // case_1 = (< cnt l)
  // case_2 = (and (= cnt l) (= s1 s_cnt))
  // conc   = (or case_1 case_2)
  // exp    = (and (rel.cyclic R) (>= l cnt))
  Node case_1 = nm->mkNode(Kind::LT, cnt_node, l);

  Node case_2 = nm->mkNode(Kind::AND,
                           nm->mkNode(Kind::EQUAL, cnt_node, l),
                           nm->mkNode(Kind::EQUAL, s[0], s.back()));

  Node conc = nm->mkNode(Kind::OR, case_1, case_2);

  Node l_geq_cnt = nm->mkNode(Kind::GEQ, l, cnt_node);
  Node exp = nm->mkNode(Kind::AND, cyclicAtom(rels), l_geq_cnt);

  Trace("rels-cycles") << "SplitCycleLen: " << conc << std::endl;

  sendInfer(conc, InferenceId::SETS_RELS_SPLIT_CYCLE_LEN, exp);
}

/*
 * RELATION_UNROLL_CYCLE, for the witness s1, ..., s_cnt of
 * (rel.cyclic (R1 U ... U Rk)) and a fresh s_{cnt+1}:
 *   (rel.cyclic R) /\ cnt < l  =>
 *     (s_cnt, s_{cnt+1}) in TC(R1) \/ ... \/ (s_cnt, s_{cnt+1}) in TC(Rk)
 * The extended witness replaces the old one in d_cycle_sequences, which is
 * context-dependent.
 */
std::vector<Node> TheorySetsRels::applyUnrollCycle(
    const std::vector<Node>& rels, const std::vector<Node>& s, Node l)
{
  Assert(0 < rels.size());
  Assert(!s.empty());

  NodeManager* nm = nodeManager();
  size_t cnt = s.size();
  // exp = (< cnt l): the witness has an element after s_cnt
  Node exp = nm->mkNode(Kind::LT, nm->mkConstInt(Rational(cnt)), l);

  // Create a new cycle element, keyed on the cycle relation and its position.
  Node relUnion = mkRelUnion(rels);
  TypeNode elementType =
      relUnion.getType().getSetElementType().getTupleTypes()[0];
  Node newElem =
      d_skCache.mkTypedSkolemCached(elementType,
                                    relUnion,
                                    nm->mkConstInt(Rational(cnt + 1)),
                                    SkolemCache::SK_CYCLE_ELEM,
                                    "cyc");
  Node sPrev = s.back();

  std::vector<Node> disjs;
  for (const Node& Ri : rels)
  {
    TypeNode tt = Ri.getType().getSetElementType();
    // tup      = (tuple s_cnt s_cnt+1)
    // Ri_tclos = (rel.tclosure Ri)
    Node tup =
        TupleUtils::constructTupleFromElements(tt, {sPrev, newElem}, 0, 1);
    // PROTOTYPE (--rels-cycle-plain-edges): edges in Ri itself
    Node Ri_tclos = options().sets.relsCyclePlainEdges
                        ? Ri
                        : nm->mkNode(Kind::RELATION_TCLOSURE, Ri);
    disjs.push_back(nm->mkNode(Kind::SET_MEMBER, tup, Ri_tclos));
  }

  // disj = (or (set.member tup (rel.tclosure R1))
  //            ...
  //            (set.member tup (rel.tclosure Rk)))
  Node disj = disjs.size() == 1 ? disjs[0] : nm->mkNode(Kind::OR, disjs);

  Trace("rels-cycles") << "UnrollCycle: exp = " << exp << ", disj = " << disj
                       << std::endl;

  sendInfer(disj, InferenceId::SETS_RELS_UNROLL_CYCLE, exp);

  // Minimality: the witness is a shortest cycle of the graph
  // TC(R1) U ... U TC(Rk). Two consecutive edges of such a cycle never lie in
  // the same TC(Ri): by transitivity of TC(Ri) they could be replaced by a
  // single edge, giving a shorter cycle (a 2-edge cycle would become a
  // self-loop). Hence, for the new edge e = (s_cnt, s_{cnt+1}):
  //  (a) e and the previous edge (s_{cnt-1}, s_cnt) are not both in TC(Ri),
  //      whenever the new element belongs to the cycle (cnt < l);
  //  (b) if the cycle closes at the new element (l = cnt + 1, so
  //      s_{cnt+1} = s_1), e and the first edge (s_1, s_2) are not both in
  //      TC(Ri).
  // ContrMinimal implies these constraints only indirectly (via a chord that
  // the transitive-closure rules first have to infer); stating them here
  // prunes the choice of the relation of every unrolled edge immediately.
  // with plain edges, consecutive edges may lie in the same operand
  if (cnt >= 2 && !options().sets.relsCyclePlainEdges)
  {
    Node acyc = cyclicAtom(rels);
    // reasonA = (and (rel.cyclic R) (< cnt l))
    // reasonB = (and (rel.cyclic R) (= l cnt+1))
    Node reasonA = nm->mkNode(Kind::AND, acyc, exp);
    Node reasonB = nm->mkNode(
        Kind::AND,
        acyc,
        nm->mkNode(Kind::EQUAL, l, nm->mkConstInt(Rational(cnt + 1))));
    for (const Node& Ri : rels)
    {
      TypeNode tt = Ri.getType().getSetElementType();
      Node Ri_tclos = nm->mkNode(Kind::RELATION_TCLOSURE, Ri);
      Node newEdge = nm->mkNode(
          Kind::SET_MEMBER,
          TupleUtils::constructTupleFromElements(tt, {sPrev, newElem}, 0, 1),
          Ri_tclos);
      Node prevEdge = nm->mkNode(
          Kind::SET_MEMBER,
          TupleUtils::constructTupleFromElements(tt, {s[cnt - 2], sPrev}, 0, 1),
          Ri_tclos);
      Node firstEdge = nm->mkNode(
          Kind::SET_MEMBER,
          TupleUtils::constructTupleFromElements(tt, {s[0], s[1]}, 0, 1),
          Ri_tclos);
      // newEdge   = (set.member (tuple s_cnt s_cnt+1) (rel.tclosure Ri))
      // prevEdge  = (set.member (tuple s_cnt-1 s_cnt) (rel.tclosure Ri))
      // firstEdge = (set.member (tuple s1 s2) (rel.tclosure Ri))
      // lemmas: reasonA => (not (and prevEdge newEdge))
      //         reasonB => (not (and newEdge firstEdge))
      sendInfer(nm->mkNode(Kind::AND, prevEdge, newEdge).negate(),
                InferenceId::SETS_RELS_CONTR_MINIMAL,
                reasonA);
      sendInfer(nm->mkNode(Kind::AND, newEdge, firstEdge).negate(),
                InferenceId::SETS_RELS_CONTR_MINIMAL,
                reasonB);
    }
  }

  std::vector<Node> sNew = s;
  sNew.push_back(newElem);
  d_cycle_sequences.insert(rels, std::make_pair(sNew, l));
  if (options().sets.relsCycleKeepPrefix)
  {
    auto pit = d_cyclePrefixes.find(rels);
    if (pit == d_cyclePrefixes.end() || pit->second.size() < sNew.size())
    {
      d_cyclePrefixes[rels] = sNew;
    }
  }
  return sNew;
}

/*
 * RELATION_CONTR_MINIMAL: the witness s1, ..., s_cnt of (rel.cyclic (R1 U ...
 * U Rk)), of length l with s_l = s1 (l - 1 edges), is a shortest cycle of
 * TC(R1) U ... U TC(Rk). For 1 <= q < r <= cnt, r <= l, and every Rb:
 *   I   no chord:          (s_q, s_r) not in TC(Rb)   if q < r - 1 and
 *                                                     (q, r) != (1, l)
 *   II  distinct elements: s_q != s_r                 if (q, r) != (1, l)
 *   III no backward edge closing a shorter cycle (--rels-acyclic-backward-
 *       chords):           (s_r, s_q) not in TC(Rb)   if r < l and
 *                          r - q + 1 < l - 1, or r = l >= 3 and q != 2
 * Example: for the witness s1 -> s2 -> s3 -> s4 = s1 (l = 4), I gives
 * (s1, s3) not in TC(Rb), and III gives (s3, s2) not in TC(Rb): the cycle
 * s2 -> s3 -> s2 would have 2 edges instead of 3. Backward edges let a
 * totality axiom on one relation (e.g. program order within a thread) bound
 * the length of the witness: two elements it relates must be adjacent. They
 * are optional because they slow down finite model finding.
 */
void TheorySetsRels::applyContrMinimalRule(const std::vector<Node>& rels,
                                           const std::vector<Node>& s,
                                           Node l,
                                           Node exp)
{
  size_t cnt = s.size();
  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "RELATION_CONTR_MINIMAL rule, cnt = "
                      << cnt << ", l = " << l << ", exp = " << exp << std::endl;
  // the smallest usable case is the pair (s_1, s_2)
  if (cnt < 2) return;
  NodeManager* nm = nodeManager();
  bool backward = options().sets.relsAcyclicBackwardChords;

  for (const Node& Ri : rels)
  {
    TypeNode tt = Ri.getType().getSetElementType();
    // Ri_tc = (rel.tclosure Ri); exp = (rel.cyclic R)
    // with plain edges the witness is a shortest cycle of the union, so a
    // chord is an edge of Ri itself
    Node Ri_tc = options().sets.relsCyclePlainEdges
                     ? Ri
                     : nm->mkNode(Kind::RELATION_TCLOSURE, Ri);
    for (size_t r = 2; r <= cnt; ++r)
    {
      Node sr = s[r - 1];  // Adjust for 0-based indexing
      // s_r is an element of the cycle only if r <= l
      Node r_leq_l = nm->mkNode(Kind::LEQ, nm->mkConstInt(Rational(r)), l);
      // reason             = (and (rel.cyclic R) (<= r l))
      // reason_not_closing = (and reason (not (= r l)))
      Node reason = nm->mkNode(Kind::AND, exp, r_leq_l);
      // (s_1, s_r) is the closing pair of the cycle when r = l
      Node r_neq_l =
          nm->mkNode(Kind::EQUAL, nm->mkConstInt(Rational(r)), l).notNode();
      Node reason_not_closing = nm->mkNode(Kind::AND, reason, r_neq_l);
      if (options().sets.relsCycleLtPremise)
      {
        // PROTOTYPE (--rels-cycle-lt-premise): the same premise as
        // (and (rel.cyclic R) (< r l)). Its atom (>= l r+1) is a bound, which
        // arithmetic propagates from a lower bound on l at once; the equality
        // atom (= r l) is falsified only once l equals a constant.
        reason_not_closing =
            nm->mkNode(Kind::AND,
                       exp,
                       nm->mkNode(Kind::LT, nm->mkConstInt(Rational(r)), l));
      }
      for (size_t q = 1; q < r; ++q)
      {
        Node sq = s[q - 1];  // Adjust for 0-based indexing
        Node reason_pair = q == 1 ? reason_not_closing : reason;
        // II: s_q and s_r are distinct, except for the closing pair
        // conc_diseq = (not (= s_q s_r))
        Node conc_diseq = nm->mkNode(Kind::EQUAL, sq, sr).notNode();
        sendInfer(
            conc_diseq, InferenceId::SETS_RELS_CONTR_MINIMAL, reason_pair);
        if (backward)
        {
          // III: no backward edge (s_r, s_q) that closes a shorter cycle
          Node bwd = TupleUtils::constructTupleFromElements(tt, {sr, sq}, 0, 1);
          // conc_bwd = (not (set.member (tuple s_r s_q) (rel.tclosure Ri)))
          Node conc_bwd = nm->mkNode(Kind::SET_MEMBER, bwd, Ri_tc).notNode();
          std::vector<Node> bwd_reasons;
          if (q >= 3)
          {
            // r < l: r - q + 1 < l - 1 follows from r + 1 <= l; r = l: the
            // edge (s_1, s_q) closes a cycle of l - q + 1 < l - 1 edges;
            // together r <= l
            bwd_reasons.push_back(reason);
          }
          else if (q == 2)
          {
            // r < l as above; for r = l the edge is the first edge itself
            bwd_reasons.push_back(nm->mkNode(
                Kind::AND,
                exp,
                nm->mkNode(Kind::LEQ, nm->mkConstInt(Rational(r + 1)), l)));
          }
          else
          {
            // q = 1, r < l: the sub-cycle s_1, ..., s_r, s_1 has r edges,
            // shorter iff r + 2 <= l; r = l: a self-loop of s_1, shorter iff
            // l >= 3
            bwd_reasons.push_back(nm->mkNode(
                Kind::AND,
                exp,
                nm->mkNode(Kind::LEQ, nm->mkConstInt(Rational(r + 2)), l)));
            if (r >= 3)
            {
              bwd_reasons.push_back(nm->mkNode(
                  Kind::AND,
                  exp,
                  nm->mkNode(Kind::EQUAL, l, nm->mkConstInt(Rational(r)))));
            }
          }
          for (const Node& br : bwd_reasons)
          {
            sendInfer(conc_bwd, InferenceId::SETS_RELS_CONTR_MINIMAL, br);
            Trace("rels-cycles") << "ContrMinimal: exp = " << br
                                 << ", conc = " << conc_bwd << std::endl;
          }
        }
        if (q + 2 > r)
        {
          // adjacent: (s_q, s_r) is an edge of the witness, not a chord
          continue;
        }
        // I: no forward chord (s_q, s_r) between non-adjacent elements
        // conc = (not (set.member (tuple s_q s_r) (rel.tclosure Ri)))
        Node tup = TupleUtils::constructTupleFromElements(tt, {sq, sr}, 0, 1);
        Node mem = nm->mkNode(Kind::SET_MEMBER, tup, Ri_tc);
        Node conc = mem.notNode();
        sendInfer(conc, InferenceId::SETS_RELS_CONTR_MINIMAL, reason);
        Trace("rels-cycles") << "ContrMinimal: exp = " << reason
                             << ", conc = " << conc << std::endl;
      }
    }
  }
}

/*
 * RELATION_ACYCLIC_DOWN:
 *   (a, b) IS_IN RELATION_TCLOSURE(x)    NOT RELATION_CYCLIC(x)
 *   ----------------------------------------------------------
 *                            a != b
 */
void TheorySetsRels::applyAcyclicDownRule(Node mem_rep,
                                          Node tc_rel,
                                          Node exp_tc)
{
  // mem_rep = (tuple a b) (representatives)
  // tc_rel  = (rel.tclosure R)
  // exp_tc  = (set.member (tuple a' b') S), S ~ tc_rel
  Node tc_rel0_rep = getRepresentative(tc_rel[0]);

  Trace("rels-debug") << "\n[Theory::Rels] *********** Applying "
                         "ACYCLIC_DOWN rule on member"
                      << mem_rep << ", transitively closed term = " << tc_rel
                      << " and its representative = " << tc_rel0_rep
                      << ", with explanation = " << exp_tc << std::endl;
  // Step 1: find rep of the transitively closed relation in d_acyclic_cache
  // This means that some relation in the equivalence class of tc_rel[0] is
  // acyclic, meaning tc_rel[0] is also acyclic
  if (d_acyclic_cache.find(tc_rel0_rep) == d_acyclic_cache.end())
  {
    return;
  }

  // Pick any acyclic relation in our equivalence class of tc_rel[0] as the
  // reason for the acyclicity of the transitively closed relation
  // exp_acyc = (not (rel.cyclic u)), u ~ R (the vectors of d_acyclic_cache are
  //            never empty), so exp_acyc[0][0] = u
  Node exp_acyc = d_acyclic_cache[tc_rel0_rep][0];

  NodeManager* nm = nodeManager();

  // The reason: the membership, the acyclicity constraint, and the equalities
  // relating the closure of the membership to tc_rel and the relation of the
  // constraint to tc_rel[0]. exp_acyc is the literal (not (rel.cyclic u)).
  std::vector<Node> reasons{exp_tc, exp_acyc};
  if (tc_rel != exp_tc[1])
    reasons.push_back(nm->mkNode(Kind::EQUAL, tc_rel, exp_tc[1]));
  Node u = exp_acyc[0][0];
  if (u != tc_rel[0]) reasons.push_back(nm->mkNode(Kind::EQUAL, u, tc_rel[0]));
  Node reason =
      reasons.size() == 1 ? reasons[0] : nm->mkNode(Kind::AND, reasons);

  // SOUNDNESS: the conclusion must be stated on the tuple that actually
  // occurs in the explanation exp_tc[0], not on mem_rep. mem_rep is only the
  // current *representative* of that tuple; it may be a syntactically
  // different tuple that is equal to exp_tc[0] merely in the current SAT
  // context (e.g. while finite model finding has merged atoms). Since the
  // inference is added as a context-independent lemma, concluding on mem_rep
  // yields lemmas such as ((w1,w2) in TC(po) /\ acyclic(po)) => w1' != w2' for
  // unrelated w1', w2' (or even => false), which wrongly refutes valid models.
  // conc   = (not (= a' b'))
  // reason = (and exp_tc exp_acyc (= tc_rel S) (= u R)), the equalities only
  //          if the terms differ
  Node tup = exp_tc[0];
  Node tup0 = TupleUtils::nthElementOfTuple(tup, 0);
  Node tup1 = TupleUtils::nthElementOfTuple(tup, 1);

  sendInfer(nm->mkNode(Kind::NOT, nm->mkNode(Kind::EQUAL, tup0, tup1)),
            InferenceId::SETS_RELS_ACYCLIC_DOWN,
            reason);
}

void TheorySetsRels::restoreCyclePrefix(const std::vector<Node>& rels,
                                        std::vector<Node>& s,
                                        Node l)
{
  // PROTOTYPE (--rels-cycle-keep-prefix): after backtracking, the witness of
  // the current context may be shorter than the longest prefix unrolled so
  // far. The elements of that prefix are the same cached skolems and their
  // lemmas are permanent, so continue from it.
  if (!options().sets.relsCycleKeepPrefix)
  {
    return;
  }
  auto pit = d_cyclePrefixes.find(rels);
  if (pit != d_cyclePrefixes.end() && pit->second.size() > s.size())
  {
    s = pit->second;
    d_cycle_sequences.insert(rels, std::make_pair(s, l));
  }
}

void TheorySetsRels::doCycleInference()
{
  // Self-loop witnesses: only the anchor rules apply, and they are re-applied
  // every round because positive acyclicity constraints may appear later.
  // sl = ([R], s): the self-loop witness (tuple s s) of (rel.cyclic R)
  for (const auto& sl : d_selfLoops)
  {
    Node acyc_exp = cyclicAtom(sl.first);
    // complete witnesses, see applyInstCycleRule
    applyAcyclicAnchorRules(sl.first, {sl.second, sl.second}, acyc_exp, 2);
  }
  CYC_IT c_it = d_cycle_sequences.begin();
  while (c_it != d_cycle_sequences.end())
  {
    // rels = [R1, ..., Rk], s = [s1, ..., s_cnt], l = the length of the witness
    std::vector<Node> rels = c_it->first;
    std::vector<Node> s = c_it->second.first;
    Node l = c_it->second.second;
    restoreCyclePrefix(rels, s, l);
    if (options().sets.relsCycleUnrollGuard && s.size() >= 2)
    {
      // PROTOTYPE: ltc = (< cnt l), the atom of SplitCycleLen for s_cnt. If
      // it is false in the current assignment, the witness is complete in
      // this branch: do not unroll it (the last call completes it to the
      // value of l if needed).
      Node ltc = rewrite(nodeManager()->mkNode(
          Kind::LT, nodeManager()->mkConstInt(Rational(s.size())), l));
      bool pol = true;
      if (ltc.getKind() == Kind::NOT)
      {
        ltc = ltc[0];
        pol = false;
      }
      bool val;
      if (d_state.hasSatValue(ltc, val) && val != pol)
      {
        ++c_it;
        continue;
      }
    }
    Node acyc_exp = cyclicAtom(rels);
    // applyUnrollCycle returns the extended vector with the newly-created
    // element appended.
    s = applyUnrollCycle(rels, s, l);
    applySplitCycleLenRule(rels, s, l);
    // Minimality: forbid shortcut edges in the cycle.
    applyContrMinimalRule(rels, s, l, acyc_exp);
    applyAcyclicAnchorRules(rels, s, acyc_exp);
    ++c_it;
  }
}

void TheorySetsRels::collectUnionOperands(Node r, std::vector<Node>& parts)
{
  // r = (set.union r[0] r[1]): both operands are flattened, e.g.
  //     (set.union A (set.union B C)) gives [A, B, C]
  if (r.getKind() == Kind::SET_UNION)
  {
    collectUnionOperands(r[0], parts);
    collectUnionOperands(r[1], parts);
    return;
  }
  parts.push_back(r);
}

bool TheorySetsRels::isSyntacticallyInTC(Node x, Node s)
{
  // x is included in TC(s) for every interpretation if
  //   x = s, or x = TC(y) with y included,
  //   x = inter(y, z) with y or z included,
  //   x = minus(y, z) with y included,
  //   x = union(y, z) with y and z included,
  //   x = join(y, z) with y and z included (TC(s) is transitive), or with one
  //     of them of the form iden(w) and the other included (iden(w);y and
  //     y;iden(w) are subsets of y).
  if (x == s)
  {
    return true;
  }
  switch (x.getKind())
  {
    case Kind::RELATION_TCLOSURE: return isSyntacticallyInTC(x[0], s);
    case Kind::SET_INTER:
      return isSyntacticallyInTC(x[0], s) || isSyntacticallyInTC(x[1], s);
    case Kind::SET_MINUS: return isSyntacticallyInTC(x[0], s);
    case Kind::SET_UNION:
      return isSyntacticallyInTC(x[0], s) && isSyntacticallyInTC(x[1], s);
    case Kind::RELATION_JOIN:
    {
      bool l = isSyntacticallyInTC(x[0], s);
      bool r = isSyntacticallyInTC(x[1], s);
      if (l && r)
      {
        return true;
      }
      if (l && x[1].getKind() == Kind::RELATION_IDEN) return true;
      if (r && x[0].getKind() == Kind::RELATION_IDEN) return true;
      return false;
    }
    default: return false;
  }
}

/*
 * Anchor rules, for an asserted (rel.cyclic R) with witness s and every
 * asserted (not (rel.cyclic S)): a cycle of R whose edges all lie in TC(S)
 * would be a cycle of S, so some edge of the cycle is not in TC(S).
 *  INCLUSION:  (rel.cyclic R) /\ (not (rel.cyclic S)) =>
 *                t in R' /\ t not in TC(S)
 *    for a fresh pair t, where R' is the union of the operands of R that are
 *    not syntactically in TC(S); if there is none, the lemma is false.
 *    Example: (rel.cyclic (rf U po)), (not (rel.cyclic po)) give t in rf and
 *    t not in TC(po).
 *  BRANCH:     (rel.cyclic R) /\ (not (rel.cyclic S)) /\ l = N =>
 *                (s1, s2) not in TC(S) \/ ... \/ (s_{N-1}, s_N) not in TC(S)
 *    sent at last call, when the candidate model gives l = N, so that the
 *    listed edges are the whole cycle (s_N = s1); at once for a self-loop.
 */
void TheorySetsRels::applyAcyclicAnchorRules(const std::vector<Node>& rels,
                                             const std::vector<Node>& s,
                                             Node acyc_exp,
                                             int64_t concreteLen,
                                             Node lenEq)
{
  NodeManager* nm = nodeManager();
  options::RelsAcyclicAnchorMode mode = options().sets.relsAcyclicAnchor;
  bool doIncl = mode == options::RelsAcyclicAnchorMode::INCLUSION
                || mode == options::RelsAcyclicAnchorMode::BOTH;
  bool doBranch = mode == options::RelsAcyclicAnchorMode::BRANCH
                  || mode == options::RelsAcyclicAnchorMode::BOTH;
  if (mode == options::RelsAcyclicAnchorMode::NONE)
  {
    return;
  }
  // relUnion = R = (set.union R1 ... Rk), the relation of the witness s
  // acyc_exp = (rel.cyclic R'), R' with the operands rels
  Node relUnion = mkRelUnion(rels);
  TypeNode tt = relUnion.getType().getSetElementType();
  // Collect the applicable acyclicity constraints. The lemmas are sent in
  // this order: first for the S that are themselves operands of the witness's
  // relation, earliest operand first, so that the edges that must leave TC(S)
  // are those of the other operands (e.g. an rf edge leaving po+).
  std::vector<Node> positives;
  for (const auto& entry : d_acyclic_cache)
  {
    for (const Node& acyc : entry.second)
    {
      // acyc = (not (rel.cyclic S)): acyc[0] = (rel.cyclic S), acyc[0][0] = S
      Node sUnion = acyc[0][0];
      if (sUnion.getType() != relUnion.getType() || sUnion == relUnion)
      {
        continue;
      }
      positives.push_back(acyc);
    }
  }
  std::stable_sort(
      positives.begin(), positives.end(), [&](const Node& a, const Node& b) {
        auto rank = [&](const Node& ac) {
          Node su = ac[0][0];
          for (size_t i = 0; i < rels.size(); i++)
          {
            if (rels[i] == su) return i;
          }
          return rels.size();
        };
        return rank(a) < rank(b);
      });
  for (const Node& acyc : positives)
  {
    {
      Node sUnion = acyc[0][0];
      // reason = (and (rel.cyclic R') (not (rel.cyclic S)))
      // tcS    = (rel.tclosure S)
      Node reason = nm->mkNode(Kind::AND, acyc_exp, acyc);
      Node tcS = nm->mkNode(Kind::RELATION_TCLOSURE, sUnion);
      std::pair<Node, Node> key(relUnion, sUnion);
      if (d_anchorInclusionSent.find(key) == d_anchorInclusionSent.end())
      {
        // The witness edge cannot lie in a part of R that is syntactically
        // included in TC(S); restrict it to the remaining parts of R. If
        // every part is included, the two constraints are contradictory: this
        // conflict needs no fresh element and is emitted in every mode. The
        // witness for the remaining parts introduces a fresh tuple and is
        // only emitted in the inclusion modes.
        std::vector<Node> parts;
        collectUnionOperands(relUnion, parts);
        std::vector<Node> rest;
        for (const Node& part : parts)
        {
          if (!isSyntacticallyInTC(part, sUnion))
          {
            rest.push_back(part);
          }
        }
        Node conc;
        if (rest.empty())
        {
          d_anchorInclusionSent.insert(key);
          conc = nm->mkConst(false);
        }
        else if (!doIncl)
        {
          conc = Node::null();
        }
        else
        {
          d_anchorInclusionSent.insert(key);
          // restUnion = the union of the operands of R that are not
          //             syntactically in TC(S)
          // t         = a fresh tuple
          // conc      = (and (set.member t restUnion)
          //                  (not (set.member t (rel.tclosure S))))
          Node restUnion = mkRelUnion(rest);
          Node t = d_skCache.mkTypedSkolemCached(
              tt, relUnion, sUnion, SkolemCache::SK_CYCLE_ELEM, "cycedge");
          conc = nm->mkNode(Kind::AND,
                            nm->mkNode(Kind::SET_MEMBER, t, restUnion),
                            nm->mkNode(Kind::SET_MEMBER, t, tcS).negate());
        }
        if (!conc.isNull())
        {
          Trace("rels-cycles") << "AcyclicAnchor (inclusion): " << conc
                               << " from " << reason << std::endl;
          sendInfer(conc, InferenceId::SETS_RELS_CONTR_MINIMAL, reason);
        }
      }
      // BRANCH: only once the length of the witness is known (concreteLen);
      // the witness may already have been unrolled beyond it. Sent at most
      // once per (R, S) and length, since the length may change between
      // last-call checks.
      if (doBranch && concreteLen >= 2)
      {
        Assert(s.size() >= static_cast<size_t>(concreteLen));
        std::pair<std::pair<Node, Node>, size_t> branchKey(
            key, static_cast<size_t>(concreteLen));
        if (d_anchorBranchSent.find(branchKey) == d_anchorBranchSent.end())
        {
          d_anchorBranchSent.insert(branchKey);
          std::vector<Node> disjuncts;
          for (size_t i = 0; i + 1 < static_cast<size_t>(concreteLen); i++)
          {
            // edge     = (tuple s_i s_i+1)
            // disjunct = (not (set.member edge (rel.tclosure S)))
            Node edge = TupleUtils::constructTupleFromElements(
                tt, {s[i], s[i + 1]}, 0, 1);
            disjuncts.push_back(
                nm->mkNode(Kind::SET_MEMBER, edge, tcS).negate());
          }
          Node conc = disjuncts.size() == 1 ? disjuncts[0]
                                            : nm->mkNode(Kind::OR, disjuncts);
          // With l = concreteLen, the listed edges are the whole cycle
          // (s_l = s_1), so one of them must leave TC(S).
          // branchReason = (and (rel.cyclic R') (not (rel.cyclic S)) (= l N))
          Node branchReason =
              lenEq.isNull() ? reason
                             : nm->mkNode(Kind::AND, acyc_exp, acyc, lenEq);
          Trace("rels-cycles") << "AcyclicAnchor (branch): " << conc << " from "
                               << branchReason << std::endl;
          sendInfer(conc, InferenceId::SETS_RELS_CONTR_MINIMAL, branchReason);
        }
      }
    }
  }
}

bool TheorySetsRels::hasOpenCycleObligation() const
{
  return !d_cycle_sequences.empty();
}

void TheorySetsRels::checkAcyclicityLastCall(Valuation& val)
{
  // Bounds the O(cnt^2) cost of applyContrMinimalRule's shortcut-forbidding
  // loop; a length beyond this is not something we can feasibly catch up on.
  static constexpr size_t MAX_CATCHUP_LEN = 10000;

  NodeManager* nm = nodeManager();
  CYC_IT c_it = d_cycle_sequences.begin();
  while (c_it != d_cycle_sequences.end())
  {
    std::vector<Node> rels = c_it->first;
    std::vector<Node> s = c_it->second.first;
    Node l = c_it->second.second;
    restoreCyclePrefix(rels, s, l);

    // The model's current candidate value for l.
    // lVal = the value of l in the candidate model, e.g. 4
    Node lVal = val.getCandidateModelValue(l);
    bool haveL = !lVal.isNull() && lVal.isConst();
    size_t N = 0;
    if (haveL)
    {
      Integer lInt = lVal.getConst<Rational>().getNumerator();
      haveL = lInt.fitsUnsignedInt() && lInt.toUnsignedInt() <= MAX_CATCHUP_LEN;
      if (haveL)
      {
        N = lInt.toUnsignedInt();
      }
    }

    if (!haveL)
    {
      Trace("rels-debug")
          << "[Theory::Rels] checkAcyclicityLastCall: l = " << l
          << " is not a concrete, practically-sized value; reporting model "
             "unsound"
          << std::endl;
      d_im.setModelUnsound(IncompleteId::SETS_RELS_ACYCLIC_LEN_UNKNOWN);
    }
    else
    {
      // The full-effort check unrolls the witness by one element per round,
      // so the value of l in the candidate model may exceed the number of
      // unrolled elements: complete the witness before the model is accepted.
      Trace("rels-debug") << "[Theory::Rels] checkAcyclicityLastCall: "
                          << "catching up cnt from " << s.size() << " to " << N
                          << " (l = " << l << ")" << std::endl;
      Node acyc_exp = cyclicAtom(rels);
      // Ensure that all cycle-unrolling lemmas have been applied up to the
      // model's current value of l.
      while (s.size() < N)
      {
        s = applyUnrollCycle(rels, s, l);
        applySplitCycleLenRule(rels, s, l);
        applyContrMinimalRule(rels, s, l, acyc_exp);
      }
      // The witness is now unrolled to its length N in the candidate model, so
      // the branching anchor lemma, which needs every edge of the witness, can
      // be sent (see applyAcyclicAnchorRules).
      if (N >= 2)
      {
        // lenEq = (= l N)
        Node lenEq = nm->mkNode(Kind::EQUAL, l, nm->mkConstInt(Rational(N)));
        applyAcyclicAnchorRules(
            rels, s, acyc_exp, static_cast<int64_t>(N), lenEq);
      }
    }
    ++c_it;
  }
}

void TheorySetsRels::doTCInference()
{
  Trace("rels-debug")
      << "[Theory::Rels] ****** Finalizing transitive closure inferences!"
      << std::endl;

  TC_IT tc_graph_it = d_tcr_tcGraph.begin();
  while (tc_graph_it != d_tcr_tcGraph.end())
  {
    Assert(d_tcr_tcGraph_exps.find(tc_graph_it->first)
           != d_tcr_tcGraph_exps.end());
    doTCInference(tc_graph_it->second,
                  d_tcr_tcGraph_exps.find(tc_graph_it->first)->second,
                  tc_graph_it->first);
    ++tc_graph_it;
  }
  Trace("rels-debug") << "[Theory::Rels] ****** Done with finalizing "
                         "transitive closure inferences!"
                      << std::endl;
}

// Bottom-up fashion to compute relations with more than 1 arity
void TheorySetsRels::computeMembersForBinOpRel(Node rel)
{
  Trace("rels-debug")
      << "\n[Theory::Rels] computeMembersForBinOpRel for relation  " << rel
      << std::endl;

  switch (rel[0].getKind())
  {
    case Kind::RELATION_TRANSPOSE:
    case Kind::RELATION_TCLOSURE:
    {
      computeMembersForUnaryOpRel(rel[0]);
      break;
    }
    case Kind::RELATION_JOIN:
    case Kind::RELATION_PRODUCT:
    case Kind::RELATION_TABLE_JOIN:
    {
      computeMembersForBinOpRel(rel[0]);
      break;
    }
    default: break;
  }
  switch (rel[1].getKind())
  {
    case Kind::RELATION_TRANSPOSE:
    {
      computeMembersForUnaryOpRel(rel[1]);
      break;
    }
    case Kind::RELATION_JOIN:
    case Kind::RELATION_PRODUCT:
    case Kind::RELATION_TABLE_JOIN:
    {
      computeMembersForBinOpRel(rel[1]);
      break;
    }
    default: break;
  }
  Kind k = rel.getKind();
  switch (k)
  {
    case Kind::RELATION_JOIN:
    case Kind::RELATION_PRODUCT:
    {
      // PROTOTYPE (--rels-product-lazy, unsat only): no eager composition of
      // product members
      if (k == Kind::RELATION_PRODUCT && options().sets.relsProductLazy)
      {
        break;
      }
      composeMembersForRels(rel);
      break;
    }
    case Kind::RELATION_TABLE_JOIN:
    {
      applyTableJoinUp(rel);
      break;
    }
    default:
      DebugUnhandled() << "No implementation for up rules for kind " << k
                       << std::endl;
  }
}

// Bottom-up fashion to compute unary relation
void TheorySetsRels::computeMembersForUnaryOpRel(Node rel)
{
  Trace("rels-debug")
      << "\n[Theory::Rels] computeMembersForUnaryOpRel for relation  " << rel
      << std::endl;

  switch (rel[0].getKind())
  {
    case Kind::RELATION_TRANSPOSE:
    case Kind::RELATION_TCLOSURE: computeMembersForUnaryOpRel(rel[0]); break;
    case Kind::RELATION_JOIN:
    case Kind::RELATION_PRODUCT:
    case Kind::RELATION_TABLE_JOIN: computeMembersForBinOpRel(rel[0]); break;
    default: break;
  }

  Node rel0_rep = getRepresentative(rel[0]);
  if (d_rReps_memberReps_cache.find(rel0_rep) == d_rReps_memberReps_cache.end())
  {
    return;
  }
  NodeManager* nm = nodeManager();

  const std::vector<Node>& members = d_rReps_memberReps_cache[rel0_rep];
  const std::vector<Node>& exps = d_rReps_memberReps_exp_cache[rel0_rep];

  Assert(members.size() == exps.size());

  if (rel.getKind() == Kind::RELATION_TRANSPOSE)
  {
    for (size_t i = 0, msize = members.size(); i < msize; i++)
    {
      Node reason = exps[i];
      if (rel[0] != exps[i][1])
      {
        reason = nm->mkNode(
            Kind::AND, reason, nm->mkNode(Kind::EQUAL, rel[0], exps[i][1]));
      }
      sendInfer(
          nm->mkNode(
              Kind::SET_MEMBER, TupleUtils::reverseTuple(exps[i][0]), rel),
          InferenceId::SETS_RELS_TRANSPOSE_REV,
          reason);
    }
  }
}

/*
 * Explicitly compose the join or product relations of r1 and r2. For example,
 * consider the case that (a, b) in r1, (c, d) in r2.
 *
 * For RELATION_JOIN, we have three cases:
 *   if b = c, we infer (a, d) in (join r1 r2)
 *   else, we mark b and c as shared terms; their equality will be split in
 *         theory combination if necessary.
 *
 * For RELATION_PRODUCT, we infer (a, b, c, d) in (product r1 r2).
 */
void TheorySetsRels::composeMembersForRels(Node rel)
{
  Trace("rels-debug")
      << "[Theory::Rels] Start composing members for relation = " << rel
      << std::endl;
  Node r1 = rel[0];
  Node r2 = rel[1];
  Node r1_rep = getRepresentative(r1);
  Node r2_rep = getRepresentative(r2);

  if (d_rReps_memberReps_cache.find(r1_rep) == d_rReps_memberReps_cache.end()
      || d_rReps_memberReps_cache.find(r2_rep)
             == d_rReps_memberReps_cache.end())
  {
    return;
  }
  NodeManager* nm = nodeManager();

  std::vector<Node> r1_rep_exps = d_rReps_memberReps_exp_cache[r1_rep];
  std::vector<Node> r2_rep_exps = d_rReps_memberReps_exp_cache[r2_rep];
  size_t r1_tuple_len = r1.getType().getSetElementType().getTupleLength();
  size_t r2_tuple_len = r2.getType().getSetElementType().getTupleLength();

  Kind rk = rel.getKind();
  TypeNode tn = rel.getType().getSetElementType();
  for (unsigned int i = 0; i < r1_rep_exps.size(); i++)
  {
    for (unsigned int j = 0; j < r2_rep_exps.size(); j++)
    {
      std::vector<Node> tuple_elements;
      tuple_elements.push_back(tn.getDType()[0].getConstructor());
      std::vector<Node> reasons;
      if (rk == Kind::RELATION_JOIN)
      {
        Node r1_rmost =
            TupleUtils::nthElementOfTuple(r1_rep_exps[i][0], r1_tuple_len - 1);
        Node r2_lmost = TupleUtils::nthElementOfTuple(r2_rep_exps[j][0], 0);
        // Since we require notification r1_rmost and r2_lmost are equal,
        // they must be shared terms of theory of sets. Hence, we make the
        // following calls to makeSharedTerm to ensure this is the case.
        makeSharedTerm(r1_rmost);
        makeSharedTerm(r2_lmost);

        Trace("rels-debug") << "[Theory::Rels] r1_rmost: " << r1_rmost
                            << " of type " << r1_rmost.getType() << std::endl;
        Trace("rels-debug") << "[Theory::Rels] r2_lmost: " << r2_lmost
                            << " of type " << r2_lmost.getType() << std::endl;
        if (!areEqual(r1_rmost, r2_lmost))
        {
          continue;
        }
        else if (r1_rmost != r2_lmost)
        {
          Trace("rels-debug") << "...equal" << std::endl;
          reasons.push_back(nm->mkNode(Kind::EQUAL, r1_rmost, r2_lmost));
        }
      }

      if (rk == Kind::RELATION_PRODUCT || rk == Kind::RELATION_JOIN)
      {
        bool isProduct = rk == Kind::RELATION_PRODUCT;
        unsigned int k = 0;
        unsigned int l = 1;

        for (; k < r1_tuple_len - 1; ++k)
        {
          tuple_elements.push_back(
              TupleUtils::nthElementOfTuple(r1_rep_exps[i][0], k));
        }
        if (isProduct)
        {
          tuple_elements.push_back(
              TupleUtils::nthElementOfTuple(r1_rep_exps[i][0], k));
          tuple_elements.push_back(
              TupleUtils::nthElementOfTuple(r2_rep_exps[j][0], 0));
        }
        for (; l < r2_tuple_len; ++l)
        {
          tuple_elements.push_back(
              TupleUtils::nthElementOfTuple(r2_rep_exps[j][0], l));
        }

        Node composed_tuple =
            nm->mkNode(Kind::APPLY_CONSTRUCTOR, tuple_elements);
        if (options().sets.relsTcUpSkipKnown)
        {
          // PROTOTYPE: the tuple is already a member of rel in this context
          auto trie = d_membership_trie.find(getRepresentative(rel));
          if (trie != d_membership_trie.end())
          {
            std::vector<Node> elemReps;
            for (size_t e = 1, ne = tuple_elements.size(); e < ne; e++)
            {
              elemReps.push_back(getRepresentative(tuple_elements[e]));
            }
            if (!trie->second.existsTerm(elemReps).isNull())
            {
              reasons.clear();
              continue;
            }
          }
        }
        Node fact = nm->mkNode(Kind::SET_MEMBER, composed_tuple, rel);
        reasons.push_back(r1_rep_exps[i]);
        reasons.push_back(r2_rep_exps[j]);

        if (r1 != r1_rep_exps[i][1])
        {
          reasons.push_back(nm->mkNode(Kind::EQUAL, r1, r1_rep_exps[i][1]));
        }
        if (r2 != r2_rep_exps[j][1])
        {
          reasons.push_back(nm->mkNode(Kind::EQUAL, r2, r2_rep_exps[j][1]));
        }
        if (isProduct)
        {
          sendInfer(fact,
                    InferenceId::SETS_RELS_PRODUCE_COMPOSE,
                    nm->mkNode(Kind::AND, reasons));
        }
        else
        {
          sendInfer(fact,
                    InferenceId::SETS_RELS_JOIN_COMPOSE,
                    nm->mkNode(Kind::AND, reasons));
        }
      }
    }
  }
}

void TheorySetsRels::applyTableJoinUp(Node n)
{
  Assert(n.getKind() == Kind::RELATION_TABLE_JOIN);
  Trace("rels-debug")
      << "[Theory::Rels] Start composing members for relation = " << n
      << std::endl;
  Node a = n[0];
  Node b = n[1];
  Node aRep = getRepresentative(a);
  Node bRep = getRepresentative(b);

  if (d_rReps_memberReps_cache.find(aRep) == d_rReps_memberReps_cache.end()
      || d_rReps_memberReps_cache.find(bRep) == d_rReps_memberReps_cache.end())
  {
    // no members found for a, b
    return;
  }

  NodeManager* nm = nodeManager();

  std::vector<Node> aMemberships = d_rReps_memberReps_exp_cache[aRep];
  std::vector<Node> bMemberships = d_rReps_memberReps_exp_cache[bRep];
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();
  for (unsigned int i = 0; i < aMemberships.size(); i++)
  {
    for (unsigned int j = 0; j < bMemberships.size(); j++)
    {
      Node aConstraint = aMemberships[i];
      Node bConstraint = bMemberships[j];
      Node e1 = aConstraint[0];
      Node e2 = bConstraint[0];
      TypeNode elementType = n.getType().getSetElementType();
      Node tuple = TupleUtils::concatTuples(elementType, e1, e2);
      std::vector<Node> reasons;

      std::vector<Node> aElements = TupleUtils::getTupleElements(e1);
      std::vector<Node> bElements = TupleUtils::getTupleElements(e2);

      // whether e1, e2 have matching join elements
      bool notMatched = false;
      for (size_t k = 0; k < indices.size(); k += 2)
      {
        Node x = aElements[indices[k]];
        Node y = bElements[indices[k + 1]];

        // Since we require notification x and y are equal,
        // they must be shared terms of theory of sets. Hence, we make the
        // following calls to makeSharedTerm to ensure this is the case.
        makeSharedTerm(x);
        makeSharedTerm(y);

        if (!areEqual(x, y))
        {
          notMatched = true;
          break;
        }
        else if (x != y)
        {
          Trace("rels-debug") << "...equal" << std::endl;
          reasons.push_back(nm->mkNode(Kind::EQUAL, x, y));
        }
      }

      if (notMatched)
      {
        continue;
      }

      Node fact = nm->mkNode(Kind::SET_MEMBER, tuple, n);
      reasons.push_back(aConstraint);
      reasons.push_back(bConstraint);
      if (a != aConstraint[1])
      {
        reasons.push_back(nm->mkNode(Kind::EQUAL, a, aConstraint[1]));
      }
      if (b != bConstraint[1])
      {
        reasons.push_back(nm->mkNode(Kind::EQUAL, b, bConstraint[1]));
      }
      sendInfer(fact,
                InferenceId::SETS_RELS_TABLE_JOIN_UP,
                nm->mkNode(Kind::AND, reasons));
    }
  }
}

void TheorySetsRels::processInference(Node conc, InferenceId id, Node exp)
{
  Trace("sets-pinfer") << "Process inference: " << exp << " => " << conc
                       << std::endl;
  if (!d_state.isEntailed(exp, true))
  {
    Trace("sets-pinfer") << "  must assert as lemma" << std::endl;
    // we wrap the spurious explanation into a splitting lemma
    Node lem = nodeManager()->mkNode(Kind::OR, exp.negate(), conc);
    d_im.assertInference(lem, id, d_trueNode, 1);
    return;
  }
  // try to assert it as a fact
  d_im.assertInference(conc, id, exp);
}

bool TheorySetsRels::isRelationKind(Kind k)
{
  return k == Kind::RELATION_TRANSPOSE || k == Kind::RELATION_PRODUCT
         || k == Kind::RELATION_JOIN || k == Kind::RELATION_TABLE_JOIN
         || k == Kind::RELATION_TCLOSURE || k == Kind::RELATION_IDEN
         || k == Kind::RELATION_JOIN_IMAGE || k == Kind::RELATION_CYCLIC
         || k == Kind::RELATION_RCLOSURE || k == Kind::RELATION_RTCLOSURE
         || k == Kind::RELATION_IS_FUNCTIONAL;
}

Node TheorySetsRels::getRepresentative(Node t)
{
  return d_state.getRepresentative(t);
}

bool TheorySetsRels::hasTerm(Node a) { return d_state.hasTerm(a); }
bool TheorySetsRels::areEqual(Node a, Node b)
{
  AssertEqual(a.getType(), b.getType());
  Trace("rels-eq") << "[sets-rels]**** checking equality between " << a
                   << " and " << b << std::endl;
  if (a == b)
  {
    return true;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    return d_state.areEqual(a, b);
  }
  TypeNode atn = a.getType();
  if (atn.isTuple())
  {
    size_t tlen = atn.getTupleLength();
    for (size_t i = 0; i < tlen; i++)
    {
      // Use a_i and b_i to ensure deterministic node ID assignments
      Node a_i = TupleUtils::nthElementOfTuple(a, i);
      Node b_i = TupleUtils::nthElementOfTuple(b, i);
      if (!areEqual(a_i, b_i))
      {
        return false;
      }
    }
    return true;
  }
  else if (!atn.isBoolean())
  {
    makeSharedTerm(a);
    makeSharedTerm(b);
  }
  return false;
}

/*
 * Make sure duplicate members are not added in map
 */
bool TheorySetsRels::safelyAddToMap(std::map<Node, std::vector<Node> >& map,
                                    Node rel_rep,
                                    Node member)
{
  std::map<Node, std::vector<Node> >::iterator mem_it = map.find(rel_rep);
  if (mem_it == map.end())
  {
    std::vector<Node> members;
    members.push_back(member);
    map[rel_rep] = members;
    return true;
  }
  else
  {
    std::vector<Node>::iterator mems = mem_it->second.begin();
    while (mems != mem_it->second.end())
    {
      if (areEqual(*mems, member))
      {
        return false;
      }
      ++mems;
    }
    map[rel_rep].push_back(member);
    return true;
  }
  return false;
}

void TheorySetsRels::makeSharedTerm(Node n)
{
  if (d_shared_terms.find(n) != d_shared_terms.end())
  {
    return;
  }
  Trace("rels-share") << " [sets-rels] making shared term " << n << std::endl;
  // force a proxy lemma to be sent for the singleton containing n
  Node ss = nodeManager()->mkNode(Kind::SET_SINGLETON, n);
  d_treg.getProxy(ss);
  d_shared_terms.insert(n);
}

/*
 * For each tuple n, we store a mapping between n and a list of its elements
 * representatives in d_tuple_reps. This would later be used for applying
 * RELATION_JOIN operator.
 */
void TheorySetsRels::computeTupleReps(Node n)
{
  if (d_tuple_reps.find(n) == d_tuple_reps.end())
  {
    for (unsigned i = 0; i < n.getType().getTupleLength(); i++)
    {
      d_tuple_reps[n].push_back(
          getRepresentative(TupleUtils::nthElementOfTuple(n, i)));
    }
  }
}

/*
 * Node n[0] is a tuple variable, reduce n[0] to a concrete representation,
 * which is (e1, ..., en) where e1, ... ,en are concrete elements of tuple n[0].
 */
void TheorySetsRels::reduceTupleVar(Node n)
{
  if (d_symbolic_tuples.find(n) == d_symbolic_tuples.end())
  {
    Trace("rels-debug") << "[Theory::Rels] Reduce tuple var: " << n[0]
                        << " to a concrete one " << " node = " << n
                        << std::endl;
    std::vector<Node> tuple_elements;
    tuple_elements.push_back((n[0].getType().getDType())[0].getConstructor());
    std::vector<TypeNode> tupleTypes = n[0].getType().getTupleTypes();
    for (unsigned int i = 0; i < n[0].getType().getTupleLength(); i++)
    {
      Node element = TupleUtils::nthElementOfTuple(n[0], i);
      makeSharedTerm(element);
      tuple_elements.push_back(element);
    }
    Node tuple_reduct =
        nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, tuple_elements);
    tuple_reduct = nodeManager()->mkNode(Kind::SET_MEMBER, tuple_reduct, n[1]);
    Node tuple_reduction_lemma =
        nodeManager()->mkNode(Kind::EQUAL, n, tuple_reduct);
    sendInfer(tuple_reduction_lemma,
              InferenceId::SETS_RELS_TUPLE_REDUCTION,
              d_trueNode);
    d_symbolic_tuples.insert(n);
  }
}

std::vector<Node> TupleTrie::findTerms(std::vector<Node>& reps, int argIndex)
{
  std::vector<Node> nodes;
  std::map<Node, TupleTrie>::iterator it;

  if (argIndex == (int)reps.size() - 1)
  {
    Kind k = reps[argIndex].getKind();
    if (k == Kind::SKOLEM || k == Kind::DUMMY_SKOLEM)
    {
      it = d_data.begin();
      while (it != d_data.end())
      {
        nodes.push_back(it->first);
        ++it;
      }
    }
    return nodes;
  }
  else
  {
    it = d_data.find(reps[argIndex]);
    if (it == d_data.end())
    {
      return nodes;
    }
    else
    {
      return it->second.findTerms(reps, argIndex + 1);
    }
  }
}

std::vector<Node> TupleTrie::findSuccessors(std::vector<Node>& reps,
                                            int argIndex)
{
  std::vector<Node> nodes;
  std::map<Node, TupleTrie>::iterator it;

  if (argIndex == (int)reps.size())
  {
    it = d_data.begin();
    while (it != d_data.end())
    {
      nodes.push_back(it->first);
      ++it;
    }
    return nodes;
  }
  else
  {
    it = d_data.find(reps[argIndex]);
    if (it == d_data.end())
    {
      return nodes;
    }
    else
    {
      return it->second.findSuccessors(reps, argIndex + 1);
    }
  }
}

Node TupleTrie::existsTerm(std::vector<Node>& reps, int argIndex)
{
  if (argIndex == (int)reps.size())
  {
    if (d_data.empty())
    {
      return Node::null();
    }
    else
    {
      return d_data.begin()->first;
    }
  }
  else
  {
    std::map<Node, TupleTrie>::iterator it = d_data.find(reps[argIndex]);
    if (it == d_data.end())
    {
      return Node::null();
    }
    else
    {
      return it->second.existsTerm(reps, argIndex + 1);
    }
  }
}

bool TupleTrie::addTerm(Node n, std::vector<Node>& reps, int argIndex)
{
  if (argIndex == (int)reps.size())
  {
    if (d_data.empty())
    {
      // store n in d_data (this should be interpreted as the "data" and not as
      // a reference to a child)
      d_data[n].clear();
      return true;
    }
    else
    {
      return false;
    }
  }
  else
  {
    return d_data[reps[argIndex]].addTerm(n, reps, argIndex + 1);
  }
}

void TupleTrie::debugPrint(const char* c, Node n, unsigned depth)
{
  for (std::map<Node, TupleTrie>::iterator it = d_data.begin();
       it != d_data.end();
       ++it)
  {
    for (unsigned i = 0; i < depth; i++)
    {
      Trace(c) << "  ";
    }
    Trace(c) << it->first << std::endl;
    it->second.debugPrint(c, n, depth + 1);
  }
}

void TheorySetsRels::sendInfer(Node fact, InferenceId id, Node reason)
{
  Trace("rels-lemma") << "Rels::lemma " << fact << " from " << reason << " by "
                      << id << std::endl;
  Node lemma = nodeManager()->mkNode(Kind::IMPLIES, reason, fact);
  d_im.addPendingLemma(lemma, id);
}
}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

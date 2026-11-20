/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The keys and NOT NULL columns of tables (TableFacts) as lemmas
 * F => t = t', for --bags-facts=static, lemma and context.
 */

#include "theory/bags/table_facts_solver.h"



#include "expr/node_algorithm.h"
#include "options/bags_options.h"
#include "smt/env.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

TableFactsSolver::TableFactsSolver(Env& env,
                                   SolverState& state,
                                   InferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_reader(nodeManager(), env.getRewriter()),
      d_sent(userContext())
{
  if (options().bags.bagsFacts == options::BagsFactsMode::CONTEXT)
  {
    d_extt = std::make_unique<ExtTheory>(env, *this, im);
    for (Kind k : {Kind::BAG_MAP,
                   Kind::BAG_FILTER,
                   Kind::BAG_FOLD,
                   Kind::BAG_SETOF,
                   Kind::BAG_COUNT,
                   Kind::BAG_CARD,
                   Kind::BAG_UNION_DISJOINT,
                   Kind::BAG_UNION_MAX,
                   Kind::BAG_INTER_MIN,
                   Kind::BAG_DIFFERENCE_SUBTRACT,
                   Kind::BAG_DIFFERENCE_REMOVE,
                   Kind::TABLE_PROJECT,
                   Kind::TABLE_PRODUCT,
                   Kind::TABLE_JOIN,
                   Kind::TABLE_AGGREGATE,
                   Kind::TABLE_GROUP})
    {
      d_extt->addFunctionKind(k);
    }
  }
}

TableFactsSolver::~TableFactsSolver() {}

void TableFactsSolver::readFacts(Facts& f, const std::vector<Node>& lits)
{
  if (lits == f.d_lits)
  {
    return;
  }
  f.d_lits = lits;
  f.d_facts = TableFacts();
  f.d_factLits.clear();
  f.d_cache.clear();
  f.d_rewriter.reset();
  for (const Node& l : lits)
  {
    TableFacts one;
    if (!d_reader.readTableFact(l, one))
    {
      continue;
    }
    for (const auto& [T, keys] : one.d_keys)
    {
      std::vector<std::set<uint32_t>>& all = f.d_facts.d_keys[T];
      all.insert(all.end(), keys.begin(), keys.end());
      f.d_factLits[T].push_back(l);
    }
    for (const auto& [T, cols] : one.d_notNull)
    {
      f.d_facts.d_notNull[T].insert(cols.begin(), cols.end());
      f.d_factLits[T].push_back(l);
    }
  }
  if (!f.d_facts.empty())
  {
    f.d_rewriter = std::make_unique<BagsRewriter>(nodeManager(),
                                                  d_env.getRewriter(),
                                                  nullptr,
                                                  logicInfo().isHigherOrder(),
                                                  &f.d_facts);
  }
}

bool TableFactsSolver::isCandidate(const Node& t) const
{
  // a bag term, or an equality of bags: some rules that read a fact apply to
  // the equality of two queries only
  if (t.getNumChildren() == 0 || t.getKind() == Kind::LAMBDA
      || (t.getKind() == Kind::EQUAL && !t[0].getType().isBag())
      || d_env.theoryOf(t) != THEORY_BAGS)
  {
    return false;
  }
  return d_protected.find(t) == d_protected.end() && !expr::hasFreeVar(t);
}

Node TableFactsSolver::premiseOf(const Facts& f, const Node& t) const
{
  std::unordered_set<Node> syms;
  expr::getSymbols(t, syms);
  std::vector<Node> lits;
  for (const auto& [T, ls] : f.d_factLits)
  {
    if (syms.find(T) != syms.end())
    {
      for (const Node& l : ls)
      {
        if (std::find(lits.begin(), lits.end(), l) == lits.end())
        {
          lits.push_back(l);
        }
      }
    }
  }
  if (lits.empty())
  {
    return Node::null();
  }
  return nodeManager()->mkAnd(lits);
}

Node TableFactsSolver::rewriteWithFacts(Facts& f, const Node& n)
{
  if (f.d_rewriter == nullptr)
  {
    return n;
  }
  auto it = f.d_cache.find(n);
  if (it != f.d_cache.end())
  {
    return it->second;
  }
  std::unordered_map<Node, Node> visited;
  Node ret = rewriteWithFactsRec(f, n, visited, 0);
  f.d_cache[n] = ret;
  return ret;
}

Node TableFactsSolver::rewriteWithFactsRec(
    Facts& f, const Node& n, std::unordered_map<Node, Node>& visited, size_t depth)
{
  // A bound on the nesting of the calls below: each is a rule that read a
  // fact, and a chain of them this long would be a loop between the rules.
  const size_t maxDepth = 64;
  NodeManager* nm = nodeManager();
  std::vector<Node> visit{n};
  do
  {
    Node cur = visit.back();
    visit.pop_back();
    auto it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    if (!it->second.isNull())
    {
      continue;
    }
    Node ret = cur;
    if (cur.getNumChildren() > 0)
    {
      bool changed = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& c : cur)
      {
        Node cn = visited[c];
        changed = changed || cn != c;
        children.push_back(cn);
      }
      if (changed)
      {
        ret = rewrite(nm->mkNode(cur.getKind(), children));
      }
      if (depth < maxDepth && ret.getNumChildren() > 0
          && ret.getKind() != Kind::LAMBDA
          && d_env.theoryOf(ret) == THEORY_BAGS)
      {
        // ret is in normal form for the rewriter of the theory, so only a
        // rule that reads the table facts applies
        Node nr = f.d_rewriter->postRewrite(ret).d_node;
        if (nr != ret)
        {
          std::unordered_map<Node, Node> inner;
          ret = rewriteWithFactsRec(f, rewrite(nr), inner, depth + 1);
        }
      }
    }
    visited[cur] = ret;
  } while (!visit.empty());
  return visited[n];
}

bool TableFactsSolver::addFactLit(TNode lit,
                                  std::vector<Node>& lits,
                                  bool& newFact)
{
  newFact = false;
  TableFacts one;
  if (!d_reader.readTableFact(lit, one))
  {
    return false;
  }
  if (std::find(lits.begin(), lits.end(), lit) == lits.end())
  {
    lits.push_back(lit);
    newFact = true;
    // the terms of a fact are never rewritten by it, nor reduced: the solver
    // must keep enforcing what the fact says of them
    std::vector<TNode> visit{lit};
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (d_protected.insert(cur).second)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }
  return true;
}

void TableFactsSolver::lemmasFor(Facts& f,
                                 const std::vector<Node>& terms,
                                 std::vector<Node>& lemmas)
{
  if (f.d_rewriter == nullptr)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  for (const Node& t : terms)
  {
    if (d_protected.find(t) != d_protected.end())
    {
      continue;
    }
    Node tr = rewriteWithFacts(f, t);
    if (tr == t)
    {
      continue;
    }
    Node prem = premiseOf(f, t);
    if (prem.isNull())
    {
      continue;
    }
    lemmas.push_back(nm->mkNode(Kind::IMPLIES, prem, t.eqNode(tr)));
  }
}

void TableFactsSolver::ppStaticLearn(TNode in, std::vector<TrustNode>& learned)
{
  bool newFact = false;
  std::vector<Node> fresh;
  if (!addFactLit(in, d_lits, newFact))
  {
    // the candidate terms of in
    std::unordered_set<TNode> visited;
    std::vector<TNode> visit{in};
    do
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second)
      {
        continue;
      }
      if (isCandidate(cur) && d_termSeen.insert(cur).second)
      {
        d_terms.push_back(cur);
        fresh.push_back(cur);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    } while (!visit.empty());
  }
  readFacts(d_seen, d_lits);
  // a new fact applies to every term seen so far, a new term to every fact
  std::vector<Node> lemmas;
  lemmasFor(d_seen, newFact ? d_terms : fresh, lemmas);
  for (const Node& lem : lemmas)
  {
    if (d_lemmaSeen.insert(lem).second)
    {
      Trace("bags-facts") << "static: " << lem << std::endl;
      learned.push_back(TrustNode::mkTrustLemma(lem, nullptr));
    }
  }
}

void TableFactsSolver::ppRewrite(TNode n)
{
  bool newFact = false;
  std::vector<Node> fresh;
  if (n.getKind() == Kind::EQUAL && addFactLit(n, d_lits, newFact))
  {
    if (!newFact)
    {
      return;
    }
  }
  else if (isCandidate(n) && d_termSeen.insert(n).second)
  {
    d_terms.push_back(n);
    fresh.push_back(n);
  }
  else
  {
    return;
  }
  readFacts(d_seen, d_lits);
  std::vector<Node> lemmas;
  lemmasFor(d_seen, newFact ? d_terms : fresh, lemmas);
  for (const Node& lem : lemmas)
  {
    if (d_lemmaSeen.insert(lem).second)
    {
      Trace("bags-facts") << "registered: " << lem << std::endl;
      d_im.lemma(lem, InferenceId::BAGS_TABLE_FACT);
    }
  }
}

void TableFactsSolver::registerTerm(TNode n)
{
  if (d_extt != nullptr)
  {
    d_extt->registerTerm(n);
  }
}

bool TableFactsSolver::isReduced(const Node& n) const
{
  if (d_extt == nullptr)
  {
    return false;
  }
  ExtReducedId rid = ExtReducedId::NONE;
  return !d_extt->isActive(n, rid) && rid == ExtReducedId::REDUCTION;
}

bool TableFactsSolver::getCurrentSubstitution(
    CVC5_UNUSED int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node>>& exp)
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  bool any = false;
  for (const Node& v : vars)
  {
    Node s = v;
    if (v.getType().isBag() && ee->hasTerm(v))
    {
      Node r = ee->getRepresentative(v);
      eq::EqClassIterator it(r, ee);
      while (!it.isFinished())
      {
        if ((*it).isConst())
        {
          s = *it;
          break;
        }
        ++it;
      }
    }
    subs.push_back(s);
    if (s != v)
    {
      exp[v].push_back(v.eqNode(s));
      any = true;
    }
  }
  return any;
}

void TableFactsSolver::check(const std::vector<Node>& asserted)
{
  NodeManager* nm = nodeManager();
  if (d_extt == nullptr)
  {
    // C: every registered term, by the fact atoms registered
    for (const Node& l : asserted)
    {
      bool newFact = false;
      addFactLit(l, d_lits, newFact);
    }
    readFacts(d_seen, d_lits);
    if (d_seen.d_rewriter == nullptr)
    {
      return;
    }
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    // the terms registered before ppRewrite reduced them, and those of the
    // equality engine
    std::vector<Node> terms = d_terms;
    eq::EqClassesIterator eqcs(ee);
    while (!eqcs.isFinished())
    {
      eq::EqClassIterator it(*eqcs, ee);
      while (!it.isFinished())
      {
        if (isCandidate(*it))
        {
          terms.push_back(*it);
        }
        ++it;
      }
      ++eqcs;
    }
    std::vector<Node> lemmas;
    lemmasFor(d_seen, terms, lemmas);
    for (const Node& lem : lemmas)
    {
      if (d_sent.insert(lem))
      {
        Trace("bags-facts") << "lemma: " << lem << std::endl;
        d_im.addPendingLemma(lem, InferenceId::BAGS_TABLE_FACT);
      }
    }
    return;
  }
  // E: the active terms, substituted by the constants of their classes and
  // rewritten by the facts asserted in the current context, are reduced
  std::vector<Node> lits;
  for (const Node& l : asserted)
  {
    bool newFact = false;
    std::vector<Node> dummy;
    if (addFactLit(l, dummy, newFact))
    {
      lits.push_back(l);
    }
  }
  readFacts(d_asserted, lits);
  // the terms that ppRewrite reduced are not registered in the extended
  // theory, and have no context: they get the lemmas of C
  {
    std::vector<Node> lemmas;
    lemmasFor(d_asserted, d_terms, lemmas);
    for (const Node& lem : lemmas)
    {
      if (d_sent.insert(lem))
      {
        Trace("bags-facts") << "context, registered: " << lem << std::endl;
        d_im.addPendingLemma(lem, InferenceId::BAGS_TABLE_FACT);
      }
    }
  }
  std::vector<Node> terms = d_extt->getActive();
  std::vector<Node> sterms;
  std::vector<std::vector<Node>> exp;
  d_extt->getSubstitutedTerms(0, terms, sterms, exp);
  for (size_t i = 0, size = terms.size(); i < size; i++)
  {
    const Node& t = terms[i];
    if (!isCandidate(t))
    {
      continue;
    }
    Node ts = rewrite(sterms[i]);
    Node tr = rewriteWithFacts(d_asserted, ts);
    if (tr == t)
    {
      continue;
    }
    std::vector<Node> ante = exp[i];
    if (tr != ts)
    {
      Node prem = premiseOf(d_asserted, ts);
      if (prem.isNull())
      {
        continue;
      }
      ante.push_back(prem);
    }
    Node concl = t.eqNode(tr);
    Node lem = ante.empty() ? concl
                            : nm->mkNode(Kind::IMPLIES, nm->mkAnd(ante), concl);
    if (d_sent.insert(lem))
    {
      Trace("bags-facts") << "context: " << lem << std::endl;
      d_im.addPendingLemma(lem, InferenceId::BAGS_TABLE_FACT);
    }
    d_extt->markInactive(t, ExtReducedId::REDUCTION, true);
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

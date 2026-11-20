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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__TABLE_FACTS_SOLVER_H
#define CVC5__THEORY__BAGS__TABLE_FACTS_SOLVER_H

#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/ext_theory.h"
#include "proof/trust_node.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class SolverState;
class InferenceManager;

/**
 * Sends, for a fact F of a table (a key or a NOT NULL column, see TableFacts)
 * and a term t over that table, the lemma
 *
 *   F => (= t t')
 *
 * where t' is t rewritten by a BagsRewriter that has the fact. For example,
 * with column 1 of X never null,
 *
 *   (=> (= (bag.filter (lambda ((t T)) (= ((_ tuple.select 1) t) null)) X)
 *          (as bag.empty (Bag T)))
 *       (= (bag.filter (lambda ((t T)) (and (nullable.is_some t.1) (> t.0 3))) X)
 *          (bag.filter (lambda ((t T)) (> t.0 3)) X)))
 *
 * The rewriter of the theory stays pure: the fact is the lemma's premise.
 * Three places send these lemmas (--bags-facts):
 * - static (D): Theory::ppStaticLearn, for the terms of the input;
 * - lemma (C): the bag solver at full effort, for every registered term;
 * - context (E): context-dependent simplification as in ExtTheory: every
 *   active term is substituted by the constants of its equivalence classes,
 *   rewritten with the facts true in the current context, and marked reduced,
 *   so that the bag solver works on t' only.
 */
class TableFactsSolver : protected EnvObj, public ExtTheoryCallback
{
 public:
  TableFactsSolver(Env& env, SolverState& state, InferenceManager& im);
  ~TableFactsSolver();

  /** D: the lemmas for the terms of the input assertion in */
  void ppStaticLearn(TNode in, std::vector<TrustNode>& learned);
  /**
   * C and E: the lemmas for a term the theory preprocessor registers, before
   * ppRewrite reduces it (as it does table.aggr and table.project), by the
   * fact atoms registered so far; and the facts a registered atom states.
   */
  void ppRewrite(TNode n);
  /** E: register a term with the extended theory */
  void registerTerm(TNode n);
  /**
   * C and E, at full effort: the lemmas for the registered terms, by the fact
   * atoms registered (C) or by the literals asserted in the current context
   * (E, which also reduces the terms it rewrites).
   */
  void check(const std::vector<Node>& asserted);
  /** E: whether n is reduced in the current context, so the solver skips it */
  bool isReduced(const Node& n) const;

  /** ExtTheoryCallback: the constant of the equivalence class of each var */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node>>& exp) override;

 private:
  /** Facts, the literals that state them, and a rewriter that has them */
  struct Facts
  {
    std::vector<Node> d_lits;
    TableFacts d_facts;
    std::map<Node, std::vector<Node>> d_factLits;
    std::unique_ptr<BagsRewriter> d_rewriter;
    std::unordered_map<Node, Node> d_cache;
  };
  /** Sets f to the facts read off lits, unless they are those of f already */
  void readFacts(Facts& f, const std::vector<Node>& lits);
  /** n rewritten bottom-up with the facts f (see LearnedRewrite) */
  Node rewriteWithFacts(Facts& f, const Node& n);
  Node rewriteWithFactsRec(Facts& f,
                           const Node& n,
                           std::unordered_map<Node, Node>& visited,
                           size_t depth);
  /** The facts of f of the tables t reads, a conjunction, or null */
  Node premiseOf(const Facts& f, const Node& t) const;
  /** Whether t is a term a rule that reads a fact may apply to */
  bool isCandidate(const Node& t) const;
  /**
   * Whether lit states a fact; if it does, it is added to lits (once), its
   * subterms are protected, and newFact says whether it was new.
   */
  bool addFactLit(TNode lit, std::vector<Node>& lits, bool& newFact);
  /** The lemmas F => t = t' for the terms, by the facts f */
  void lemmasFor(Facts& f,
                 const std::vector<Node>& terms,
                 std::vector<Node>& lemmas);

  /** The solver state */
  SolverState& d_state;
  /** The inference manager */
  InferenceManager& d_im;
  /** A pure rewriter, which reads facts off literals */
  BagsRewriter d_reader;
  /** D, and the registration of C and E: the fact atoms seen so far */
  Facts d_seen;
  /** E: the facts asserted in the current context */
  Facts d_asserted;
  /** The terms that occur in a fact literal: never rewritten nor reduced */
  std::unordered_set<Node> d_protected;
  /** The terms and fact literals seen so far, and the lemmas sent */
  std::vector<Node> d_terms;
  std::vector<Node> d_lits;
  std::unordered_set<Node> d_termSeen;
  std::unordered_set<Node> d_lemmaSeen;
  /** C and E: the lemmas sent at full effort, in the user context */
  context::CDHashSet<Node> d_sent;
  /** E: the extended theory, whose active terms are those not reduced */
  std::unique_ptr<ExtTheory> d_extt;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__TABLE_FACTS_SOLVER_H */

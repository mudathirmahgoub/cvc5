/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Static learning of the lemmas that the keys and NOT NULL columns of tables
 * give, and of EQ_EMPTY_ARG.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__TABLE_FACTS_LEARNER_H
#define CVC5__THEORY__BAGS__TABLE_FACTS_LEARNER_H

#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/bags/bags_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/**
 * For a fact F that a top-level assertion states of a table, a key or a NOT
 * NULL column (see TableFacts), and a term t of the input that reads the same
 * table, learns the lemma
 *
 *   F => (= t t')
 *
 * where t' is t rewritten by a BagsRewriter that has the facts. For
 * X : (Bag (Tuple Int Int)) with column 0 a key,
 *
 *   (=> (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))
 *       (= ((_ table.aggr 0) f (tuple 0 0 0) X)
 *          (bag.map (lambda ((t (Tuple Int Int))) (f t (tuple 0 0 0))) X)))
 *
 * The rewriter of the theory knows no fact, so what it returns depends only on
 * the node it rewrites, and the fact is the premise of the lemma, which a
 * proof can name.
 *
 * The rewriter also applies EQ_EMPTY_ARG, which reads no fact and which the
 * rewriter of the theory must not apply (see BagsRewriter::postRewriteEqual).
 * For a term t that reads no table with a fact, the lemma is (= t t'). For
 * X : (Bag (Tuple Int Int)), Y : (Bag (Tuple Int)) and
 *
 *   P = (lambda ((y (Tuple Int)))
 *         (= ((_ tuple.select 0) y) ((_ tuple.select 1) t)))
 *   g = (lambda ((y (Tuple Int))) (tuple 1))
 *
 * the rows of X with no row in Y, a NOT EXISTS, give
 *
 *   (= (bag.filter
 *        (lambda ((t (Tuple Int Int)))
 *          (= (bag.map g (bag.filter P Y)) (as bag.empty (Bag (Tuple Int)))))
 *        X)
 *      (bag.filter
 *        (lambda ((t (Tuple Int Int)))
 *          (= (bag.filter P Y) (as bag.empty (Bag (Tuple Int)))))
 *        X))
 *
 * The facts outlive a pop: a lemma has its fact as premise, so it holds in any
 * scope. The terms and the lemmas are those of the current scope, since the
 * lemmas of a popped scope are gone.
 */
class TableFactsLearner : protected EnvObj
{
 public:
  TableFactsLearner(Env& env);
  ~TableFactsLearner();

  /**
   * Adds to learned the lemmas of the top-level assertion in (see
   * Theory::ppStaticLearn): if in states a fact, for it and every term seen so
   * far; otherwise, for the terms of in and every fact seen so far.
   */
  void ppStaticLearn(TNode in, std::vector<TrustNode>& learned);

 private:
  /**
   * Whether lit states a fact. A new one is recorded, its terms are never
   * rewritten (see d_protected), and the rewriter that has the facts is made
   * anew.
   */
  bool addFact(TNode lit);
  /** Makes d_rewriter anew for d_facts, and clears d_cache */
  void makeRewriter();
  /**
   * Whether t is a term that a rule reading a fact, or EQ_EMPTY_ARG, may
   * rewrite
   */
  bool isCandidate(const Node& t) const;
  /** The conjunction of the fact literals of the tables t reads, or null */
  Node premiseOf(const Node& t) const;
  /** n rewritten bottom-up by the rewriter that has the facts */
  Node rewriteWithFacts(const Node& n);
  Node rewriteWithFactsRec(const Node& n, size_t depth);
  /**
   * Adds to learned the lemmas F => (= t t') for the terms, or (= t t') for a
   * term that reads no table with a fact
   */
  void learnFor(const std::vector<Node>& terms,
                std::vector<TrustNode>& learned);

  /** A rewriter without facts, which reads facts off literals */
  BagsRewriter d_reader;
  /** The facts seen so far */
  TableFacts d_facts;
  /** For each table, the literals that state its facts */
  std::map<Node, std::vector<Node>> d_factLits;
  /** A rewriter that has d_facts, which may be empty */
  std::unique_ptr<BagsRewriter> d_rewriter;
  /** rewriteWithFacts by d_rewriter, cleared when a fact is added */
  std::unordered_map<Node, Node> d_cache;
  /**
   * The terms of the fact literals. A lemma for one would rewrite it by the
   * fact it states.
   */
  std::unordered_set<Node> d_protected;
  /** The candidate terms of the current scope, in order */
  context::CDList<Node> d_terms;
  context::CDHashSet<Node> d_termSeen;
  /** The lemmas of the current scope */
  context::CDHashSet<Node> d_learned;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__TABLE_FACTS_LEARNER_H */

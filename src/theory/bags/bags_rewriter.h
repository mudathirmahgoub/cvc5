/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include <map>
#include <unordered_map>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H
#define CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H

#include <set>
#include <utility>

#include "theory/bags/rewrites.h"
#include "theory/theory_rewriter.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/** a class represents the result of rewriting bag nodes */
struct BagsRewriteResponse
{
  BagsRewriteResponse();
  BagsRewriteResponse(Node n, Rewrite rewrite);
  /** the rewritten node */
  Node d_node;
  /** type of rewrite used by bags */
  Rewrite d_rewrite;

}; /* struct BagsRewriteResponse */

/**
 * The rewriter of the theory of bags and tables.
 *
 * Besides the rules for bag constants and the basic operators, it puts the
 * terms of relational algebra over tables (bags of tuples) in a normal form,
 * so that two queries that are one SQL rewrite apart become one term, or
 * terms that the solver relates cheaply. The normal form of a select-project-
 * join query is
 *   (bag.map h (bag.filter P (table.product X1 (table.product X2 ..))))
 * maps above filters above products, products right-nested and sorted, every
 * lambda over a canonical variable (canonicalLambda). Aggregates
 * ((_ table.aggr K) f i X) have their own normal forms: grouping by a key,
 * pushing through joins and unions, merging and splitting.
 *
 * Some rules use facts about the table constants of the problem, its keys and
 * NOT NULL columns, which the bags-facts preprocessing pass reads off the
 * top-level assertions (recordFacts).
 *
 * The notation of the examples is described at the top of bags_rewriter.cpp:
 * SMT-LIB terms over tables X, Y of rows of sort T, with t a row bound by a
 * lambda and acc an accumulator. Each rule is named by its Rewrite value,
 * see rewrites.h, and shown as
 *   previous node
 *   ---> next node
 */
class BagsRewriter : public TheoryRewriter
{
 public:
  /**
   * With higherOrder false, for a logic without higher-order terms, the rules
   * that build a lambda where the term has none (FILTER_FILTER, FILTER_MAP,
   * MAP_MAP, PRODUCT_MAP_*, PRODUCT_FILTER_*, PRODUCT_SWAP, PRODUCT_BAG_MAKE,
   * PROJECT_TO_MAP, and COUNT_MAP_CONST_PROBE over a table constant) do not
   * apply: the theory of uninterpreted functions rejects lambdas there. The
   * rewriter does not know the logic, so the default is false: the owner of
   * the rewriter passes true for a higher-order logic.
   */
  BagsRewriter(NodeManager* nm,
               Rewriter* r,
               HistogramStat<Rewrite>* statistics = nullptr,
               bool higherOrder = false);

  /**
   * postRewrite nodes with kinds: EQUAL, BAG_MAKE, BAG_COUNT, BAG_SETOF,
   * BAG_UNION_MAX, BAG_UNION_DISJOINT, BAG_INTER_MIN,
   * BAG_DIFFERENCE_SUBTRACT, BAG_DIFFERENCE_REMOVE, BAG_CHOOSE, BAG_CARD,
   * BAG_MAP, BAG_FILTER, BAG_ALL, BAG_SOME, BAG_FOLD, BAG_PARTITION,
   * TABLE_PRODUCT, TABLE_PROJECT, TABLE_AGGREGATE and TABLE_GROUP; a node
   * whose children are constants is evaluated. See the rewrite rules for
   * these kinds below. With the environment variable BAGS_TRACE set, every
   * step is printed on stderr, a debugging aid.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, BAG_SUBBAG, BAG_MEMBER.
   * See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

  /**
   * Record the facts a top-level assertion states about table constants,
   * which the rules below then use: the keys of a table (see recordKey) and
   * its NOT NULL columns (see recordNotNull). Conjuncts of a top-level
   * conjunction are read too. The bags-facts preprocessing pass calls this on
   * every assertion before any of them is rewritten; the rewriter never
   * reads a fact off an equality it rewrites, which may not be asserted (it
   * may occur under a negation). E.g. for the assertions
   *   (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))
   *   (= (bag.filter (lambda ((t T))
   *                    (= ((_ tuple.select 1) t)
   *                       (as nullable.null (Nullable Int))))
   *                  X)
   *      (as bag.empty (Bag T)))
   * column 0 is a key of X and column 1 of X is never null.
   */
  void recordFacts(TNode assertion) const;

 private:
  // ---------------------------------------------------------------------------
  // The rules of each kind. A function returns its argument with
  // Rewrite::NONE when no rule applies.
  // ---------------------------------------------------------------------------

  /**
   * rewrites for n include:
   * - (= A A) = true where A is a bag
   */
  BagsRewriteResponse preRewriteEqual(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.subbag A B) = ((bag.difference_subtract A B) == bag.empty)
   */
  BagsRewriteResponse rewriteSubBag(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.member x A) = (>= (bag.count x A) 1)
   */
  BagsRewriteResponse rewriteMember(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag x 0) = (bag.empty T) where T is the type of x
   * - (bag x (-c)) = (bag.empty T) where T is the type of x, and c > 0 is a
   *   constant
   * - otherwise = n
   */
  BagsRewriteResponse rewriteMakeBag(const TNode& n) const;

  /**
   * rewrites for n include:
   * - COUNT_EMPTY: (bag.count x (as bag.empty (Bag T))) ---> 0
   * - COUNT_BAG_MAKE: (bag.count x (bag x c)) ---> c, c > 0 a constant
   * - COUNT_NULL_IN_NOT_NULL, a null in a column X has no null in:
   *     (bag.count (tuple a (as nullable.null (Nullable Int))) X) ---> 0
   * - COUNT_MAP_DUPLICATE_COLUMNS, a map that makes columns i < j equal:
   *     (bag.count (tuple a b c) (bag.map (lambda ((t T)) (tuple u v u)) X))
   *     ---> (ite (= a c)
   *               (bag.count (tuple a b)
   *                          (bag.map (lambda ((t T)) (tuple u v)) X))
   *               0)
   * - COUNT_MAP_CONST_COLUMN, a map that makes column j a constant:
   *     (bag.count (tuple a b)
   *                (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
   *                         X))
   *     ---> (ite (= b 5)
   *               (bag.count (tuple a)
   *                          (bag.map (lambda ((t T))
   *                                     (tuple ((_ tuple.select 0) t)))
   *                                   X))
   *               0)
   * - COUNT_MAP_CONST_PROBE, a constant in the probe selects rows of X:
   *     (bag.count (tuple 5 b)
   *                (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)
   *                                                ((_ tuple.select 0) t)))
   *                         X))
   *     ---> (bag.count (tuple b)
   *                     (bag.map (lambda ((t T))
   *                                (tuple ((_ tuple.select 0) t)))
   *                              (bag.filter (lambda ((t T))
   *                                            (= ((_ tuple.select 1) t) 5))
   *                                          X)))
   *   also for a table constant X, as its identity map
   * - COUNT_MAP_FILTER_KEYS, a conjunct on projected columns is decided on
   *   the probe:
   *     (bag.count (tuple a)
   *                (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                         (bag.filter (lambda ((t T)) (and c q)) X)))
   *     ---> (ite c[((_ tuple.select 0) t) := a]
   *               (bag.count (tuple a)
   *                          (bag.map (lambda ((t T))
   *                                     (tuple ((_ tuple.select 0) t)))
   *                                   (bag.filter (lambda ((t T)) q) X)))
   *               0)
   *   for c reading only column 0 of t
   * - COUNT_MAP_FILTER_CORRELATED, an equation of a column with a term E of
   *   an enclosing row becomes a column of the map and the probe:
   *     (bag.count (tuple a)
   *                (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                         (bag.filter (lambda ((t T))
   *                                       (and (= ((_ tuple.select 1) t) E)
   *                                            q))
   *                                     X)))
   *     ---> (bag.count (tuple a E)
   *                     (bag.map (lambda ((t T))
   *                                (tuple ((_ tuple.select 0) t)
   *                                       ((_ tuple.select 1) t)))
   *                              (bag.filter (lambda ((t T)) q) X)))
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   * rewrites for n include, unless n is the bag.setof of a key assertion
   * (see BagsKeyTermAttribute in the .cpp):
   * - SETOF_BAG_MAKE: (bag.setof (bag x c)) ---> (bag x 1), c > 0 a
   *   constant; (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
   * - SETOF_SETOF: (bag.setof (bag.setof A)) ---> (bag.setof A)
   * - SETOF_UNION_SAME:
   *     (bag.setof (bag.union_disjoint A A)) ---> (bag.setof A)
   * - SETOF_ABSORB, an inner bag.setof under maps, filters and unions:
   *     (bag.setof (bag.map f (bag.setof X))) ---> (bag.setof (bag.map f X))
   * - SETOF_OF_SET, a bag with no element twice (see isSet):
   *     (bag.setof X) ---> X
   * - AGGREGATE_GROUP_KEYS, see keysOfReachedGroups:
   *     (bag.setof (bag.map h (bag.filter Q ((_ table.aggr K) f i X))))
   *     ---> (bag.setof (bag.map h' X))
   * - SEMI_TO_INTERSECTION, see semiJoinToIntersection
   * - SETOF_PUSHDOWN, see rewriteSetofPushdown
   * - SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, see rewriteSetofOfMap
   */
  BagsRewriteResponse rewriteSetof(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.union_max A bag.empty) = A
   * - (bag.union_max bag.empty A) = A
   * - (bag.union_max A A) = A
   * - (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
   * - (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
   * - (bag.union_max (bag.union_max A B) A) = (bag.union_max A B)
   * - (bag.union_max (bag.union_max B A) A) = (bag.union_max B A)
   * - (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
   * - (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
   * - (bag.union_max (bag.union_disjoint A B) A) = (bag.union_disjoint A B)
   * - (bag.union_max (bag.union_disjoint B A) A) = (bag.union_disjoint B A)
   * - otherwise = n
   */
  BagsRewriteResponse rewriteUnionMax(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.union_disjoint A bag.empty) = A
   * - (bag.union_disjoint bag.empty A) = A
   * - (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B)) =
   *         (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
   * - other permutations of the above like swapping A and B, or swapping
   *   bag.intersection_min and bag.union_max
   * - UNION_COMPLEMENTARY_FILTERS, filters of X by p and by (not p):
   *     (bag.union_disjoint (bag.filter (lambda ((t T)) (and p q)) X)
   *                         (bag.filter (lambda ((t T)) (and (not p) q)) X))
   *     ---> (bag.filter (lambda ((t T)) q) X)
   *   also under one map of both, and for two parts of a longer union
   * - otherwise = n
   */
  BagsRewriteResponse rewriteUnionDisjoint(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.inter_min A bag.empty) = bag.empty
   * - (bag.inter_min bag.empty A) = bag.empty
   * - (bag.inter_min A A) = A
   * - (bag.inter_min A (bag.union_disjoint A B)) = A
   * - (bag.inter_min A (bag.union_disjoint B A)) = A
   * - (bag.inter_min (bag.union_disjoint A B) A) = A
   * - (bag.inter_min (bag.union_disjoint B A) A) = A
   * - (bag.inter_min A (bag.union_max A B)) = A
   * - (bag.inter_min A (bag.union_max B A)) = A
   * - (bag.inter_min (bag.union_max A B) A) = A
   * - (bag.inter_min (bag.union_max B A) A) = A
   * - INTERSECTION_SORT: (bag.inter_min B A) ---> (bag.inter_min A B) for
   *   A < B
   * - INTERSECTION_SHARE_CONDITIONS, each side gets the conditions the
   *   elements of the other satisfy (see elementConditions):
   *     (bag.inter_min (bag.filter (lambda ((t T)) qA) X)
   *                    (bag.filter (lambda ((t T)) qB) Y))
   *     ---> (bag.inter_min (bag.filter (lambda ((t T)) (and qA qB)) X)
   *                         (bag.filter (lambda ((t T)) (and qA qB)) Y))
   *   up to the order of the conjuncts
   * - otherwise = n
   */
  BagsRewriteResponse rewriteIntersectionMin(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.difference_subtract A bag.empty) = A
   * - (bag.difference_subtract bag.empty A) = bag.empty
   * - (bag.difference_subtract A A) = bag.empty
   * - (bag.difference_subtract (bag.union_disjoint A B) A) = B
   * - (bag.difference_subtract (bag.union_disjoint B A) A) = B
   * - (bag.difference_subtract A (bag.union_disjoint A B)) = bag.empty
   * - (bag.difference_subtract A (bag.union_disjoint B A)) = bag.empty
   * - (bag.difference_subtract A (bag.union_max A B)) = bag.empty
   * - (bag.difference_subtract A (bag.union_max B A)) = bag.empty
   * - (bag.difference_subtract (bag.inter_min A B) A) = bag.empty
   * - (bag.difference_subtract (bag.inter_min B A) A) = bag.empty
   * - otherwise = n
   */
  BagsRewriteResponse rewriteDifferenceSubtract(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (bag.difference_remove A bag.empty) = A
   * - (bag.difference_remove bag.empty A) = bag.empty
   * - (bag.difference_remove A A) = bag.empty
   * - (bag.difference_remove A (bag.union_disjoint A B)) = bag.empty
   * - (bag.difference_remove A (bag.union_disjoint B A)) = bag.empty
   * - (bag.difference_remove A (bag.union_max A B)) = bag.empty
   * - (bag.difference_remove A (bag.union_max B A)) = bag.empty
   * - (bag.difference_remove (bag.inter_min A B) A) = bag.empty
   * - (bag.difference_remove (bag.inter_min B A) A) = bag.empty
   * - otherwise = n
   */
  BagsRewriteResponse rewriteDifferenceRemove(const TNode& n) const;
  /**
   * rewrites for n include:
   * - (bag.choose (bag x c)) = x where c is a constant > 0
   * - otherwise = n
   */
  BagsRewriteResponse rewriteChoose(const TNode& n) const;
  /**
   * rewrites for n include:
   * - (bag.card (bag x c)) = c where c is a constant
   * - otherwise = n
   */
  BagsRewriteResponse rewriteCard(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (= A A) = true
   *  - (= A B) = false if A and B are different bag constants
   *  - (= B A) = (= A B) if A < B and at least one of A or B is not a constant
   *  - EQ_EMPTY_ARG, a map or a bag.setof is empty when its argument is:
   *      (= (bag.map f X) (as bag.empty (Bag U)))
   *      ---> (= X (as bag.empty (Bag T)))
   *      (= (bag.setof X) (as bag.empty (Bag T)))
   *      ---> (= X (as bag.empty (Bag T)))
   */
  BagsRewriteResponse postRewriteEqual(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.map f (as bag.empty (Bag T1)) = (as bag.empty (Bag T2))
   *  - (bag.map f (bag x y)) = (bag (apply f x) y)
   *  - (bag.map f (bag.union_disjoint A B)) =
   *       (bag.union_disjoint (bag.map f A) (bag.map f B))
   *  where f: T1 -> T2
   *  - MAP_IDENTITY:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
   *                                      ((_ tuple.select 1) t)))
   *               X)
   *      ---> X
   *  - NOT_NULL_COLUMNS, the null tests of columns X never has null in are
   *    decided (see assumeNonNull):
   *      (bag.map (lambda ((t T))
   *                 (ite (nullable.is_some ((_ tuple.select 1) t)) a b))
   *               X)
   *      ---> (bag.map (lambda ((t T)) (ite true a b)) X)
   *  - MAP_MAP, see rewriteMapOfMap
   *  - EQ_EMPTY_FILTER_DECORRELATE, see normalizeEmptiness
   *  - MAP_SPLIT_CLOSED, AGGREGATE_DEAD_COLUMNS, AGGREGATE_COLLAPSE,
   *    AGGREGATE_ROLLUP, AGGREGATE_JOIN_MERGE, AGGREGATE_SETOF_IDEMPOTENT,
   *    PRODUCT_AGGREGATE_DEAD_COLUMN, AGGREGATE_UNION_DISJOINT_KEYS and
   *    AGGREGATE_UNION_SPLIT, see their functions
   *  - MAP_EQUAL_COLUMNS, the first of the columns the filter equates:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)))
   *               (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                              ((_ tuple.select 2) s)))
   *                           X))
   *      ---> (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                    (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                                   ((_ tuple.select 2) s)))
   *                                X))
   *  - AGGREGATE_GROUP_KEYS, see keysOfReachedGroups:
   *      (bag.map h (bag.filter Q ((_ table.aggr K) f i X)))
   *      ---> (bag.setof (bag.map h' X))
   *  - MAP_FIXED_COLUMNS, the constants the filter fixes columns to:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)))
   *               (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                           X))
   *      ---> (bag.map (lambda ((t T)) (tuple 5))
   *                    (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s)
   *                                                   5))
   *                                X))
   *    and, over an aggregate whose counter the filter tests, the constants
   *    its groups compute (see reachedGroupConstants)
   *  - MAP_IDENTITY_ON_FILTER, the identity on the rows that pass:
   *      (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
   *               (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                           X))
   *      ---> (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X)
   *  - SEMI_TO_INTERSECTION and SEMI_JOIN, see semiJoinToIntersection and
   *    rewriteSemiJoin
   *  - CANONICAL_VARIABLE, see canonicalLambda
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   *  rewrites for n include, unless n is the filter of a not-null assertion
   *  (see BagsKeyTermAttribute in the .cpp):
   *  - (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
   *  - FILTER_BAG_MAKE: (bag.filter p (bag x y)) ---> (bag x (ite (p x) y 0))
   *  - (bag.filter p (bag.union_disjoint A B)) =
   *       (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   *  where p: T -> Bool
   *  - FILTER_COUNT_AS_COUNTER, COUNT(*) read as the counter c of the
   *    aggregate:
   *      (bag.filter (lambda ((t T)) (= ((_ tuple.select 1) t)
   *                                     (nullable.some 3)))
   *                  ((_ table.aggr 0) f i X))
   *      ---> (bag.filter (lambda ((t T))
   *                         (= (nullable.some ((_ tuple.select 2) t))
   *                            (nullable.some 3)))
   *                       ((_ table.aggr 0) f i X))
   *  - NOT_NULL_COLUMNS, as for bag.map
   *  - FILTER_TRUE and FILTER_FALSE:
   *      (bag.filter (lambda ((t T)) true) A) ---> A
   *      (bag.filter (lambda ((t T)) false) A) ---> (as bag.empty (Bag T))
   *      (bag.filter (lambda ((t T)) (and p (not p))) A)
   *      ---> (as bag.empty (Bag T))
   *  - EQ_EMPTY_FILTER_DECORRELATE, see normalizeEmptiness
   *  - FILTER_NULLABLE_TRUTH, see normalizeTruth
   *  - FILTER_DE_MORGAN:
   *      (bag.filter (lambda ((t T)) (and p (not (or a b)))) X)
   *      ---> (bag.filter (lambda ((t T)) (and p (not a) (not b))) X)
   *  - FILTER_CONFLICTING_CONSTANTS:
   *      (bag.filter (lambda ((t T)) (and (= ((_ tuple.select 0) t) 1)
   *                                       (= ((_ tuple.select 0) t) 2)))
   *                  X)
   *      ---> (as bag.empty (Bag T))
   *    and the conjuncts the others imply go: (nullable.is_some a) beside
   *    (= a (nullable.some 5)), the null test of a value that a membership
   *    puts in a never-null column, (>= (* a b) 1) beside (>= a 1) and
   *    (>= b 1)
   *  - FILTER_KNOWN_NONEMPTY, a bag a membership conjunct finds a row in is
   *    not empty:
   *      (and (>= (bag.count e (bag.map g Y)) 1)
   *           (not (= Y (as bag.empty (Bag U)))))
   *      ---> (>= (bag.count e (bag.map g Y)) 1)
   *    in the predicate, and the filter is empty when it says Y is empty
   *  - FILTER_INTO_SETOF, see rewriteFilterIntoSetofComponent
   *  - FILTER_KNOWN_MEMBERSHIP, see dropKnownMemberships
   *  - FILTER_SORT_CONJUNCTS, the conjuncts in the order of their alpha
   *    keys, without duplicates:
   *      (bag.filter (lambda ((t T)) (and q p q)) X)
   *      ---> (bag.filter (lambda ((t T)) (and p q)) X)
   *  - CANONICAL_VARIABLE, see canonicalLambda
   *  - FILTER_SPLIT_CLOSED, a disjunct c that does not read the row (EXISTS):
   *      (bag.filter (lambda ((t T)) (or c q)) A)
   *      ---> (bag.union_disjoint
   *             (bag.filter (lambda ((t T)) c) A)
   *             (bag.filter (lambda ((t T)) (and (not c) q)) A))
   *  - FILTER_FILTER and FILTER_MAP, see rewriteFilterOfFilter and
   *    rewriteFilterOfMap
   *  - AGGREGATE_KEYED, see keyedAggregateRows: under a filter that drops the
   *    row of initial values (see rejectsInitialRow),
   *      (bag.filter Q ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X))
   *      ---> (bag.filter Q (bag.map (lambda ((t T)) b[acc := i]) X))
   *    for 0 a key of X, and for an aggregate component of a product whose
   *    groups the filter keeps reached ones of (see reachedComponents)
   *  - FILTER_AGGREGATE_ONE_ROW, an aggregate of one row e:
   *      (bag.filter Q ((_ table.aggr 0) f i (bag e m)))
   *      ---> (bag.filter Q (bag (f e i) m))
   *    for Q testing the counter, m 1 or (ite c 1 0)
   *  - FILTER_AGGREGATE, see rewriteFilterOfAggregate
   *  - FILTER_SETOF:
   *      (bag.filter p (bag.setof A)) ---> (bag.setof (bag.filter p A))
   *  - FILTER_INTER_MIN:
   *      (bag.filter p (bag.inter_min A B))
   *      ---> (bag.inter_min (bag.filter p A) (bag.filter p B))
   *  - FILTER_IMPLIED_COUNTER, FILTER_JOIN_TRANSITIVE and
   *    FILTER_EQUI_JOIN_SETS, see dropImpliedCounters,
   *    rewriteJoinTransitiveConditions and rewriteEquiJoinOfSets
   */
  BagsRewriteResponse postRewriteFilter(const TNode& n) const;

  /**
   *  rewrites for n include:
   *  - (bag.all p (as bag.empty (Bag T)) is rewritten as true
   *  - (bag.all p (bag x n)) is rewritten as ((p x) or (<= n 0))
   *  - (bag.all p (bag.union_disjoint A B)) is rewritten as
   *       (and (bag.all p A) (bag.all p B))
   *  - otherwise (bag.all p A) is rewritten as (= (bag.filter p A) A)
   *  where p: T -> Bool
   */
  BagsRewriteResponse postRewriteAll(TNode n);
  /**
   *  rewrites for n include:
   *  - (bag.some p (as bag.empty (Bag T)) is rewritten as false
   *  - (bag.some p (bag x n)) is rewritten as (and (> n 0) (p x))
   *  - (bag.some p (bag.union A B)) is rewritten as
   *       (or (bag.some p A) (bag.some p B))
   *  - otherwise (bag.some p A) is rewritten as
   *       (distinct (bag.filter p A) (as bag.empty (Bag T)))
   *  where p: T -> Bool
   */
  BagsRewriteResponse postRewriteSome(TNode n);

  /**
   *  rewrites for n include:
   *  - (bag.fold f t (as bag.empty (Bag T1))) = t
   *  - (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, where n > 0
   *  - (bag.fold f t (bag.union_disjoint A B)) =
   *       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
   *  where f: T1 -> T2 -> T2
   *  - FOLD_IDENTITY_STEP: (bag.fold (lambda ((t T) (acc S)) acc) i X) ---> i
   *  - FOLD_OVER_JOIN, the eager form of a fold over a join, see
   *    eagerAggregation:
   *      (bag.fold f i (bag.filter P (table.product X Y)))
   *      ---> (bag.fold f' i J')
   *  - FOLD_SUM_FROM_ZERO, SUM from 0 is the sum from null, or 0:
   *      (bag.fold (lambda ((t T) (acc (Nullable Int)))
   *                  (nullable.some (+ (nullable.val acc) e)))
   *                (nullable.some 0) X)
   *      ---> (ite (= (as nullable.null (Nullable Int)) S) (nullable.some 0) S)
   *    with S the fold that skips nulls from null
   *  - FOLD_UNION_COMBINE, a sum, minimum, maximum or count over a union is
   *    the two folds combined:
   *      (bag.fold f (as nullable.null (Nullable Int))
   *                (bag.union_disjoint A B))
   *      ---> (ite (= (as nullable.null (Nullable Int)) a) b
   *                (ite (= (as nullable.null (Nullable Int)) b) a
   *                     (nullable.some (+ (nullable.val a) (nullable.val b)))))
   *    for a sum f, with a and b the folds over A and B
   *  - NOT_NULL_COLUMNS, as for bag.map
   *  - FOLD_MAP:
   *      (bag.fold (lambda ((t U) (acc S)) b) i
   *                (bag.map (lambda ((s T)) e) Y))
   *      ---> (bag.fold (lambda ((s T) (acc S)) b[t := e]) i Y)
   *  - FOLD_TUPLE, see rewriteFoldOfTuple
   *  - FOLD_CONSTANT_STEP:
   *      (bag.fold (lambda ((t T) (acc S)) c) i X)
   *      ---> (ite (= X (as bag.empty (Bag T))) i c)
   *    for c reading neither t nor acc
   *  - CANONICAL_VARIABLE, see canonicalLambda
   */
  BagsRewriteResponse postRewriteFold(const TNode& n) const;
  /**
   * rewrites for n include:
   * - PARTITION_CONST: a bag.partition of a constant bag is evaluated
   */
  BagsRewriteResponse postRewritePartition(const TNode& n) const;
  /**
   * rewrites for n = ((_ table.aggr K) f i X) include:
   * - AGGREGATE_INTEGER_SUM, see rewriteAggregateIntegerSum
   * - AGGREGATE_OVER_JOIN, see rewriteAggregateOverJoin
   * - AGGREGATE_DUPLICATE_COLUMN, see rewriteAggregateDuplicateColumn
   * - NOT_NULL_COLUMNS, as for bag.map, in the steps of f
   * - AGGREGATE_SEMI_JOIN, see rewriteAggregateSemiJoin
   * - AGGREGATE_UNION_OF_MAPS, a union of maps by one g is the map of the
   *   union, which AGGREGATE_MAP then absorbs:
   *     ((_ table.aggr K) f i (bag.union_disjoint (bag.map g X1)
   *                                               (bag.map g X2)))
   *     ---> the AGGREGATE_MAP rewrite of
   *          ((_ table.aggr K) f i (bag.map g (bag.union_disjoint X1 X2)))
   * - AGGREGATE_FIXED_COLUMNS, the rows of every group have the constants
   *   the filter fixes, and a group column fixed splits no group:
   *     ((_ table.aggr 0 1) (lambda ((t T) (acc S)) b) i
   *                         (bag.filter (lambda ((s T))
   *                                       (= ((_ tuple.select 1) s) 5))
   *                                     X))
   *     ---> ((_ table.aggr 0) (lambda ((t T) (acc S))
   *                              b[((_ tuple.select 1) t) := 5])
   *                            i
   *                            (bag.filter (lambda ((s T))
   *                                          (= ((_ tuple.select 1) s) 5))
   *                                        X))
   * - AGGREGATE_NO_KEYS, one group of all of X, even an empty X:
   *     ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
   * - SORTED_KEYS, AGGREGATE_SORT_OUTPUT, AGGREGATE_MAP, see
   *   rewriteSortedKeys, rewriteAggregateSortOutput, rewriteAggregateOfMap
   * - CANONICAL_VARIABLE, see canonicalLambda
   * - AGGREGATE_CONST: an aggregate of constants is evaluated
   */
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   * rewrites for n include:
   * - PRODUCT_EMPTY:
   *     (table.product X (as bag.empty (Bag U))) ---> (as bag.empty (Bag V))
   *   and the same on the left
   * - PRODUCT_BAG_MAKE, see rewriteProductOfBagMake
   * - PRODUCT_MAP_LEFT, PRODUCT_MAP_RIGHT, PRODUCT_FILTER_LEFT and
   *   PRODUCT_FILTER_RIGHT, see rewriteProductOfMap and
   *   rewriteProductOfFilter
   * - PRODUCT_UNION_DISJOINT:
   *     (table.product (bag.union_disjoint A B) C)
   *     ---> (bag.union_disjoint (table.product A C) (table.product B C))
   *   and the same on the right
   * - PRODUCT_ASSOC:
   *     (table.product (table.product A B) C)
   *     ---> (table.product A (table.product B C))
   * - PRODUCT_SWAP, see rewriteProductSwap
   */
  BagsRewriteResponse postRewriteProduct(const TNode& n) const;

  /**
   * PROJECT_TO_MAP: a projection is a map, which the map rules then reach:
   *   ((_ table.project 1 0) X)
   *   ---> (bag.map (lambda ((t T)) ((_ tuple.project 1 0) t)) X)
   */
  BagsRewriteResponse postRewriteProject(const TNode& n) const;
  /** SORTED_KEYS for a table.group, see rewriteSortedKeys */
  BagsRewriteResponse postRewriteGroup(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // The normal form of select-project-join: maps above filters above
  // products. The functions compose lambdas only (see composable); a declared
  // function symbol is left to the rules above.
  // ---------------------------------------------------------------------------

  /**
   * FILTER_FILTER:
   *   (bag.filter (lambda ((s T)) p) (bag.filter (lambda ((t T)) q) A))
   *   ---> (bag.filter (lambda ((t T)) (and p[s := t] q)) A)
   */
  BagsRewriteResponse rewriteFilterOfFilter(const TNode& n) const;
  /**
   * FILTER_MAP:
   *   (bag.filter (lambda ((s U)) p) (bag.map (lambda ((t T)) e) A))
   *   ---> (bag.map (lambda ((t T)) e)
   *                 (bag.filter (lambda ((t T)) p[s := e]) A))
   */
  BagsRewriteResponse rewriteFilterOfMap(const TNode& n) const;
  /**
   * MAP_MAP:
   *   (bag.map (lambda ((s U)) e) (bag.map (lambda ((t T)) g) A))
   *   ---> (bag.map (lambda ((t T)) e[s := g]) A)
   */
  BagsRewriteResponse rewriteMapOfMap(const TNode& n) const;
  /**
   * PRODUCT_MAP_LEFT (left) and PRODUCT_MAP_RIGHT: the map of a factor is a
   * map of the product. With A and B of two columns,
   *   (table.product (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
   *                           A)
   *                  B)
   *   ---> (bag.map (lambda ((t V)) (tuple ((_ tuple.select 1) t)
   *                                        ((_ tuple.select 2) t)
   *                                        ((_ tuple.select 3) t)))
   *                 (table.product A B))
   */
  BagsRewriteResponse rewriteProductOfMap(const TNode& n, bool left) const;
  /**
   * PRODUCT_FILTER_LEFT (left) and PRODUCT_FILTER_RIGHT: the filter of a
   * factor is a filter of the product. With A of two columns,
   *   (table.product A (bag.filter (lambda ((s U)) (> ((_ tuple.select 1) s)
   *                                                  3))
   *                                B))
   *   ---> (bag.filter (lambda ((t V)) (> ((_ tuple.select 3) t) 3))
   *                    (table.product A B))
   */
  BagsRewriteResponse rewriteProductOfFilter(const TNode& n, bool left) const;
  /**
   * PRODUCT_SWAP, the factors in the order of their ids, B < A, under the map
   * that puts the columns back:
   *   (table.product A (table.product B C))
   *   ---> (bag.map perm (table.product B (table.product A C)))
   * with, for one column each,
   *   perm = (lambda ((t V)) (tuple ((_ tuple.select 1) t)
   *                                 ((_ tuple.select 0) t)
   *                                 ((_ tuple.select 2) t)))
   */
  BagsRewriteResponse rewriteProductSwap(const TNode& n) const;
  /**
   * PRODUCT_BAG_MAKE, a product with one row e, present once or when b:
   *   (table.product A (bag (tuple 7) (ite b 1 0)))
   *   ---> (bag.filter (lambda ((r V)) b)
   *                    (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
   *                                                    ((_ tuple.select 1) t)
   *                                                    7))
   *                             A))
   * side is the factor that is a bag of one row, 1 here.
   */
  BagsRewriteResponse rewriteProductOfBagMake(const TNode& n,
                                              size_t side) const;
  /**
   * MAP_SPLIT_CLOSED, a map whose body asks a question c about a bag that
   * reads no variable but the row (EXISTS or IN as a column):
   *   (bag.map (lambda ((t T)) b) X)
   *   ---> (bag.union_disjoint
   *          (bag.map (lambda ((t T)) b[c := true])
   *                   (bag.filter (lambda ((t T)) c) X))
   *          (bag.map (lambda ((t T)) b[c := false])
   *                   (bag.filter (lambda ((t T)) (not c)) X)))
   */
  BagsRewriteResponse rewriteMapSplitClosed(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // Aggregates ((_ table.aggr K) f i X): X grouped by its columns K, each
  // group folded by f from i. The translator adds a counter column to every
  // aggregate with group columns, (+ ((_ tuple.select c) acc) 1) from 0,
  // under a filter that tests it positive: SQL's GROUP BY makes no group of
  // an empty table, while table.aggr folds it to the row of initial values i.
  // ---------------------------------------------------------------------------

  /**
   * AGGREGATE_MAP, grouping the rows of a map by the columns it copies:
   *   ((_ table.aggr 0) (lambda ((s U) (acc S)) b) i
   *                     (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
   *                                                     ((_ tuple.select 0)
   *                                                      t)))
   *                              X))
   *   ---> ((_ table.aggr 2) (lambda ((t T) (acc S))
   *                            b[s := (tuple ((_ tuple.select 2) t)
   *                                          ((_ tuple.select 0) t))])
   *                          i X)
   */
  BagsRewriteResponse rewriteAggregateOfMap(const TNode& n) const;
  /**
   * SORTED_KEYS, the group columns sorted and without repeats:
   *   ((_ table.aggr 2 0 2) f i X) ---> ((_ table.aggr 0 2) f i X)
   *   ((_ table.group 1 0) X) ---> ((_ table.group 0 1) X)
   */
  BagsRewriteResponse rewriteSortedKeys(const TNode& n) const;
  /**
   * AGGREGATE_SORT_OUTPUT, the columns of the aggregate's rows in one order,
   * copies of group columns first:
   *   ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a1 ((_ tuple.select 0)
   *                                                      t)))
   *                     (tuple i1 i0) X)
   *   ---> (bag.map (lambda ((r S')) (tuple ((_ tuple.select 1) r)
   *                                         ((_ tuple.select 0) r)))
   *                 ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                     (tuple ((_ tuple.select 0) t) a1'))
   *                                   (tuple i0 i1) X))
   */
  BagsRewriteResponse rewriteAggregateSortOutput(const TNode& n) const;
  /**
   * FOLD_TUPLE, a fold of tuples whose components read their own
   * accumulator only:
   *   (bag.fold (lambda ((t T) (acc (Tuple Int Int))) (tuple b0 b1))
   *             (tuple i0 i1) X)
   *   ---> (tuple (bag.fold (lambda ((t T) (a Int)) b0') i0 X)
   *               (bag.fold (lambda ((t T) (a Int)) b1') i1 X))
   */
  BagsRewriteResponse rewriteFoldOfTuple(const TNode& n) const;
  /**
   * AGGREGATE_DEAD_COLUMNS, a column of the aggregate nothing reads:
   *   (bag.map h ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
   *                                (tuple i0 i1 i2) X))
   *   ---> (bag.map h' ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                        (tuple a0 a2'))
   *                                      (tuple i0 i2) X))
   * also under a filter between the map and the aggregate
   */
  BagsRewriteResponse rewriteAggregateDeadColumns(const TNode& n) const;
  /**
   * AGGREGATE_COLLAPSE, an aggregate over a union of aggregates by the same
   * columns, which merges them:
   *   (bag.map h (bag.filter Q ((_ table.aggr K) g j
   *     (bag.union_disjoint (bag.map pi (bag.filter Qi ((_ table.aggr K) f i0
   *                                                     X1)))
   *                         (bag.map pi (bag.filter Qi ((_ table.aggr K) f i0
   *                                                     X2)))))))
   *   ---> (bag.map h' (bag.filter Q' ((_ table.aggr K) f i0
   *                                     (bag.union_disjoint X1 X2))))
   * for g merging f's columns (a sum of counts or sums, a minimum of
   * minimums, a maximum of maximums)
   */
  BagsRewriteResponse rewriteAggregateCollapse(const TNode& n) const;
  /**
   * AGGREGATE_INTEGER_SUM, a sum of integers read as reals is the integer
   * sum read as a real once:
   *   ((_ table.aggr 0) f i X)
   *   ---> (bag.map (lambda ((r U)) (tuple .. (ite (= (as nullable.null
   *                                                     (Nullable Int))
   *                                                    ((_ tuple.select 1) r))
   *                                                 (as nullable.null
   *                                                   (Nullable Real))
   *                                                 (nullable.some
   *                                                   (to_real (nullable.val
   *                                                     ((_ tuple.select 1)
   *                                                      r)))))))
   *                 ((_ table.aggr 0) f' i' X))
   * for column 1 of f the sum of (to_real ..) of an integer column
   */
  BagsRewriteResponse rewriteAggregateIntegerSum(const TNode& n) const;
  /**
   * AGGREGATE_ROLLUP, an aggregate of an aggregate (Calcite's form of
   * DISTINCT aggregates) as a join of an aggregate over X with one over the
   * distinct (keys, c) of X:
   *   (bag.map h (bag.filter Q ((_ table.aggr Ko) g j
   *                               (bag.filter P ((_ table.aggr K) f i X)))))
   *   ---> (bag.map h (bag.filter Q (bag.map rows
   *          (bag.filter (lambda ((p W)) (= keys of A keys of B))
   *            (table.product (bag.filter counter ((_ table.aggr Ko) fA iA
   *                                                X))
   *                           (bag.filter counter ((_ table.aggr Ko) fB iB
   *                             (bag.setof (bag.map (lambda ((t T))
   *                                          (tuple .. c)) X)))))))))
   */
  BagsRewriteResponse rewriteAggregateRollup(const TNode& n) const;
  /**
   * AGGREGATE_SETOF_IDEMPOTENT and AGGREGATE_JOIN_MERGE, for aggregates that
   * are components of a product under (bag.map h (bag.filter P ..)):
   *   ((_ table.aggr 0) f i (bag.setof Y)) ---> ((_ table.aggr 0) f i Y)
   * when f computes only copies, minimums, maximums and a counter nothing
   * reads but (>= c 1); and two aggregates over one X by one K, joined on
   * their copies of the group columns, are one:
   *   (bag.map h (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
   *                                             ((_ tuple.select 3) p)))
   *                          (table.product ((_ table.aggr 0) fa ia X)
   *                                         ((_ table.aggr 0) fb ib X))))
   *   ---> (bag.map h' ((_ table.aggr 0) fm im X))
   * when the two seed the copies alike
   */
  BagsRewriteResponse rewriteAggregateJoinMerge(const TNode& n) const;
  /**
   * AGGREGATE_UNION_SPLIT, an aggregate over a union of parts each of which
   * gives the arguments of some columns and null to the others, all with the
   * same keys, as the join of the parts' aggregates:
   *   (bag.map h (bag.filter Q ((_ table.aggr 0) f i
   *                               (bag.union_disjoint U1 U2))))
   *   ---> (bag.map h (bag.filter Q (bag.map rows
   *          (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
   *                                         ((_ tuple.select 3) p)))
   *            (table.product ((_ table.aggr 0) f1 i1 U1)
   *                           ((_ table.aggr 0) f2 i2 U2))))))
   */
  BagsRewriteResponse rewriteAggregateUnionSplit(const TNode& n) const;
  /**
   * AGGREGATE_UNION_DISJOINT_KEYS, an aggregate over a union of parts no two
   * of which share a key value:
   *   (bag.map h (bag.filter Q ((_ table.aggr 0) f i
   *                               (bag.union_disjoint U1 U2))))
   *   ---> (bag.map h (bag.filter Q (bag.union_disjoint
   *                                   ((_ table.aggr 0) f i U1)
   *                                   ((_ table.aggr 0) f i U2))))
   */
  BagsRewriteResponse rewriteAggregateUnionDisjointKeys(const TNode& n) const;
  /**
   * Eager aggregation, an aggregate pushed through a join: for f folding the
   * rows of J = (bag.filter P (table.product X Y)) grouped by K, returns
   * (SEXPR f3 J' (SEXPR k..)) where J' joins the aggregates of X and of Y by
   * their join and group columns, f3 folds the pairs of groups (a sum of X
   * times the rows of Y, a minimum of X, a count of X times the rows of Y),
   * and k.. are the columns of J' that hold K; null when J or f is not of
   * that shape. See the example in the .cpp.
   */
  Node eagerAggregation(const Node& f,
                        const Node& init,
                        const Node& J,
                        const std::vector<uint32_t>& K) const;
  /**
   * AGGREGATE_OVER_JOIN, see eagerAggregation:
   *   ((_ table.aggr K) f i (bag.filter P (table.product X Y)))
   *   ---> ((_ table.aggr K') f3 i J')
   */
  BagsRewriteResponse rewriteAggregateOverJoin(const TNode& n) const;
  /**
   * PRODUCT_AGGREGATE_DEAD_COLUMN, a column of an aggregate component that
   * nothing reads:
   *   (bag.map h (table.product ((_ table.aggr 0) (lambda ((t T) (acc S))
   *                                                 (tuple a0 a1 a2))
   *                                               (tuple i0 i1 i2) X)
   *                             Y))
   *   ---> (bag.map h' (table.product ((_ table.aggr 0)
   *                                     (lambda ((t T) (acc S'))
   *                                       (tuple a0 a2'))
   *                                     (tuple i0 i2) X)
   *                                   Y))
   * also under a filter between the map and the product
   */
  BagsRewriteResponse rewriteProductAggregateColumns(const TNode& n) const;
  /**
   * AGGREGATE_DUPLICATE_COLUMN, two columns that fold alike are one, read
   * twice:
   *   ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 s1 s2))
   *                     (tuple i0 i1 i1) X)
   *   ---> (bag.map (lambda ((r U)) (tuple ((_ tuple.select 0) r)
   *                                        ((_ tuple.select 1) r)
   *                                        ((_ tuple.select 1) r)))
   *                 ((_ table.aggr 0) (lambda ((t T) (acc U)) (tuple a0 s1))
   *                                   (tuple i0 i1) X))
   */
  BagsRewriteResponse rewriteAggregateDuplicateColumn(const TNode& n) const;
  /**
   * The group columns h reads of the groups some row reached, as a map over
   * the rows: for h reading copies of group columns of
   *   F = (bag.filter (lambda ((r V)) (>= ((_ tuple.select c) r) 1))
   *                   ((_ table.aggr K) f i X))
   * the term (bag.map h' X) with h' reading those columns of X's rows, to put
   * under a bag.setof; null otherwise. With covering, h must read all of K.
   */
  Node keysOfReachedGroups(const Node& h, const Node& F, bool covering) const;
  /**
   * FILTER_AGGREGATE, a conjunct on the copies of group columns filters the
   * rows of X before grouping:
   *   (bag.filter (lambda ((r V)) (and (> ((_ tuple.select 0) r) 3) q))
   *               ((_ table.aggr 0) f i X))
   *   ---> (bag.filter (lambda ((r V)) q)
   *                    ((_ table.aggr 0) f i
   *                                      (bag.filter (lambda ((t T))
   *                                                    (> ((_ tuple.select 0)
   *                                                          t)
   *                                                       3))
   *                                                  X)))
   * when f copies column 0 of X to column 0, and q, which stays, rejects the
   * row of initial values (see rejectsInitialRow)
   */
  BagsRewriteResponse rewriteFilterOfAggregate(const TNode& n) const;
  /**
   * For A = ((_ table.aggr K) f i X) with K containing a key of X (see
   * rowKeys): the rows of the groups some row reached, every group one row
   * of X folded once,
   *   (bag.map (lambda ((t T)) b[acc := i]) X)
   * for f = (lambda ((t T) (acc S)) b); null otherwise. They are the
   * aggregate's rows but for the row of initial values of an empty X, so
   * AGGREGATE_KEYED uses them where that row is dropped.
   */
  Node keyedAggregateRows(const Node& A) const;
  /** Whether n, a formula, rewrites to false */
  bool rewritesToFalse(const Node& n) const;
  /**
   * Whether the predicate P is false on the row of initial values i, the one
   * row an aggregate of an empty table has: (P i) rewrites to false, as for
   *   P = (lambda ((r V)) (>= ((_ tuple.select 2) r) 1))
   *   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
   */
  bool rejectsInitialRow(const Node& P, const Node& i) const;
  /**
   * AGGREGATE_SEMI_JOIN, SEMI_JOIN under an aggregate (see rewriteSemiJoin):
   *   ((_ table.aggr K) f i (bag.filter p (table.product A B)))
   *   ---> ((_ table.aggr K') f' i
   *          (bag.filter (lambda ((a U))
   *                        (and pA (not (= (bag.filter (lambda ((b W)) pAB) B)
   *                                        (as bag.empty (Bag W))))))
   *                      A))
   * for B a set whose row p fixes, read by f and K only through columns p
   * equates to columns of A
   */
  BagsRewriteResponse rewriteAggregateSemiJoin(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // Sets, keys and semi-joins
  // ---------------------------------------------------------------------------

  /**
   * SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, the set of a map:
   *   (bag.setof (bag.map (lambda ((t T)) c) Y))
   *   ---> (bag c (ite (= Y (as bag.empty (Bag T))) 0 1))
   *   (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
   *                                              ((_ tuple.select 0) t)))
   *                       Y))
   *   ---> (bag.map (lambda ((r U)) (tuple ((_ tuple.select 1) r)
   *                                        ((_ tuple.select 0) r)))
   *                 (bag.setof (bag.map (lambda ((t T))
   *                                       (tuple ((_ tuple.select 0) t)
   *                                              ((_ tuple.select 2) t)))
   *                                     Y)))
   *   (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t) 5)) Y))
   *   ---> (bag.map (lambda ((r U)) (tuple ((_ tuple.select 0) r) 5))
   *                 (bag.setof (bag.map (lambda ((t T))
   *                                       (tuple ((_ tuple.select 1) t)))
   *                                     Y)))
   */
  BagsRewriteResponse rewriteSetofOfMap(const TNode& n) const;
  /**
   * SEMI_JOIN, a join with a set B whose row the join equations fix (all its
   * columns, or a key) and whose columns the map does not read, as a filter
   * by the existence of the matching row. With the key {0} of Z,
   *   (bag.map (lambda ((t V)) (tuple ((_ tuple.select 1) t)))
   *            (bag.filter (lambda ((t V)) (= ((_ tuple.select 0) t)
   *                                           ((_ tuple.select 2) t)))
   *                        (table.product Y Z)))
   *   ---> (bag.map (lambda ((a U)) (tuple ((_ tuple.select 1) a)))
   *                 (bag.filter (lambda ((a U))
   *                               (not (= (bag.filter (lambda ((b W))
   *                                                     (= ((_ tuple.select 0)
   *                                                          a)
   *                                                        ((_ tuple.select 0)
   *                                                          b)))
   *                                                   Z)
   *                                       (as bag.empty (Bag W)))))
   *                             Y))
   * Called with side 0 only; every component of the product is tried.
   */
  BagsRewriteResponse rewriteSemiJoin(const TNode& n, size_t side) const;
  /**
   * SETOF_PUSHDOWN, under duplicate removal each component of a product is
   * the set of the columns read of it:
   *   (bag.setof (bag.map g (bag.filter p (table.product C1 C2))))
   *   ---> (bag.setof (bag.map g' (bag.filter p'
   *          (table.product (bag.setof (bag.map pi1 (bag.filter p1 C1)))
   *                         (bag.setof (bag.map pi2 (bag.filter p2 C2)))))))
   */
  BagsRewriteResponse rewriteSetofPushdown(const TNode& n) const;
  /**
   * FILTER_INTO_SETOF, a conjunct on a set component only goes into it:
   *   (bag.filter (lambda ((t V)) (and c q)) (table.product X (bag.setof Z)))
   *   ---> (bag.filter (lambda ((t V)) q)
   *                    (table.product X (bag.setof (bag.filter
   *                                                  (lambda ((v U)) c')
   *                                                  Z))))
   */
  BagsRewriteResponse rewriteFilterIntoSetofComponent(const TNode& n) const;
  /**
   * SEMI_TO_INTERSECTION, a projected semi-join as an intersection of sets,
   * or null:
   *   (bag.map g (bag.filter (lambda ((x T))
   *                            (and (>= (bag.count (pi x) M) 1) q r))
   *                          X))
   *   ---> (bag.map h (bag.inter_min
   *                     (bag.setof (bag.filter q' (bag.map pi
   *                                                 (bag.filter r X))))
   *                     (bag.setof (bag.filter q' M))))
   * under duplicate removal (underSetof), or when the projected rows are a
   * set; g is h applied to the result of pi
   */
  Node semiJoinToIntersection(const Node& n, bool underSetof) const;
  /**
   * FILTER_EQUI_JOIN_SETS, a join of two sets of one row sort on all their
   * columns is their intersection, twice:
   *   (bag.filter (lambda ((t V)) (and (= ((_ tuple.select 0) t)
   *                                       ((_ tuple.select 2) t))
   *                                    (= ((_ tuple.select 1) t)
   *                                       ((_ tuple.select 3) t))
   *                                    q))
   *               (table.product X Y))
   *   ---> (bag.filter (lambda ((t V)) q)
   *                    (bag.map (lambda ((w T)) (tuple ((_ tuple.select 0) w)
   *                                                    ((_ tuple.select 1) w)
   *                                                    ((_ tuple.select 0) w)
   *                                                    ((_ tuple.select 1) w)))
   *                             (bag.inter_min X Y)))
   */
  BagsRewriteResponse rewriteEquiJoinOfSets(const TNode& n) const;
  /**
   * Whether no element of X occurs twice, syntactically: a bag.setof, a table
   * with a key, a filter over a set, a product of sets, or a map over one of
   * these that keeps, of every component, all its columns or a key.
   */
  bool isSet(const Node& X) const;
  /**
   * The keys of B read off its structure: a table's declared keys, kept by
   * filters, intersections and differences, by maps that keep their columns,
   * and combined by products; all the columns of a bag.setof; the group
   * columns an aggregate's rows copy. With the key {0} of X and of Y, and X
   * of two columns, (table.product X Y) has the key {0, 2}. Every key found
   * makes B a set.
   */
  std::vector<std::set<uint32_t>> rowKeys(const Node& B) const;
  /**
   * The keys of a table constant (see BagsKeysAttribute in the .cpp), or of
   * a filter over one: {{0, 2}, {1}} for keys {0, 2} and {1}.
   */
  std::vector<std::set<uint32_t>> keysOf(const Node& B) const;
  /**
   * The conditions every element w of A satisfies, read off A's filters,
   * through projections onto distinct columns, and through the copies of
   * group columns of an aggregate whose counter a filter tests: for
   *   A = (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
   *                (bag.filter (lambda ((s T)) (> ((_ tuple.select 1) s) 3))
   *                            X))
   * out gets (> ((_ tuple.select 0) w) 3).
   */
  void elementConditions(const Node& A,
                         const Node& w,
                         std::set<Node>& out) const;
  /**
   * FILTER_KNOWN_MEMBERSHIP: body without the membership conjuncts that
   * every row t of A satisfies, or that another conjunct implies: with
   * A = (table.product X Y),
   *   (and (>= (bag.count (tuple ((_ tuple.select 0) t))
   *                       (bag.map (lambda ((s T))
   *                                  (tuple ((_ tuple.select 0) s)))
   *                                X))
   *            1)
   *        q)
   *   ---> q
   */
  Node dropKnownMemberships(const Node& body,
                            const Node& t,
                            const Node& A) const;

  // ---------------------------------------------------------------------------
  // Facts: keys and NOT NULL columns of table constants
  // ---------------------------------------------------------------------------

  /**
   * Record the key a key assertion states: for n =
   *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
   * either way round, or with the projection as a bag.map, X gets the key
   * {0, 2} (see BagsKeysAttribute in the .cpp), and the assertion's bag.setof
   * is not rewritten (BagsKeyTermAttribute). Called for top-level assertions
   * only, see recordFacts.
   */
  void recordKey(const TNode& n) const;
  /**
   * Record the never-null column a not-null assertion states: for n =
   *   (= (bag.filter (lambda ((t T))
   *                    (= (as nullable.null (Nullable Int))
   *                       ((_ tuple.select 1) t)))
   *                  X)
   *      (as bag.empty (Bag T)))
   * either way round, column 1 of X is never null (BagsNotNullAttribute in
   * the .cpp), and the filter is not rewritten (BagsKeyTermAttribute).
   * Called for top-level assertions only, see recordFacts.
   */
  void recordNotNull(const TNode& n) const;
  /**
   * Whether t is never null, given the columns nx of the row x and nacc of
   * the accumulator acc that are never null: true for (nullable.some a), for
   * ((_ tuple.select k) x) with k in nx, for an ite of such terms, and for a
   * fold seeded with (nullable.some a) whose step keeps it so. x and acc may
   * be null.
   */
  bool nonNullTerm(const Node& t,
                   const Node& x,
                   const std::set<uint32_t>& nx,
                   const Node& acc,
                   const std::set<uint32_t>& nacc) const;
  /**
   * The never-null columns of the rows of the aggregate B: those whose seed
   * is never null and whose step keeps them so; with reached, for the groups
   * a row reached, also those the step makes never null from these.
   */
  std::set<uint32_t> aggregateNonNull(const Node& B, bool reached) const;
  /**
   * The columns of B's rows that are never null, read off its structure:
   * the NOT NULL columns of a table constant, kept by filters, maps, unions
   * (of both sides), products, aggregates (see aggregateNonNull), and those a
   * filter tests with (nullable.is_some ((_ tuple.select k) t)). Cached in
   * d_nonNull.
   */
  std::set<uint32_t> nonNullColumns(const Node& B) const;
  /**
   * body with the null tests of the never-null columns cols of x decided:
   * with cols {1},
   *   (and (nullable.is_some ((_ tuple.select 1) x)) p) is (and true p)
   *   (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x)) is false
   */
  Node assumeNonNull(const Node& body,
                     const Node& x,
                     const std::set<uint32_t>& cols) const;

  // ---------------------------------------------------------------------------
  // Counters, steps of aggregates, and the groups a row reached
  // ---------------------------------------------------------------------------

  /**
   * The column c of the rows of an aggregate ((_ table.aggr K) f i X) that
   * counts the rows of each group, (+ ((_ tuple.select c) acc) 1) from 0,
   * when the filter predicate P has the conjunct
   * (>= ((_ tuple.select c) r) 1); -1 otherwise.
   */
  int counterColumn(const Node& P, const Node& f, const Node& i) const;
  /**
   * For the step of a column of an aggregate over acc, its accumulator
   * column: 0 for SQL's SUM, 1 for MIN, 2 for MAX, which skip nulls and are
   * null over no value,
   *   (ite (= (as nullable.null (Nullable Int)) A)
   *        acc
   *        (ite (= (as nullable.null (Nullable Int)) acc) A C))
   * with C the sum, minimum or maximum of A and acc; -1 for anything else.
   * arg is set to A.
   */
  int nullAwareStepKind(const Node& step, const Node& acc, Node& arg) const;
  /**
   * Whether step counts rows from seed (nullable.some 0): COUNT(*),
   * (nullable.some (+ (nullable.val acc) 1)), or COUNT(x), an ite that keeps
   * acc on the rows where x is null and counts the others.
   */
  bool isCountStep(const Node& step, const Node& acc, const Node& seed) const;
  /**
   * For a filter P over the product of comps, whose columns start at starts:
   * per component, the conjunct of P that tests its counter positive (-1
   * when none), in test, and whether its groups are reached: 1 when tested,
   * 2 when joined on all its group columns with a reached aggregate whose
   * input has the same key values, 0 otherwise. The rows of initial values
   * of a reached component are in no row that passes P.
   */
  std::vector<int> reachedComponents(const Node& P,
                                     const std::vector<Node>& comps,
                                     const std::vector<size_t>& starts,
                                     std::vector<int>& test) const;
  /**
   * FILTER_IMPLIED_COUNTER, a counter test that a join with a reached
   * aggregate over the same key values implies goes (see reachedComponents):
   *   (bag.filter (lambda ((t V)) (and (>= ((_ tuple.select 2) t) 1)
   *                                    (>= ((_ tuple.select 5) t) 1)
   *                                    (= ((_ tuple.select 0) t)
   *                                       ((_ tuple.select 3) t))))
   *               (table.product G1 G2))
   *   ---> (bag.filter (lambda ((t V)) (and (>= ((_ tuple.select 2) t) 1)
   *                                         (= ((_ tuple.select 0) t)
   *                                            ((_ tuple.select 3) t))))
   *                    (table.product G1 G2))
   * for G1 and G2 aggregates over one X by its column 0
   */
  BagsRewriteResponse dropImpliedCounters(const TNode& n) const;
  /**
   * FILTER_JOIN_TRANSITIVE, a condition the rows of one side of a join
   * satisfy on a column the join equates holds of the class's first column:
   *   (bag.filter (lambda ((t V)) (= ((_ tuple.select 0) t)
   *                                  ((_ tuple.select 2) t)))
   *               (table.product X (bag.filter (lambda ((s U))
   *                                              (> ((_ tuple.select 0) s)
   *                                                 3))
   *                                            Y)))
   *   ---> (bag.filter (lambda ((t V)) (and (= ((_ tuple.select 0) t)
   *                                            ((_ tuple.select 2) t))
   *                                         (> ((_ tuple.select 0) t) 3)))
   *                    (table.product X (bag.filter .. Y)))
   */
  BagsRewriteResponse rewriteJoinTransitiveConditions(const TNode& n) const;
  /**
   * The columns a filter predicate fixes to constants: {1 -> 5} for
   * (lambda ((t T)) (and (= ((_ tuple.select 1) t) 5) q)).
   */
  std::map<uint32_t, Node> fixedColumns(const Node& p) const;
  /**
   * The constant columns of the groups a counter filter F over an aggregate
   * keeps: those its step sets to a constant, and those it keeps at their
   * constant seed.
   */
  std::map<uint32_t, Node> reachedGroupConstants(const Node& F) const;
  /**
   * body with the columns of var that fixed maps read as their constants:
   * ((_ tuple.select 1) var) read as 5 for {1 -> 5}.
   */
  Node readFixed(const Node& body,
                 const Node& var,
                 const std::map<uint32_t, Node>& fixed) const;

  // ---------------------------------------------------------------------------
  // Emptiness tests and SQL's three-valued truth in lambda bodies
  // ---------------------------------------------------------------------------

  /**
   * The formula an emptiness atom of a filter stands for, decorrelated, or
   * null (EQ_EMPTY_FILTER_DECORRELATE): for F over the rows s of X, inside a
   * lambda over a row r,
   *   (= (as bag.empty (Bag T))
   *      (bag.filter (lambda ((s T)) (and c q (= ((_ tuple.select 1) s)
   *                                              ((_ tuple.select 0) r))))
   *                  X))
   *   ---> (or (not c)
   *            (not (>= (bag.count (tuple ((_ tuple.select 0) r))
   *                                (bag.map (lambda ((s T))
   *                                           (tuple ((_ tuple.select 1) s)))
   *                                         (bag.filter (lambda ((s T)) q)
   *                                                     X)))
   *                     1)))
   * for c reading no s and q only s.
   */
  Node rewriteEmptyFilter(const Node& F) const;
  /**
   * An atom of a lambda body that asks about a bag, as the formula it stands
   * for, or null: a membership in an intersection or a bag.setof, an
   * emptiness of a filter (see rewriteEmptyFilter), of a counter filter over
   * an aggregate, of an intersection whose filters fix its element, or of a
   * (bag x c), and the count of a fold that counts rows being 0.
   */
  Node emptinessAtom(const Node& atom) const;
  /**
   * body with its atoms outside inner binders replaced by emptinessAtom:
   * those under an inner binder belong to that lambda's own filter or map.
   */
  Node normalizeEmptiness(const Node& body) const;
  /**
   * The formula X = (nullable.some true) for a nullable Boolean X built of
   * ites over (nullable.some b) and null, or null when X is not one: (ite c b
   * false) for X = (ite c (nullable.some b) (as nullable.null (Nullable
   * Bool))).
   */
  Node truthOf(const Node& X) const;
  /**
   * FILTER_NULLABLE_TRUTH: body with the conjuncts (nullable.is_some X) and
   * (nullable.val X) replaced by truthOf(X), the one formula they say.
   */
  Node normalizeTruth(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Canonical lambdas: one variable per role and type, named after the
  // lambda's alpha key, so that alpha-equivalent lambdas are one node, which
  // the solver purifies into one function symbol
  // ---------------------------------------------------------------------------

  /** The variable of the accumulator of an aggregate's function, per type */
  Node accumulatorVariable(TypeNode type) const;
  /**
   * CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N the
   * id of f's alpha key, when that is safe:
   *   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
   *   ---> (lambda ((t_N T)) (> ((_ tuple.select 0) t_N) 3))
   * f's body is first simplified, see simplifyIteSame.
   */
  Node canonicalLambda(const Node& f) const;
  /**
   * A node equal for alpha-equivalent f: f with every variable it binds
   * replaced by a placeholder for its binding depth, every free variable by
   * one placeholder per type, the arguments of commutative operators sorted
   * and arithmetic atoms oriented over the placeholders. Cached in
   * d_alphaKeys.
   */
  Node alphaKey(const Node& f) const;
  /**
   * The alpha key of root, with bound mapping the variables of the binders
   * that enclose root to their placeholders, at binding depth depth.
   */
  Node alphaKeyScope(TNode root,
                     std::unordered_map<TNode, Node>& bound,
                     size_t depth) const;
  /** the alpha keys computed so far */
  mutable std::unordered_map<Node, Node> d_alphaKeys;
  /** cache of nonNullColumns, cleared when a not-null fact is recorded */
  mutable std::unordered_map<Node, std::set<uint32_t>> d_nonNull;
  /**
   * body with (ite (= a b) b a) replaced by a and (ite (= a b) a b) by b,
   * which the translator's null-aware steps leave once an accumulator is
   * known.
   */
  Node simplifyIteSame(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Lambdas and rows
  // ---------------------------------------------------------------------------

  /**
   * The columns a projection lambda selects, in order: {2, 0} for
   * (lambda ((t T)) (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t))) or
   * (lambda ((t T)) ((_ tuple.project 2 0) t)); empty when f is not one.
   */
  std::vector<uint32_t> projectionIndices(const Node& f) const;
  /**
   * (f x) beta-reduced: (> ((_ tuple.select 1) (tuple a b)) 3), which the
   * rewriter simplifies to (> b 3), for f = (lambda ((s T))
   * (> ((_ tuple.select 1) s) 3)) and x = (tuple a b); (f x) as an
   * application when f is not a lambda; null when the substitution would
   * capture a variable.
   */
  Node applyFunction(const Node& f, const Node& x) const;
  /** f as a lambda when it is a function array constant, else f */
  Node asLambda(const Node& f) const;
  /** whether v occurs free in n */
  bool occursFree(const Node& n, const Node& v) const;
  /** The one bound row variable of a tuple type, row_N */
  Node rowVariable(TypeNode tupleType) const;
  /** Whether a closure in body binds var */
  bool bindsVariable(const Node& body, const Node& var) const;
  /** (lambda ((var T)) body) */
  Node mkLambda(const Node& var, const Node& body) const;
  /** whether f is a lambda of one variable, which the rules may compose */
  bool composable(const Node& f) const;
  /**
   * The variable and body of the lambda (lambda ((t T)) body) a function of
   * type T -> S stands for: the lambda's own, or the row variable t of T and
   * (f t) for a function that is not a lambda.
   */
  std::pair<Node, Node> lambdaOf(const Node& f) const;
  /**
   * The tuple positions a lambda body reads of its bound variable, as
   * (_ tuple.select i) applications: {0, 2} for (> ((_ tuple.select 0) t)
   * ((_ tuple.select 2) t)); false when the variable is used any other way.
   */
  bool readPositions(const Node& body,
                     const Node& var,
                     std::set<uint32_t>& positions) const;

 private:
  /** the integer constants 0 and 1 */
  Node d_zero;
  Node d_one;
  /**
   * Pointer to the rewriter. NOTE this is a cyclic dependency, and should
   * be removed.
   */
  Rewriter* d_rewriter;
  /** Reference to the rewriter statistics. */
  HistogramStat<Rewrite>* d_statistics;
  /** whether the logic has higher-order terms, see the constructor */
  bool d_higherOrder;

}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H */

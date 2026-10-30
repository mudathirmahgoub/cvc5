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
 * Besides evaluating constants and simplifying the bag operators, it brings
 * the terms of relational algebra over tables (bags of tuples) to a normal
 * form, so that the encodings of two equivalent SQL queries often become one
 * term. A query SELECT h FROM X1, X2 WHERE P becomes
 *
 *   (bag.map h (bag.filter P (table.product X1 X2)))
 *
 * with maps above filters above products, and every lambda over the same
 * variables (see canonicalLambda).
 *
 * Each rule is a Rewrite id, documented with an example in rewrites.h. The
 * functions below that apply several rules list them; a function that
 * implements a rule is documented with its conditions. Some rules read facts
 * about the tables of the problem, their keys and NOT NULL columns, that
 * top-level assertions state (see recordFacts).
 */
class BagsRewriter : public TheoryRewriter
{
 public:
  /**
   * With higherOrder false, for a logic without higher-order terms, the rules
   * that build a lambda where the term has none do not apply, since the theory
   * of uninterpreted functions rejects lambdas there:
   * - FILTER_MAP, MAP_MAP and PROJECT_TO_MAP
   * - FILTER_FILTER, PRODUCT_MAP_*, PRODUCT_FILTER_* and PRODUCT_SWAP
   * - COUNT_MAP_CONST_PROBE over a table constant
   * The rewriter does not know the logic, so the default is false: the owner
   * of the rewriter passes true for a higher-order logic.
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
   * TABLE_PRODUCT, TABLE_PROJECT and TABLE_AGGREGATE; a node
   * whose children are constants is evaluated. See the rewrite rules for
   * these kinds below.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, BAG_SUBBAG, BAG_MEMBER.
   * See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

  /**
   * Record the facts that a top-level assertion states about a table constant,
   * which some rules read: a key of the table (see recordKey) or a NOT NULL
   * column (see recordNotNull), also in the conjuncts of a conjunction. For
   * X : (Bag (Tuple Int (Nullable Int))), the assertions
   *
   *   (assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
   *
   *   (assert (= (bag.filter
   *                (lambda ((t (Tuple Int (Nullable Int))))
   *                  (= ((_ tuple.select 1) t)
   *                     (as nullable.null (Nullable Int))))
   *                X)
   *              (as bag.empty (Bag (Tuple Int (Nullable Int))))))
   *
   * state that column 0 is a key of X (no two rows agree on it) and that column
   * 1 is never null. The bags-facts preprocessing pass calls this on every
   * top-level assertion, before any of them is rewritten. Facts are never read
   * off an equality the rewriter meets, which may be under a negation.
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
   * The rules for (bag.count e X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - COUNT_EMPTY and COUNT_BAG_MAKE
   * - COUNT_MAP_CONST_PROBE, for e with a constant column
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   * The rules for (bag.setof X), each a Rewrite id with an example in
   * rewrites.h, except for the bag.setof of a key assertion
   * (see BagsKeyTermAttribute in the .cpp):
   *
   * - SETOF_BAG_MAKE
   * - SETOF_MAP_CONSTANT (rewriteSetofOfMap)
   * - SETOF_PROJECTION_SORT (rewriteSetofOfMap)
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
   * The rules for an equality of bags (= A B), each a Rewrite id with an
   * example in rewrites.h:
   *
   * - EQ_EMPTY_ARG, for a map or a bag.setof equal to the empty bag
   * - EQ_REFL, EQ_CONST_FALSE and EQ_SYM
   */
  BagsRewriteResponse postRewriteEqual(const TNode& n) const;

  /**
   * The rules for (bag.map f X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - MAP_IDENTITY
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - MAP_CONST, MAP_BAG_MAKE and MAP_UNION_DISJOINT
   * - MAP_MAP, for X a map (rewriteMapOfMap)
   * - EQ_EMPTY_FILTER_DECORRELATE (normalizeEmptiness)
   * - AGGREGATE_DEAD_COLUMNS, for X an aggregate (rewriteAggregateDeadColumns)
   * - AGGREGATE_UNION_DISJOINT_KEYS (rewriteAggregateUnionDisjointKeys)
   * - MAP_EQUAL_COLUMNS, for X a filter
   * - MAP_FIXED_COLUMNS, for X a filter (fixedColumns, readFixed)
   * - SEMI_JOIN (rewriteSemiJoin)
   * - CANONICAL_VARIABLE (canonicalLambda)
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   * The rules for (bag.filter p X), each a Rewrite id with an example in
   * rewrites.h, except for the filter of a NOT NULL assertion
   * (see BagsKeyTermAttribute in the .cpp):
   *
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - FILTER_TRUE and FILTER_FALSE
   * - EQ_EMPTY_FILTER_DECORRELATE (normalizeEmptiness)
   * - FILTER_NULLABLE_TRUTH (normalizeTruth)
   * - FILTER_CONFLICTING_CONSTANTS
   * - FILTER_KNOWN_MEMBERSHIP (dropKnownMemberships)
   * - FILTER_SORT_CONJUNCTS
   * - CANONICAL_VARIABLE (canonicalLambda)
   * - FILTER_SPLIT_CLOSED
   * - FILTER_CONST, FILTER_BAG_MAKE and FILTER_UNION_DISJOINT
   * - FILTER_FILTER, for X a filter (rewriteFilterOfFilter)
   * - FILTER_MAP, for X a map (rewriteFilterOfMap)
   * - AGGREGATE_KEYED, for X an aggregate or a product of them
   *   (keyedAggregateRows)
   * - FILTER_SETOF, for X a bag.setof
   * - FILTER_JOIN_TRANSITIVE (rewriteJoinTransitiveConditions)
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
   * The rules for (bag.fold f i X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - FOLD_CONST and FOLD_BAG, for X a constant or (bag x c)
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - FOLD_MAP
   * - FOLD_TUPLE (rewriteFoldOfTuple)
   * - FOLD_CONSTANT_STEP
   * - FOLD_UNION_DISJOINT
   * - CANONICAL_VARIABLE (canonicalLambda)
   */
  BagsRewriteResponse postRewriteFold(const TNode& n) const;
  /**
   * rewrites for n include:
   * - PARTITION_CONST: a bag.partition of a constant bag is evaluated
   */
  BagsRewriteResponse postRewritePartition(const TNode& n) const;
  /**
   * The rules for ((_ table.aggr K) f i X), each a Rewrite id with an example
   * in rewrites.h:
   *
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - AGGREGATE_NO_KEYS
   * - AGGREGATE_SORT_OUTPUT (rewriteAggregateSortOutput)
   * - CANONICAL_VARIABLE (canonicalLambda)
   * - AGGREGATE_MAP, for X a map (rewriteAggregateOfMap)
   * - AGGREGATE_CONST
   */
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   * The rules for (table.product A B), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - PRODUCT_EMPTY
   * - PRODUCT_MAP_LEFT and PRODUCT_MAP_RIGHT (rewriteProductOfMap)
   * - PRODUCT_FILTER_LEFT and PRODUCT_FILTER_RIGHT (rewriteProductOfFilter)
   * - PRODUCT_UNION_DISJOINT
   * - PRODUCT_ASSOC
   * - PRODUCT_SWAP (rewriteProductSwap)
   */
  BagsRewriteResponse postRewriteProduct(const TNode& n) const;

  /**
   * PROJECT_TO_MAP, the rule for ((_ table.project J) X), with an example at
   * its Rewrite id in rewrites.h.
   */
  BagsRewriteResponse postRewriteProject(const TNode& n) const;

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
   * FILTER_MAP, a filter of a map as a map of a filter. The map's function must
   * be a lambda (see composable).
   */
  BagsRewriteResponse rewriteFilterOfMap(const TNode& n) const;
  /**
   * MAP_MAP, a map of a map as one map, by the composition. Both functions must
   * be lambdas (see composable).
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

  // ---------------------------------------------------------------------------
  // Aggregates ((_ table.aggr K) f i X): X grouped by its columns K, each
  // group folded by f from i. The translator adds a counter column to every
  // aggregate with group columns, (+ ((_ tuple.select c) acc) 1) from 0,
  // under a filter that tests it positive: SQL's GROUP BY makes no group of
  // an empty table, while table.aggr folds it to the row of initial values i.
  // ---------------------------------------------------------------------------

  /**
   * AGGREGATE_MAP, an aggregate of a map as an aggregate of the map's argument.
   * It applies when the map copies a column of its argument to each group
   * column, so that the groups are the same.
   */
  BagsRewriteResponse rewriteAggregateOfMap(const TNode& n) const;
  /**
   * AGGREGATE_SORT_OUTPUT, the columns of an aggregate's rows in one order, the
   * copies of the group columns first, under a map that puts them back.
   */
  BagsRewriteResponse rewriteAggregateSortOutput(const TNode& n) const;
  /**
   * FOLD_TUPLE, a fold of tuples whose components each read only their own
   * accumulator as the tuple of the folds of the components.
   */
  BagsRewriteResponse rewriteFoldOfTuple(const TNode& n) const;
  /**
   * AGGREGATE_DEAD_COLUMNS, the columns of an aggregate that the map above it,
   * and a filter in between, do not read are not computed.
   */
  BagsRewriteResponse rewriteAggregateDeadColumns(const TNode& n) const;
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
   * For A = ((_ table.aggr K) f i X) whose group columns K contain a key of X
   * (see rowKeys), the rows of the groups some row of X reached: every group is
   * one row t of X, folded once from i, so they are
   *
   *   (bag.map (lambda ((t (Tuple Int Int))) (f t i)) X)
   *
   * for rows of sort (Tuple Int Int), with (f t i) beta-reduced; null when K
   * holds no key. They are the aggregate's rows except the row of initial
   * values that an aggregate of an empty X has, so AGGREGATE_KEYED uses them
   * where that row is dropped.
   */
  Node keyedAggregateRows(const Node& A) const;
  /** Whether n, a formula, rewrites to false */
  bool rewritesToFalse(const Node& n) const;
  /**
   * Whether the predicate P is false on the row of initial values i, the one
   * row that an aggregate of an empty table has: (P i) rewrites to false. For
   * instance for a test that the count of rows, column 2, is positive,
   *
   *   P = (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1))
   *   i = (tuple 0 0 0)
   */
  bool rejectsInitialRow(const Node& P, const Node& i) const;

  // ---------------------------------------------------------------------------
  // Sets, keys and semi-joins
  // ---------------------------------------------------------------------------

  /**
   * SETOF_MAP_CONSTANT and SETOF_PROJECTION_SORT, the set of a map. Of a
   * map with constant columns: the set of the map without them, under a map
   * that puts them back. Of a projection onto columns in another order than
   * theirs: the set of the projection onto the sorted columns, under a map
   * that puts them in their order.
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
   * Whether no element of X occurs twice, syntactically: a bag.setof, a table
   * with a key, a filter over a set, a product of sets, or a map over one of
   * these that keeps, of every component, all its columns or a key.
   */
  bool isSet(const Node& X) const;
  /**
   * The keys of B, read off its structure: the declared keys of a table
   * constant (see recordKey), kept by filters, intersections and differences
   * and by maps that copy them, combined by products; all the columns of a
   * bag.setof; the group columns of an aggregate. For X and Y of two columns,
   * both with the key {0}, (table.product X Y) has the key {0, 2}. A bag with a
   * key has no row twice.
   */
  std::vector<std::set<uint32_t>> rowKeys(const Node& B) const;
  /**
   * The keys declared for the table constant B, or for the table constant a
   * filter B filters (see BagsKeysAttribute in the .cpp): {{0, 2}, {1}} for
   * keys {0, 2} and {1}.
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
   * Record the key that a key assertion states. For
   * X : (Bag (Tuple Int Int Int)) and
   *
   *   n = (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
   *
   * either way round, or with the projection written as a bag.map, {0, 2} is a
   * key of X (see BagsKeysAttribute in the .cpp), and the bag.setof of n is not
   * rewritten (BagsKeyTermAttribute). Called for top-level assertions only, see
   * recordFacts.
   */
  void recordKey(const TNode& n) const;
  /**
   * Record the NOT NULL column that a NOT NULL assertion states. For
   * X : (Bag (Tuple Int (Nullable Int))) and
   *
   *   n = (= (bag.filter
   *            (lambda ((t (Tuple Int (Nullable Int))))
   *              (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
   *            X)
   *          (as bag.empty (Bag (Tuple Int (Nullable Int)))))
   *
   * either way round, column 1 of X is never null
   * (see BagsNotNullAttribute in the .cpp), and the filter of n is not
   * rewritten (BagsKeyTermAttribute). Called for top-level assertions only, see
   * recordFacts.
   */
  void recordNotNull(const TNode& n) const;
  /**
   * Whether the term t is never null, given the columns nx of the row x and
   * nacc of the accumulator acc that are never null: true for
   * (nullable.some a), for ((_ tuple.select k) x) with k in nx, for an ite of
   * such terms, and for a fold from (nullable.some a) whose step keeps the
   * accumulator so. x and acc may be null.
   */
  bool nonNullTerm(const Node& t,
                   const Node& x,
                   const std::set<uint32_t>& nx,
                   const Node& acc,
                   const std::set<uint32_t>& nacc) const;
  /**
   * The columns of the rows of the aggregate B that are never null: those whose
   * initial value is never null and whose step keeps them so. With reached, for
   * the groups some row reached, also those the step makes never null from
   * these.
   */
  std::set<uint32_t> aggregateNonNull(const Node& B, bool reached) const;
  /**
   * The columns of the rows of B that are never null, read off its structure:
   * the NOT NULL columns of a table constant (see recordNotNull), kept by
   * filters, maps, unions (of both sides), products and aggregates
   * (see aggregateNonNull), and those a filter tests with
   * (nullable.is_some ((_ tuple.select k) t)). Cached in d_nonNull.
   */
  std::set<uint32_t> nonNullColumns(const Node& B) const;
  /**
   * body with the null tests of the columns cols of the row x decided, for
   * columns that are never null. With cols {1},
   * (nullable.is_some ((_ tuple.select 1) x)) becomes true and
   * (= ((_ tuple.select 1) x) (as nullable.null (Nullable Int))) becomes false.
   */
  Node assumeNonNull(const Node& body,
                     const Node& x,
                     const std::set<uint32_t>& cols) const;

  // ---------------------------------------------------------------------------
  // Counters, steps of aggregates, and the groups a row reached
  // ---------------------------------------------------------------------------

  /**
   * The column c of the rows of an aggregate ((_ table.aggr K) f i X) that
   * counts the rows of each group, with the step (+ ((_ tuple.select c) acc) 1)
   * from 0, when the filter predicate P has the conjunct
   * (>= ((_ tuple.select c) r) 1); -1 otherwise.
   */
  int counterColumn(const Node& P, const Node& f, const Node& i) const;
  /**
   * Whether step counts rows from seed (nullable.some 0): COUNT(*),
   * (nullable.some (+ (nullable.val acc) 1)), or COUNT(x), an ite that keeps
   * acc on the rows where x is null and counts the others.
   */
  bool isCountStep(const Node& step, const Node& acc, const Node& seed) const;
  /**
   * For a filter predicate P over the product of comps, whose columns start at
   * starts: for each component, in test, the conjunct of P that tests its count
   * of rows positive (-1 when none), and, as the result, whether its groups are
   * the ones some row reached: 1 when P tests the count, 2 when P joins it on
   * all its group columns with a reached aggregate over the same key values, 0
   * otherwise. The row of initial values of a reached component is in no row
   * that passes P.
   */
  std::vector<int> reachedComponents(const Node& P,
                                     const std::vector<Node>& comps,
                                     const std::vector<size_t>& starts,
                                     std::vector<int>& test) const;
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
   * The columns that a filter predicate fixes to constants: {1 -> 5} for
   * (lambda ((t (Tuple Int Int))) (and (= ((_ tuple.select 1) t) 5) q)).
   */
  std::map<uint32_t, Node> fixedColumns(const Node& p) const;
  /**
   * The columns that every group kept by a counter filter F over an aggregate
   * computes as a constant: those the step sets to a constant, and those it
   * keeps at a constant initial value.
   */
  std::map<uint32_t, Node> reachedGroupConstants(const Node& F) const;
  /**
   * body with the columns of var that fixed maps to constants read as those
   * constants: ((_ tuple.select 1) var) becomes 5 for {1 -> 5}.
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
   * The formula that a nullable Boolean X built of ites over (nullable.some b)
   * and null is (nullable.some true): (ite c b false) for
   * (ite c (nullable.some b) (as nullable.null (Nullable Bool))); null when X
   * is not one.
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

  /**
   * The variable for the accumulator of an aggregate's step, one per type.
   */
  Node accumulatorVariable(TypeNode type) const;
  /**
   * CANONICAL_VARIABLE: the lambda f with its variables renamed to t_N and
   * acc_N, N the id of f's alpha key (see alphaKey), so that lambdas that
   * differ only in the names of their variables become one node. f's body is
   * first simplified (see simplifyIteSame).
   */
  Node canonicalLambda(const Node& f) const;
  /**
   * A node that is the same for lambdas that differ only in the names of their
   * variables: f with every variable it binds replaced by a placeholder for its
   * binding depth, every free variable by one placeholder per sort, the
   * arguments of commutative operators sorted and arithmetic atoms oriented.
   * Cached in d_alphaKeys.
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
   * body with (ite (= a b) b a) replaced by a and (ite (= a b) a b) by b, which
   * the null-aware steps of sqleq's translator leave once an accumulator is
   * known.
   */
  Node simplifyIteSame(const Node& body) const;

  // ---------------------------------------------------------------------------
  // Lambdas and rows
  // ---------------------------------------------------------------------------

  /**
   * The columns that a projection lambda selects, in order: {2, 0} for
   * (lambda ((t (Tuple Int Int Int))) (tuple ((_ tuple.select 2) t) ((_
   * tuple.select 0) t))) or for
   * (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 2 0) t)); empty when f
   * is not one.
   */
  std::vector<uint32_t> projectionIndices(const Node& f) const;
  /**
   * (f x) beta-reduced, for f =
   * (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3)) and x =
   * (tuple a b): (> ((_ tuple.select 1) (tuple a b)) 3), which the rewriter
   * simplifies to (> b 3). (f x) as an application when f is not a lambda; null
   * when the substitution would capture a variable.
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
  /** The lambda of the variable var with the body body */
  Node mkLambda(const Node& var, const Node& body) const;
  /** whether f is a lambda of one variable, which the rules may compose */
  bool composable(const Node& f) const;
  /**
   * The variable and the body of the lambda that the function f stands for: the
   * lambda's own, or, for a function that is not a lambda, the row variable t
   * of its argument sort and (f t).
   */
  std::pair<Node, Node> lambdaOf(const Node& f) const;
  /**
   * The columns of its variable var that body reads, through
   * ((_ tuple.select k) var): {0, 2} for
   * (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)) and var t; false when
   * body uses var otherwise.
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

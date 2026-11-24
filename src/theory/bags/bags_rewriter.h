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
#include <vector>

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
 * Keys and NOT NULL columns of table constants that the input asserts. The
 * rewriter of the theory has none, so what it returns depends only on the
 * node it rewrites. Static learning reads them off the top-level assertions
 * (BagsRewriter::readTableFact) and, with a BagsRewriter of its own that has
 * them, learns F => (= t t') for the terms t of the input (see
 * TableFactsLearner). For X : (Bag (Tuple Int (Nullable Int) Int)), the
 * assertions
 *
 *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
 *   (= (bag.filter
 *        (lambda ((t (Tuple Int (Nullable Int) Int)))
 *          (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
 *        X)
 *      (as bag.empty (Bag (Tuple Int (Nullable Int) Int))))
 *
 * give d_keys = {X: {{0, 2}}} and d_notNull = {X: {1}}.
 */
struct TableFacts
{
  /** whether no table has a key or a NOT NULL column */
  bool empty() const { return d_keys.empty() && d_notNull.empty(); }
  /** the keys of each table constant */
  std::map<Node, std::vector<std::set<uint32_t>>> d_keys;
  /** the NOT NULL columns of each table constant */
  std::map<Node, std::set<uint32_t>> d_notNull;
};

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
 * top-level assertions state (see TableFacts); only a rewriter that has them,
 * as TableFactsLearner builds, applies them. That rewriter also applies
 * EQ_EMPTY_ARG, which the rewriter of the theory must not (see
 * postRewriteEqual).
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
   * - PRODUCT_BAG_MAKE
   * The rewriter does not know the logic, so the default is false: the owner
   * of the rewriter passes true for a higher-order logic. With facts null, as
   * for the rewriter of the theory, no table has a key or a NOT NULL column,
   * and the rules that need one do not apply, nor does EQ_EMPTY_ARG. With
   * facts that are not null but empty, EQ_EMPTY_ARG is the only rule added.
   */
  BagsRewriter(NodeManager* nm,
               Rewriter* r,
               HistogramStat<Rewrite>* statistics = nullptr,
               bool higherOrder = false,
               const TableFacts* facts = nullptr);

  /**
   * postRewrite nodes with kinds: EQUAL, BAG_MAKE, BAG_COUNT, BAG_SETOF,
   * BAG_UNION_MAX, BAG_UNION_DISJOINT, BAG_INTER_MIN,
   * BAG_DIFFERENCE_SUBTRACT, BAG_DIFFERENCE_REMOVE, BAG_CHOOSE, BAG_CARD,
   * BAG_MAP, BAG_FILTER, BAG_ALL, BAG_SOME, BAG_FOLD, BAG_PARTITION,
   * TABLE_PRODUCT, TABLE_PROJECT, TABLE_AGGREGATE and TABLE_GROUP; a node
   * whose children are constants is evaluated. See the rewrite rules for
   * these kinds below.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, BAG_SUBBAG, BAG_MEMBER, BAG_FILTER
   * (FILTER_COUNT_POSITIVE). See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

  /**
   * Adds to facts the key or the NOT NULL column that the literal lit states
   * of a table constant, and returns whether it states one (see TableFacts,
   * readKey and readNotNull). TableFactsLearner calls it on each top-level
   * assertion, which the rewriter of the theory has already rewritten.
   */
  bool readTableFact(TNode lit, TableFacts& facts) const;

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
   * - COUNT_NULL_IN_NOT_NULL, for e with a null where X never has one
   * - COUNT_MAP_DUPLICATE_COLUMNS, for X a map with two equal columns
   * - COUNT_MAP_CONST_COLUMN, for X a map with a constant column
   * - COUNT_MAP_CONST_PROBE, for e with a constant column
   * - COUNT_MAP_FILTER_KEYS, for X a projection of a filter
   * - COUNT_MAP_FILTER_CORRELATED, for X a projection of a filter that reads an
   *   enclosing row
   */
  BagsRewriteResponse rewriteBagCount(const TNode& n) const;

  /**
   * The rules for (bag.setof X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - SETOF_BAG_MAKE
   * - SETOF_UNION_SAME
   * - SETOF_SETOF
   * - SETOF_ABSORB
   * - SEMI_TO_INTERSECTION (semiJoinToIntersection)
   * - SETOF_OF_SET (isSet)
   * - SETOF_PUSHDOWN (rewriteSetofPushdown)
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
   * - UNION_COMPLEMENTARY_FILTERS: two filters of one bag that differ in a
   *   conjunct and its negation are the filter by the other conjuncts
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
   * - INTERSECTION_SORT: the arguments in the order of their node ids
   * - INTERSECTION_SHARE_CONDITIONS: each side gets a filter by the
   *   conditions that the elements of the other satisfy (see
   *   elementConditions)
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
   * - EQ_EMPTY_ARG, for a map or a bag.setof equal to the empty bag, only with
   *   facts (see the constructor)
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
   * - MAP_ITE
   * - MAP_MAP, for X a map (rewriteMapOfMap)
   * - EQ_EMPTY_FILTER_DECORRELATE (normalizeEmptiness)
   * - MAP_SPLIT_CLOSED (rewriteMapSplitClosed)
   * - AGGREGATE_DEAD_COLUMNS, for X an aggregate (rewriteAggregateDeadColumns)
   * - AGGREGATE_JOIN_MERGE (rewriteAggregateJoinMerge)
   * - PRODUCT_AGGREGATE_DEAD_COLUMN (rewriteProductAggregateColumns)
   * - MAP_EQUAL_COLUMNS, for X a filter
   * - MAP_FIXED_COLUMNS, for X a filter (fixedColumns, readFixed)
   * - MAP_IDENTITY_ON_FILTER
   * - SEMI_TO_INTERSECTION (semiJoinToIntersection)
   * - SEMI_JOIN (rewriteSemiJoin)
   * - CANONICAL_VARIABLE (canonicalLambda)
   */
  BagsRewriteResponse postRewriteMap(const TNode& n) const;

  /**
   * The rules for (bag.filter p X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - FILTER_TRUE and FILTER_FALSE
   * - EQ_EMPTY_FILTER_DECORRELATE (normalizeEmptiness)
   * - FILTER_NULLABLE_TRUTH (normalizeTruth)
   * - FILTER_DE_MORGAN
   * - FILTER_CONFLICTING_CONSTANTS
   * - FILTER_KNOWN_NONEMPTY
   * - FILTER_INTO_SETOF (rewriteFilterIntoSetofComponent)
   * - FILTER_KNOWN_MEMBERSHIP (dropKnownMemberships)
   * - FILTER_SORT_CONJUNCTS
   * - CANONICAL_VARIABLE (canonicalLambda)
   * - FILTER_SPLIT_CLOSED
   * - FILTER_CONST, FILTER_BAG_MAKE and FILTER_UNION_DISJOINT
   * - FILTER_ITE
   * - FILTER_FILTER, for X a filter (rewriteFilterOfFilter)
   * - FILTER_MAP, for X a map (rewriteFilterOfMap)
   * - FILTER_COUNT_POSITIVE, for X an aggregate (rewriteFilterCountPositive)
   * - FILTER_AGGREGATE (rewriteFilterOfAggregate)
   * - FILTER_SETOF, for X a bag.setof
   * - FILTER_INTER_MIN, for X an intersection
   * - FILTER_JOIN_TRANSITIVE (rewriteJoinTransitiveConditions)
   * - FILTER_EQUI_JOIN_SETS (rewriteEquiJoinOfSets)
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
   * - FOLD_IDENTITY_STEP
   * - FOLD_OVER_JOIN (eagerAggregation)
   * - FOLD_SUM_FROM_ZERO
   * - FOLD_UNION_COMBINE
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - FOLD_MAP
   * - FOLD_TUPLE (rewriteFoldOfTuple)
   * - FOLD_CONSTANT_STEP
   * - FOLD_ITE
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
   * - AGGREGATE_BAG_MAKE, for X a union of known elements (collectElements):
   *   reduced to bag.map, table.group and bag.fold
   * - AGGREGATE_INTEGER_SUM (rewriteAggregateIntegerSum)
   * - AGGREGATE_OVER_JOIN (rewriteAggregateOverJoin)
   * - AGGREGATE_DUPLICATE_COLUMN (rewriteAggregateDuplicateColumn)
   * - NOT_NULL_COLUMNS (assumeNonNull)
   * - AGGREGATE_SEMI_JOIN (rewriteAggregateSemiJoin)
   * - AGGREGATE_UNION_OF_MAPS
   * - AGGREGATE_FIXED_COLUMNS (fixedColumns, readFixed)
   * - AGGREGATE_NO_KEYS
   * - AGGREGATE_CONSTANT_COLUMNS (rewriteAggregateConstantColumns)
   * - SORTED_KEYS (rewriteSortedKeys)
   * - AGGREGATE_SORT_OUTPUT (rewriteAggregateSortOutput)
   * - CANONICAL_VARIABLE (canonicalLambda)
   * - AGGREGATE_MAP, for X a map (rewriteAggregateOfMap)
   * - AGGREGATE_CONST
   * - AGGREGATE_KEYED (keyedAggregateRows)
   * - AGGREGATE_GROUP_KEYS (rewriteAggregateGroupKeys)
   * - AGGREGATE_ONE_ROW
   * - AGGREGATE_SETOF_IDEMPOTENT
   * - AGGREGATE_COLLAPSE (rewriteAggregateCollapse)
   * - AGGREGATE_ROLLUP (rewriteAggregateRollup)
   * - AGGREGATE_UNION_DISJOINT_KEYS (rewriteAggregateUnionDisjointKeys)
   * - AGGREGATE_UNION_SPLIT (rewriteAggregateUnionSplit)
   */
  BagsRewriteResponse postRewriteAggregate(const TNode& n) const;
  /**
   * An element of a bag: the bag has the elements of d_bag if d_cond, where
   * d_bag is (bag x c) with c > 0 a constant. For example,
   * (ite b (bag y 2) (as bag.empty (Table Int Int))) has the element
   *   {d_cond: b, d_bag: (bag y 2)}
   */
  struct GuardedElement
  {
    Node d_cond;
    Node d_bag;
  };
  /**
   * Collects the elements of A, if A is built from bag.empty, ite,
   * bag.union_disjoint and (bag x c) with c a constant or an ite of
   * constants, as FILTER_BAG_MAKE writes a row of a filter. Each element comes
   * with the condition under which A has it: cond and the conditions of the
   * ite terms above it and in its count. For example, with cond = true,
   *   (bag.union_disjoint
   *     (bag x 1)
   *     (ite b (bag y 2) (as bag.empty (Table Int Int))))
   * gives the elements
   *   {d_cond: true,         d_bag: (bag x 1)}
   *   {d_cond: (and true b), d_bag: (bag y 2)}
   * and (bag x (ite b 1 0)) gives {d_cond: (and true b), d_bag: (bag x 1)}.
   * Returns false if A has another form, for example a variable.
   */
  bool collectElements(TNode A,
                       Node cond,
                       std::vector<GuardedElement>& elements) const;
  /**
   * The rules for (table.product A B), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - PRODUCT_EMPTY
   * - PRODUCT_BAG_MAKE (rewriteProductOfBagMake)
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
  /**
   * The rules for ((_ table.group K) X), each a Rewrite id with an example in
   * rewrites.h:
   *
   * - SORTED_KEYS (rewriteSortedKeys)
   * - GROUP_BAG_MAKE, for X a union of known elements (collectElements)
   */
  BagsRewriteResponse postRewriteGroup(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // The normal form of select-project-join: maps above filters above
  // products. The functions compose lambdas only (see composable); a declared
  // function symbol is left to the rules above.
  // ---------------------------------------------------------------------------

  /**
   * FILTER_FILTER, two filters as one, by the conjunction of their predicates.
   * Both predicates must be lambdas (see composable).
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
   * PRODUCT_MAP_LEFT (left) and PRODUCT_MAP_RIGHT, a product with a map as a
   * factor as a map of the product, which keeps the columns of the other
   * factor. Only with the higher-order flag, see the constructor.
   */
  BagsRewriteResponse rewriteProductOfMap(const TNode& n, bool left) const;
  /**
   * PRODUCT_FILTER_LEFT (left) and PRODUCT_FILTER_RIGHT, a product with a
   * filter as a factor as a filter of the product, over the columns of that
   * factor. Only with the higher-order flag, see the constructor.
   */
  BagsRewriteResponse rewriteProductOfFilter(const TNode& n, bool left) const;
  /**
   * PRODUCT_SWAP, the factors of a product in the order of their node ids,
   * under a map that puts the columns back, so that two joins that list their
   * tables in different orders become one product. Only with the higher-order
   * flag, see the constructor.
   */
  BagsRewriteResponse rewriteProductSwap(const TNode& n) const;
  /**
   * PRODUCT_BAG_MAKE, a product with a bag of one row e, present once or when a
   * condition b holds, as a map of the other factor that adds the columns of e,
   * under a filter by b. side is the factor that is the bag of one row. Only
   * with the higher-order flag, see the constructor.
   */
  BagsRewriteResponse rewriteProductOfBagMake(const TNode& n,
                                              size_t side) const;
  /**
   * MAP_SPLIT_CLOSED, a map whose body asks a question c about a bag that reads
   * no variable but the row, as SQL's EXISTS or IN as a column, as the union of
   * the map over the rows where c holds, with true for c, and the map over the
   * others, with false.
   */
  BagsRewriteResponse rewriteMapSplitClosed(const TNode& n) const;

  // ---------------------------------------------------------------------------
  // Aggregates ((_ table.aggr K) f i X): X grouped by its columns K, each
  // group folded by f from i. A group holds at least one row, so the
  // aggregate of an empty table is empty, as SQL's GROUP BY.
  // ---------------------------------------------------------------------------

  /**
   * AGGREGATE_MAP, an aggregate of a map as an aggregate of the map's argument.
   * It applies when the map copies a column of its argument to each group
   * column, so that the groups are the same, and when the value of the step
   * does not depend on the order of the rows (see orderIndependentStep).
   */
  BagsRewriteResponse rewriteAggregateOfMap(const TNode& n) const;
  /**
   * Whether folding the rows of a bag with the step f gives one value in any
   * order of the rows. Each bag is folded in an order of its own (see
   * BagReduction::reduceFoldOperator), so a rule that replaces the bag that a
   * fold or an aggregate folds, as AGGREGATE_MAP does, keeps its value only
   * for such a step. Each column of the result of f must be a term of the
   * columns of the row in same, which the rows folded together share, or of
   * none; its own accumulator; a sum, as the count of rows
   * (+ ((_ tuple.select 2) acc) 1) or COUNT(*); a minimum or a maximum; SQL's
   * SUM, MIN or MAX, which skip nulls, of an argument tested not null or never
   * null, nonNull the columns of the row that are never null; or one of these
   * on the rows that a condition reading no accumulator holds of, as COUNT(x).
   */
  bool orderIndependentStep(const Node& f,
                            const std::set<uint32_t>& same,
                            const std::set<uint32_t>& nonNull) const;
  /**
   * SORTED_KEYS, the group columns of an aggregate or a partition sorted and
   * without repeats, so that two that group by the same columns are one term.
   */
  BagsRewriteResponse rewriteSortedKeys(const TNode& n) const;
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
   * AGGREGATE_COLLAPSE, an aggregate over a union of aggregates by the same
   * group columns, which merges their columns (a sum of counts or of sums, a
   * minimum of minimums, a maximum of maximums), as one aggregate over the
   * union of their tables. This is the shape of an aggregate pushed through a
   * UNION ALL.
   */
  BagsRewriteResponse rewriteAggregateCollapse(const TNode& n) const;
  /**
   * AGGREGATE_INTEGER_SUM, a column of an aggregate that sums integers read as
   * reals, SQL's SUM(CAST(c AS REAL)), as the integer sum, read as a real once
   * by a map above the aggregate.
   */
  BagsRewriteResponse rewriteAggregateIntegerSum(const TNode& n) const;
  /**
   * AGGREGATE_ROLLUP, an aggregate of an aggregate, Calcite's form of DISTINCT
   * aggregates, as the join of an aggregate over the table with one over the
   * distinct values that the inner aggregate groups by. Every outer column must
   * be a group column, a merge of an inner aggregate, or an aggregate over an
   * inner group column (see the .cpp).
   */
  BagsRewriteResponse rewriteAggregateRollup(const TNode& n) const;
  /**
   * AGGREGATE_JOIN_MERGE, for aggregates that are components of a product
   * under (bag.map h (bag.filter P ..)): two aggregates over one table by the
   * same group columns, joined on their copies of them, are one aggregate.
   */
  BagsRewriteResponse rewriteAggregateJoinMerge(const TNode& n) const;
  /**
   * AGGREGATE_UNION_SPLIT, an aggregate over a union of parts each of which
   * gives the arguments of some columns and null for the others, all with the
   * same keys, as the join of the aggregates of the parts.
   */
  BagsRewriteResponse rewriteAggregateUnionSplit(const TNode& n) const;
  /**
   * AGGREGATE_UNION_DISJOINT_KEYS, an aggregate over a union of parts no two of
   * which share a key value, as the union of the aggregates of the parts.
   */
  BagsRewriteResponse rewriteAggregateUnionDisjointKeys(const TNode& n) const;
  /** Whether n, a formula, rewrites to false */
  bool rewritesToFalse(const Node& n) const;
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
   * AGGREGATE_OVER_JOIN, an aggregate over a join, aggregated eagerly: the
   * aggregate over the join of the aggregates of its sides
   * (see eagerAggregation).
   */
  BagsRewriteResponse rewriteAggregateOverJoin(const TNode& n) const;
  /**
   * PRODUCT_AGGREGATE_DEAD_COLUMN, a column of an aggregate among the
   * components of a product that the map above, and a filter in between, do not
   * read is not computed.
   */
  BagsRewriteResponse rewriteProductAggregateColumns(const TNode& n) const;
  /**
   * AGGREGATE_DUPLICATE_COLUMN, two columns of an aggregate that fold alike,
   * with the same step and initial value, as one column, read twice by a map
   * above the aggregate.
   */
  BagsRewriteResponse rewriteAggregateDuplicateColumn(const TNode& n) const;
  /**
   * AGGREGATE_CONSTANT_COLUMNS, the columns of an aggregate that have one
   * constant in every row (see aggregateConstants) as columns of a map above
   * the aggregate of the others.
   */
  BagsRewriteResponse rewriteAggregateConstantColumns(const TNode& n) const;
  /**
   * AGGREGATE_GROUP_KEYS, an aggregate whose columns are all copies of group
   * columns as those columns of the distinct values of the group columns of
   * its table.
   */
  BagsRewriteResponse rewriteAggregateGroupKeys(const TNode& n) const;
  /**
   * FILTER_AGGREGATE, a conjunct of a filter over an aggregate that reads only
   * copies of group columns, as a filter of the rows of the table before
   * grouping.
   */
  BagsRewriteResponse rewriteFilterOfAggregate(const TNode& n) const;
  /**
   * AGGREGATE_KEYED: for A = ((_ table.aggr K) f i X) whose group columns K
   * contain a key of X (see rowKeys), every group is one row t of X, folded
   * once from i, so A is
   *
   *   (bag.map (lambda ((t (Tuple Int Int))) (f t i)) X)
   *
   * for rows of sort (Tuple Int Int), with (f t i) beta-reduced; null when K
   * holds no key.
   */
  Node keyedAggregateRows(const Node& A) const;
  /**
   * AGGREGATE_SEMI_JOIN, SEMI_JOIN under an aggregate (see rewriteSemiJoin): a
   * join with a set B whose row the join fixes, which the aggregate reads only
   * through columns that the join equates to columns of the other factor, as a
   * filter of that factor by the existence of the matching row of B.
   */
  BagsRewriteResponse rewriteAggregateSemiJoin(const TNode& n) const;

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
   * SEMI_JOIN, a join with a set B whose row the join equations fix, all its
   * columns or a key, and whose columns the map does not read, as a filter of
   * the other components by the existence of the matching row of B: SQL's
   * EXISTS and IN. Called with side 0 only; every component of the product is
   * tried.
   */
  BagsRewriteResponse rewriteSemiJoin(const TNode& n, size_t side) const;
  /**
   * SETOF_PUSHDOWN, under duplicate removal, each component of a product as the
   * set of the columns that the map and the filter read of it.
   */
  BagsRewriteResponse rewriteSetofPushdown(const TNode& n) const;
  /**
   * FILTER_INTO_SETOF, a conjunct of a filter over a product that reads only a
   * component that is a bag.setof, moved into it.
   */
  BagsRewriteResponse rewriteFilterIntoSetofComponent(const TNode& n) const;
  /**
   * SEMI_TO_INTERSECTION: for n a projection of a filter by the membership of
   * the projected row in a bag M, the intersection of the set of the projected
   * rows with the set of M; null when n is not of that shape. It applies under
   * duplicate removal (underSetof), or when the projected rows are a set.
   */
  Node semiJoinToIntersection(const Node& n, bool underSetof) const;
  /**
   * FILTER_EQUI_JOIN_SETS, a join of two sets of one row sort on all their
   * columns, as their intersection, each row twice over; the other conjuncts of
   * the filter stay.
   */
  BagsRewriteResponse rewriteEquiJoinOfSets(const TNode& n) const;
  /**
   * Whether no element of X occurs twice, syntactically: a bag.setof, a table
   * with a key, a filter over a set, a product of sets, or a map over one of
   * these that keeps, of every component, all its columns or a key.
   */
  bool isSet(const Node& X) const;
  /**
   * The keys of B, read off its structure: the keys of a table constant in
   * the facts (see keysOf), kept by filters, intersections and differences
   * and by maps that copy them, combined by products; all the columns of a
   * bag.setof; the group columns of an aggregate. For X and Y of two columns,
   * both with the key {0}, (table.product X Y) has the key {0, 2}. A bag with a
   * key has no row twice.
   */
  std::vector<std::set<uint32_t>> rowKeys(const Node& B) const;
  /**
   * The keys that the facts give the table constant B, or the table constant a
   * filter B filters (see TableFacts): {{0, 2}, {1}} for keys {0, 2} and {1}.
   */
  std::vector<std::set<uint32_t>> keysOf(const Node& B) const;
  /**
   * The conditions that every element w of A satisfies, added to out: those
   * read off the filters of A, through projections onto distinct columns, and
   * through the copies of group columns of an aggregate. For
   * X : (Bag (Tuple Int Int)) and
   *
   *   A = (bag.map
   *         (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 1) s)))
   *         (bag.filter
   *           (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3))
   *           X))
   *
   * out gets (> ((_ tuple.select 0) w) 3).
   */
  void elementConditions(const Node& A,
                         const Node& w,
                         std::set<Node>& out) const;
  /**
   * FILTER_KNOWN_MEMBERSHIP: body, the predicate of a filter over the rows t of
   * A, without the membership conjuncts that every row of A satisfies, or that
   * another conjunct implies. For X : (Bag (Tuple Int Int)), A the product of X
   * with another bag, and
   *
   *   body = (and (>= (bag.count (tuple ((_ tuple.select 0) t))
   *                              (bag.map
   *                                (lambda ((s (Tuple Int Int)))
   *                                  (tuple ((_ tuple.select 0) s)))
   *                                X))
   *                   1)
   *               q)
   *
   * the result is q: column 0 of t is column 0 of a row of X.
   */
  Node dropKnownMemberships(const Node& body,
                            const Node& t,
                            const Node& A) const;

  // ---------------------------------------------------------------------------
  // Facts: keys and NOT NULL columns of table constants
  // ---------------------------------------------------------------------------

  /**
   * Adds to facts the key that the equality n states, and returns whether it
   * states one. The projection M onto the columns of the key is a set, with n
   * either way round. For X : (Bag (Tuple Int Int Int)), the key {0, 2} of X
   * from
   *
   *   n = (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
   *
   * and, as the rewriter of the theory leaves a key on columns out of order
   * (SETOF_PROJECTION_SORT), from
   *
   *   n = (= ((_ table.project 2 0) X)
   *          (bag.map
   *            (lambda ((r (Tuple Int Int)))
   *              (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *            (bag.setof ((_ table.project 0 2) X))))
   *
   * where the map only puts the columns back in order, so its image of a set
   * is a set. A projection may also be a bag.map of a projection lambda
   * (PROJECT_TO_MAP).
   */
  bool readKey(const TNode& n, TableFacts& facts) const;
  /**
   * Adds to facts the NOT NULL column that the equality n states, and returns
   * whether it states one. For X : (Bag (Tuple Int (Nullable Int))), column 1
   * of X from
   *
   *   n = (= (bag.filter
   *            (lambda ((t (Tuple Int (Nullable Int))))
   *              (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
   *            X)
   *          (as bag.empty (Bag (Tuple Int (Nullable Int)))))
   *
   * with both equalities either way round.
   */
  bool readNotNull(const TNode& n, TableFacts& facts) const;
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
   * The columns of the rows of the aggregate B that are never null: those the
   * step makes never null, given the columns of the accumulator whose initial
   * value is never null and that the step keeps so. Every row is a group
   * folded by at least one step.
   */
  std::set<uint32_t> aggregateNonNull(const Node& B) const;
  /**
   * The columns of the rows of B that are never null, read off its structure:
   * the NOT NULL columns of a table constant in the facts (see TableFacts),
   * kept by
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
  // Counters, steps of aggregates, and columns that hold one constant in every
  // row
  // ---------------------------------------------------------------------------

  /**
   * Whether column c of the aggregate A counts the rows of each group, with
   * the step (+ ((_ tuple.select c) acc) 1) from 0, or as SQL's COUNT(*) (see
   * isCountStep). Such a count is at least 1, as every group has a row.
   */
  bool countsRows(const Node& A, size_t c) const;
  /**
   * For arg the column ((_ tuple.select c) row), or that column read as
   * (nullable.some (nullable.val ((_ tuple.select c) row))) where it is never
   * null, c; -1 for any other term, as a function of the column.
   */
  int columnOf(const Node& arg, const Node& row) const;
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
   * FILTER_COUNT_POSITIVE, for a filter over an aggregate: a conjunct that
   * tests a count of the rows of each group (see countsRows) to be at least 1
   * goes, as it holds of every group, and one that tests it equal to a
   * constant below 1 leaves no row. Also a pre-rewrite.
   */
  BagsRewriteResponse rewriteFilterCountPositive(const TNode& n) const;
  /**
   * FILTER_JOIN_TRANSITIVE, a condition that the rows of one side of a join
   * satisfy on a column that the join equates with others holds of the first
   * column of their class too, and joins the filter, so that it is on both
   * sides.
   */
  BagsRewriteResponse rewriteJoinTransitiveConditions(const TNode& n) const;
  /**
   * The columns that a filter predicate fixes to constants: {1 -> 5} for
   * (lambda ((t (Tuple Int Int))) (and (= ((_ tuple.select 1) t) 5) q)).
   */
  std::map<uint32_t, Node> fixedColumns(const Node& p) const;
  /**
   * The columns that every group of the aggregate A computes as a constant:
   * those the step sets to a constant, and those it keeps at a constant
   * initial value.
   */
  std::map<uint32_t, Node> aggregateConstants(const Node& A) const;
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
   * EQ_EMPTY_FILTER_DECORRELATE: the formula that the emptiness of the filter F
   * stands for, decorrelated, or null. F, inside a lambda over a row r, filters
   * the rows s of X by conjuncts c that read no s, conjuncts q that read only
   * s, and equations of columns of s with terms that read no s: it is empty
   * when c fails, or when the tuple of those terms is not among those columns
   * of the rows of X that pass q, a bag that does not depend on r
   * (see rewrites.h).
   */
  Node rewriteEmptyFilter(const Node& F) const;
  /**
   * An atom of a lambda body that asks about a bag, as the formula it stands
   * for, or null: a membership in an intersection or a bag.setof, an
   * emptiness of a filter (see rewriteEmptyFilter), of an aggregate, of an
   * intersection whose filters fix its element, or of a
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
  /** the keys and NOT NULL columns of tables, null for none (TableFacts) */
  const TableFacts* d_facts;

}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_REWRITER_H */

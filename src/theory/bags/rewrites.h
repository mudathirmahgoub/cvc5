/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type for rewrites for bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__REWRITES_H
#define CVC5__THEORY__BAGS__REWRITES_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {
namespace bags {

/** Types of rewrites used by bags
 *
 * This rewrites are documented where they are used in the rewriter. Each one
 * the relational rules add names the function of BagsRewriter that documents
 * it, with its previous and next node.
 */
enum class Rewrite : uint32_t
{
  NONE,  // no rewrite happened
  AGGREGATE_CONST,
  BAG_MAKE_COUNT_NEGATIVE,
  CARD_DISJOINT,
  CARD_BAG_MAKE,
  CHOOSE_BAG_MAKE,
  CONSTANT_EVALUATION,
  COUNT_EMPTY,
  COUNT_BAG_MAKE,
  SETOF_BAG_MAKE,
  EQ_CONST_FALSE,
  EQ_REFL,
  EQ_SYM,
  FILTER_CONST,
  FILTER_BAG_MAKE,
  FILTER_UNION_DISJOINT,
  /** two filters as one, by the conjunction (rewriteFilterOfFilter) */
  FILTER_FILTER,
  /** a filter of a map as a map of a filter (rewriteFilterOfMap) */
  FILTER_MAP,
  /** a filter pushed into a product; not applied (rewriteFilterOfProduct) */
  FILTER_PRODUCT,
  /** (bag.filter p (bag.setof A)) as (bag.setof (bag.filter p A)) */
  FILTER_SETOF,
  /** two maps as one, by the composition (rewriteMapOfMap) */
  MAP_MAP,
  /** a map of the left factor as a map of the product (rewriteProductOfMap) */
  PRODUCT_MAP_LEFT,
  /** a map of the right factor as a map of the product (rewriteProductOfMap) */
  PRODUCT_MAP_RIGHT,
  /**
   * a filter of the left factor as a filter of the product
   * (rewriteProductOfFilter)
   */
  PRODUCT_FILTER_LEFT,
  /**
   * a filter of the right factor as a filter of the product
   * (rewriteProductOfFilter)
   */
  PRODUCT_FILTER_RIGHT,
  /** a product of a union as a union of products (postRewriteProduct) */
  PRODUCT_UNION_DISJOINT,
  /** products right-nested (postRewriteProduct) */
  PRODUCT_ASSOC,
  /**
   * the factors of a product in one order, under a permutation map
   * (rewriteProductSwap)
   */
  PRODUCT_SWAP,
  /** (bag.setof (bag.setof A)) as (bag.setof A) */
  SETOF_SETOF,
  /** a map or a bag.setof empty when its argument is (postRewriteEqual) */
  EQ_EMPTY_ARG,
  /**
   * an aggregate of a map, grouping the rows of the map's argument
   * (rewriteAggregateOfMap)
   */
  AGGREGATE_MAP,
  /**
   * a filter on group columns moved below the aggregate
   * (rewriteFilterOfAggregate)
   */
  FILTER_AGGREGATE,
  /**
   * the group columns of table.aggr and table.group sorted and distinct
   * (rewriteSortedKeys)
   */
  SORTED_KEYS,
  /** a filter by true is its argument (postRewriteFilter) */
  FILTER_TRUE,
  /** a filter by false, or by p and (not p), is empty (postRewriteFilter) */
  FILTER_FALSE,
  /**
   * the conjuncts of a filter in the order of their alpha keys
   * (postRewriteFilter)
   */
  FILTER_SORT_CONJUNCTS,
  /**
   * a lambda over the canonical variables of its alpha key (canonicalLambda)
   */
  CANONICAL_VARIABLE,
  /**
   * the columns of an aggregate's rows in one order
   * (rewriteAggregateSortOutput)
   */
  AGGREGATE_SORT_OUTPUT,
  /**
   * ((_ table.aggr) f i X) as (bag (bag.fold f i X) 1) (postRewriteAggregate)
   */
  AGGREGATE_NO_KEYS,
  /** a fold of tuples as a tuple of folds (rewriteFoldOfTuple) */
  FOLD_TUPLE,
  /** a product with a bag of one row as a map (rewriteProductOfBagMake) */
  PRODUCT_BAG_MAKE,
  /** the set of a map with constant columns (rewriteSetofOfMap) */
  SETOF_MAP_CONSTANT,
  /** unused */
  EQ_EMPTY_BAG_MAKE,
  /** a filter by (or c q), c reading no row, as a union (postRewriteFilter) */
  FILTER_SPLIT_CLOSED,
  /**
   * a join with a set whose row the join fixes as an existence test
   * (rewriteSemiJoin)
   */
  SEMI_JOIN,
  /**
   * a map whose body asks a closed question as a union (rewriteMapSplitClosed)
   */
  MAP_SPLIT_CLOSED,
  /** emptiness tests in lambda bodies as formulas (normalizeEmptiness) */
  EQ_EMPTY_FILTER_DECORRELATE,
  /** a conjunct on projected columns decided on the probe (rewriteBagCount) */
  COUNT_MAP_FILTER_KEYS,
  /**
   * a column of an aggregate nothing reads goes (rewriteAggregateDeadColumns)
   */
  AGGREGATE_DEAD_COLUMNS,
  /** a fold whose step reads neither row nor accumulator (postRewriteFold) */
  FOLD_CONSTANT_STEP,
  /** a map reads the constants a filter fixes (postRewriteMap) */
  MAP_FIXED_COLUMNS,
  /** an aggregate reads the constants a filter fixes (postRewriteAggregate) */
  AGGREGATE_FIXED_COLUMNS,
  /** the identity on the rows a filter passes (postRewriteMap) */
  MAP_IDENTITY_ON_FILTER,
  /**
   * the set of a projection onto sorted columns, permuted (rewriteSetofOfMap)
   */
  SETOF_PROJECTION_SORT,
  /** an aggregate of a union of maps by one function (postRewriteAggregate) */
  AGGREGATE_UNION_OF_MAPS,
  /** an aggregate of a union of aggregates as one (rewriteAggregateCollapse) */
  AGGREGATE_COLLAPSE,
  /** an inner bag.setof under maps, filters and unions goes (rewriteSetof) */
  SETOF_ABSORB,
  /** memberships every row satisfies go (dropKnownMemberships) */
  FILTER_KNOWN_MEMBERSHIP,
  /**
   * (not (or a b)) among the conjuncts as (not a) and (not b)
   * (postRewriteFilter)
   */
  FILTER_DE_MORGAN,
  /** a count in a map with two equal columns (rewriteBagCount) */
  COUNT_MAP_DUPLICATE_COLUMNS,
  /** an equation with an enclosing row as a probe column (rewriteBagCount) */
  COUNT_MAP_FILTER_CORRELATED,
  /** (bag.setof X) as X for a set X (rewriteSetof) */
  SETOF_OF_SET,
  /**
   * the components of a product under bag.setof as sets (rewriteSetofPushdown)
   */
  SETOF_PUSHDOWN,
  /**
   * a conjunct on a set component moved into it
   * (rewriteFilterIntoSetofComponent)
   */
  FILTER_INTO_SETOF,
  /** a semi-join under an aggregate (rewriteAggregateSemiJoin) */
  AGGREGATE_SEMI_JOIN,
  /**
   * a projected semi-join as an intersection of sets (semiJoinToIntersection)
   */
  SEMI_TO_INTERSECTION,
  /** the arguments of bag.inter_min in one order (rewriteIntersectionMin) */
  INTERSECTION_SORT,
  /** a constant in the probe as a filter of the rows (rewriteBagCount) */
  COUNT_MAP_CONST_PROBE,
  /** a count in a map with a constant column (rewriteBagCount) */
  COUNT_MAP_CONST_COLUMN,
  /**
   * a filter of an intersection as an intersection of filters
   * (postRewriteFilter)
   */
  FILTER_INTER_MIN,
  /**
   * an aggregate grouped by a key as a map, where its row of initial values is
   * dropped (keyedAggregateRows)
   */
  AGGREGATE_KEYED,
  /** the null tests of never-null columns decided (assumeNonNull) */
  NOT_NULL_COLUMNS,
  /**
   * a sum of integers read as reals as an integer sum
   * (rewriteAggregateIntegerSum)
   */
  AGGREGATE_INTEGER_SUM,
  /** the two ways to say a nullable Boolean holds as one (normalizeTruth) */
  FILTER_NULLABLE_TRUTH,
  /** an aggregate of an aggregate as a join of two (rewriteAggregateRollup) */
  AGGREGATE_ROLLUP,
  /** an idempotent aggregate of a bag.setof (rewriteAggregateJoinMerge) */
  AGGREGATE_SETOF_IDEMPOTENT,
  /**
   * two aggregates over one table joined on their keys as one
   * (rewriteAggregateJoinMerge)
   */
  AGGREGATE_JOIN_MERGE,
  /**
   * an aggregate of a union of parts as a join of their aggregates
   * (rewriteAggregateUnionSplit)
   */
  AGGREGATE_UNION_SPLIT,
  /**
   * the group columns of the reached groups read off the rows
   * (keysOfReachedGroups)
   */
  AGGREGATE_GROUP_KEYS,
  /** a map reads the first of the columns a filter equates (postRewriteMap) */
  MAP_EQUAL_COLUMNS,
  /** a fold whose step is the accumulator (postRewriteFold) */
  FOLD_IDENTITY_STEP,
  /** a fold of a map as a fold of its argument (postRewriteFold) */
  FOLD_MAP,
  /** (bag.setof (bag.union_disjoint A A)) as (bag.setof A) (rewriteSetof) */
  SETOF_UNION_SAME,
  /**
   * a sum, minimum, maximum or count over a union as two folds combined
   * (postRewriteFold)
   */
  FOLD_UNION_COMBINE,
  /**
   * an aggregate of a union of parts with disjoint keys as a union
   * (rewriteAggregateUnionDisjointKeys)
   */
  AGGREGATE_UNION_DISJOINT_KEYS,
  /** an aggregate of one row (postRewriteFilter) */
  FILTER_AGGREGATE_ONE_ROW,
  /**
   * a condition on one side of a join equation on the other
   * (rewriteJoinTransitiveConditions)
   */
  FILTER_JOIN_TRANSITIVE,
  /**
   * an aggregate pushed through a join (rewriteAggregateOverJoin,
   * eagerAggregation)
   */
  AGGREGATE_OVER_JOIN,
  /** a fold pushed through a join (postRewriteFold, eagerAggregation) */
  FOLD_OVER_JOIN,
  /**
   * a column of an aggregate component nothing reads goes
   * (rewriteProductAggregateColumns)
   */
  PRODUCT_AGGREGATE_DEAD_COLUMN,
  /** two columns that fold alike as one (rewriteAggregateDuplicateColumn) */
  AGGREGATE_DUPLICATE_COLUMN,
  /** a sum from 0 as the sum from null, or 0 (postRewriteFold) */
  FOLD_SUM_FROM_ZERO,
  /** the map that copies every column in order goes (postRewriteMap) */
  MAP_IDENTITY,
  /** COUNT(*) of an aggregate read as its counter (postRewriteFilter) */
  FILTER_COUNT_AS_COUNTER,
  /** filters by p and by (not p) as one (rewriteUnionDisjoint) */
  UNION_COMPLEMENTARY_FILTERS,
  /** a bag a membership finds a row in is not empty (postRewriteFilter) */
  FILTER_KNOWN_NONEMPTY,
  /** a counter test a join implies goes (dropImpliedCounters) */
  FILTER_IMPLIED_COUNTER,
  /** a null in a never-null column occurs 0 times (rewriteBagCount) */
  COUNT_NULL_IN_NOT_NULL,
  /**
   * a join of two sets on all columns as their intersection
   * (rewriteEquiJoinOfSets)
   */
  FILTER_EQUI_JOIN_SETS,
  /**
   * each side of an intersection gets the other's conditions
   * (rewriteIntersectionMin)
   */
  INTERSECTION_SHARE_CONDITIONS,
  /**
   * a conjunction that fixes a term to two constants, or implied conjuncts
   * (postRewriteFilter)
   */
  FILTER_CONFLICTING_CONSTANTS,
  /** a table.project as a bag.map (postRewriteProject) */
  PROJECT_TO_MAP,
  ALL_EMPTY,
  ALL_BAG_MAKE,
  ALL_UNION_DISJOINT,
  ALL_FILTER,
  SOME_EMPTY,
  SOME_BAG_MAKE,
  SOME_UNION_DISJOINT,
  SOME_FILTER,
  FROM_SINGLETON,
  FOLD_BAG,
  FOLD_CONST,
  FOLD_UNION_DISJOINT,
  IDENTICAL_NODES,
  INTERSECTION_EMPTY_LEFT,
  INTERSECTION_EMPTY_RIGHT,
  INTERSECTION_SAME,
  INTERSECTION_SHARED_LEFT,
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_BAG_MAKE,
  MAP_CONST,
  MAP_BAG_MAKE,
  MAP_UNION_DISJOINT,
  MEMBER,
  PARTITION_CONST,
  PRODUCT_EMPTY,
  REMOVE_FROM_UNION,
  REMOVE_MIN,
  REMOVE_RETURN_LEFT,
  REMOVE_SAME,
  SUB_BAG,
  SUBTRACT_DISJOINT_SHARED_LEFT,
  SUBTRACT_DISJOINT_SHARED_RIGHT,
  SUBTRACT_FROM_UNION,
  SUBTRACT_MIN,
  SUBTRACT_RETURN_LEFT,
  SUBTRACT_SAME,
  TO_SINGLETON,
  UNION_DISJOINT_EMPTY_LEFT,
  UNION_DISJOINT_EMPTY_RIGHT,
  UNION_DISJOINT_MAX_MIN,
  UNION_MAX_EMPTY,
  UNION_MAX_SAME_OR_EMPTY,
  UNION_MAX_UNION_LEFT,
  UNION_MAX_UNION_RIGHT
};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__REWRITES_H */

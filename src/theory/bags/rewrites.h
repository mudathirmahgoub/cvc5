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

/**
 * Types of rewrites used by bags, each documented by an example in the
 * notation at the top of bags_rewriter.cpp:
 *   previous node
 *   ---> next node
 * The function of BagsRewriter named with a rule documents it further.
 */
enum class Rewrite : uint32_t
{
  /** no rewrite happened */
  NONE,
  /**
   * AGGREGATE_CONST: an aggregate of constants is evaluated
   */
  AGGREGATE_CONST,
  /**
   * BAG_MAKE_COUNT_NEGATIVE: for a constant c <= 0,
   *   (bag x c) ---> (as bag.empty (Bag T))
   */
  BAG_MAKE_COUNT_NEGATIVE,
  CARD_DISJOINT,
  /**
   * CARD_BAG_MAKE: for a constant c > 0,
   *   (bag.card (bag x c)) ---> c
   */
  CARD_BAG_MAKE,
  /**
   * CHOOSE_BAG_MAKE: for a constant c > 0,
   *   (bag.choose (bag x c)) ---> x
   */
  CHOOSE_BAG_MAKE,
  /**
   * CONSTANT_EVALUATION: a term of constants is evaluated:
   *   (bag.union_disjoint (bag 1 2) (bag 1 3)) ---> (bag 1 5)
   */
  CONSTANT_EVALUATION,
  /**
   * COUNT_EMPTY:
   *   (bag.count x (as bag.empty (Bag T))) ---> 0
   */
  COUNT_EMPTY,
  /**
   * COUNT_BAG_MAKE: for a constant c > 0,
   *   (bag.count x (bag x c)) ---> c
   */
  COUNT_BAG_MAKE,
  /**
   * SETOF_BAG_MAKE:
   *   (bag.setof (bag x c)) ---> (bag x 1)
   * for a constant c > 0, and otherwise
   *   (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
   */
  SETOF_BAG_MAKE,
  /**
   * EQ_CONST_FALSE: for distinct constants A and B,
   *   (= A B) ---> false
   */
  EQ_CONST_FALSE,
  /**
   * EQ_REFL:
   *   (= A A) ---> true
   */
  EQ_REFL,
  /**
   * EQ_SYM: for A < B,
   *   (= B A) ---> (= A B)
   */
  EQ_SYM,
  /**
   * FILTER_CONST: a filter of a constant is evaluated:
   *   (bag.filter p (bag "a" 3))
   *   ---> (ite (p "a") (bag "a" 3) (as bag.empty (Bag String)))
   */
  FILTER_CONST,
  /**
   * FILTER_BAG_MAKE:
   *   (bag.filter p (bag x c)) ---> (bag x (ite (p x) c 0))
   */
  FILTER_BAG_MAKE,
  /**
   * FILTER_UNION_DISJOINT:
   *   (bag.filter p (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   */
  FILTER_UNION_DISJOINT,
  /**
   * FILTER_FILTER:
   *   (bag.filter (lambda ((s T)) p) (bag.filter (lambda ((t T)) q) A))
   *   ---> (bag.filter (lambda ((t T)) (and p[s := t] q)) A)
   */
  FILTER_FILTER,
  /**
   * FILTER_MAP:
   *   (bag.filter (lambda ((s U)) p) (bag.map (lambda ((t T)) e) A))
   *   ---> (bag.map (lambda ((t T)) e)
   *                 (bag.filter (lambda ((t T)) p[s := e]) A))
   */
  FILTER_MAP,
  /**
   * FILTER_SETOF:
   *   (bag.filter p (bag.setof A)) ---> (bag.setof (bag.filter p A))
   */
  FILTER_SETOF,
  /**
   * MAP_MAP:
   *   (bag.map (lambda ((s U)) e) (bag.map (lambda ((t T)) g) A))
   *   ---> (bag.map (lambda ((t T)) e[s := g]) A)
   */
  MAP_MAP,
  /**
   * PRODUCT_MAP_LEFT, the map of the left factor as a map of the product
   * (see rewriteProductOfMap); with A and B of two columns,
   *   (table.product (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
   *                           A)
   *                  B)
   *   ---> (bag.map (lambda ((t V)) (tuple ((_ tuple.select 1) t)
   *                                        ((_ tuple.select 2) t)
   *                                        ((_ tuple.select 3) t)))
   *                 (table.product A B))
   */
  PRODUCT_MAP_LEFT,
  /**
   * PRODUCT_MAP_RIGHT, the map of the right factor as a map of the product
   * (see rewriteProductOfMap); with A and B of two columns,
   *   (table.product A
   *                  (bag.map (lambda ((s T)) (tuple ((_ tuple.select 1) s)))
   *                           B))
   *   ---> (bag.map (lambda ((t V)) (tuple ((_ tuple.select 0) t)
   *                                        ((_ tuple.select 1) t)
   *                                        ((_ tuple.select 3) t)))
   *                 (table.product A B))
   */
  PRODUCT_MAP_RIGHT,
  /**
   * PRODUCT_FILTER_LEFT, the filter of the left factor as a filter of the
   * product (see rewriteProductOfFilter):
   *   (table.product (bag.filter (lambda ((s T)) (> ((_ tuple.select 1) s) 3))
   *                              A)
   *                  B)
   *   ---> (bag.filter (lambda ((t V)) (> ((_ tuple.select 1) t) 3))
   *                    (table.product A B))
   */
  PRODUCT_FILTER_LEFT,
  /**
   * PRODUCT_FILTER_RIGHT, the filter of the right factor as a filter of the
   * product (see rewriteProductOfFilter); with A of two columns,
   *   (table.product A (bag.filter (lambda ((s U)) (> ((_ tuple.select 1) s)
   *                                                  3))
   *                                B))
   *   ---> (bag.filter (lambda ((t V)) (> ((_ tuple.select 3) t) 3))
   *                    (table.product A B))
   */
  PRODUCT_FILTER_RIGHT,
  /**
   * PRODUCT_UNION_DISJOINT:
   *     (table.product (bag.union_disjoint A B) C)
   *     ---> (bag.union_disjoint (table.product A C) (table.product B C))
   *   and the same on the right
   */
  PRODUCT_UNION_DISJOINT,
  /**
   * PRODUCT_ASSOC:
   *     (table.product (table.product A B) C)
   *     ---> (table.product A (table.product B C))
   */
  PRODUCT_ASSOC,
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
  PRODUCT_SWAP,
  /**
   * SETOF_SETOF: (bag.setof (bag.setof A)) ---> (bag.setof A)
   */
  SETOF_SETOF,
  /**
   * EQ_EMPTY_ARG, a map or a bag.setof is empty when its argument is:
   *   (= (bag.map f X) (as bag.empty (Bag U)))
   *   ---> (= X (as bag.empty (Bag T)))
   *   (= (bag.setof X) (as bag.empty (Bag T)))
   *   ---> (= X (as bag.empty (Bag T)))
   */
  EQ_EMPTY_ARG,
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
  AGGREGATE_MAP,
  /**
   * FILTER_TRUE:
   *   (bag.filter (lambda ((t T)) true) A) ---> A
   */
  FILTER_TRUE,
  /**
   * FILTER_FALSE, a filter no row passes:
   *   (bag.filter (lambda ((t T)) false) A) ---> (as bag.empty (Bag T))
   *   (bag.filter (lambda ((t T)) (and p (not p))) A)
   *   ---> (as bag.empty (Bag T))
   */
  FILTER_FALSE,
  /**
   * FILTER_SORT_CONJUNCTS, the conjuncts in the order of their alpha
   * keys, without duplicates:
   *   (bag.filter (lambda ((t T)) (and q p q)) X)
   *   ---> (bag.filter (lambda ((t T)) (and p q)) X)
   */
  FILTER_SORT_CONJUNCTS,
  /**
   * CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N the
   * id of f's alpha key, when that is safe:
   *   (lambda ((s T)) (> ((_ tuple.select 0) s) 3))
   *   ---> (lambda ((t_N T)) (> ((_ tuple.select 0) t_N) 3))
   * f's body is first simplified, see simplifyIteSame.
   */
  CANONICAL_VARIABLE,
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
  AGGREGATE_SORT_OUTPUT,
  /**
   * AGGREGATE_NO_KEYS, one group of all of X, even an empty X:
   *     ((_ table.aggr) f i X) ---> (bag (bag.fold f i X) 1)
   */
  AGGREGATE_NO_KEYS,
  /**
   * FOLD_TUPLE, a fold of tuples whose components read their own
   * accumulator only:
   *   (bag.fold (lambda ((t T) (acc (Tuple Int Int))) (tuple b0 b1))
   *             (tuple i0 i1) X)
   *   ---> (tuple (bag.fold (lambda ((t T) (a Int)) b0') i0 X)
   *               (bag.fold (lambda ((t T) (a Int)) b1') i1 X))
   */
  FOLD_TUPLE,
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
  PRODUCT_BAG_MAKE,
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
  SETOF_MAP_CONSTANT,
  /**
   * FILTER_SPLIT_CLOSED, a disjunct c that does not read the row (EXISTS):
   *   (bag.filter (lambda ((t T)) (or c q)) A)
   *   ---> (bag.union_disjoint
   *          (bag.filter (lambda ((t T)) c) A)
   *          (bag.filter (lambda ((t T)) (and (not c) q)) A))
   */
  FILTER_SPLIT_CLOSED,
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
   */
  SEMI_JOIN,
  /**
   * EQ_EMPTY_FILTER_DECORRELATE, the emptiness of a filter that reads the
   * row r of an enclosing lambda, as a membership that does not, in the
   * bodies of filters and maps (see normalizeEmptiness, rewriteEmptyFilter):
   *   (= (as bag.empty (Bag T))
   *      (bag.filter (lambda ((s T)) (and q (= ((_ tuple.select 1) s)
   *                                            ((_ tuple.select 0) r))))
   *                  X))
   *   ---> (not (>= (bag.count (tuple ((_ tuple.select 0) r))
   *                            (bag.map (lambda ((s T))
   *                                       (tuple ((_ tuple.select 1) s)))
   *                                     (bag.filter (lambda ((s T)) q) X)))
   *                 1))
   * for q reading only s
   */
  EQ_EMPTY_FILTER_DECORRELATE,
  /**
   * COUNT_MAP_FILTER_KEYS, a conjunct on projected columns is decided on
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
   */
  COUNT_MAP_FILTER_KEYS,
  /**
   * AGGREGATE_DEAD_COLUMNS, a column of the aggregate nothing reads:
   *   (bag.map h ((_ table.aggr 0) (lambda ((t T) (acc S)) (tuple a0 a1 a2))
   *                                (tuple i0 i1 i2) X))
   *   ---> (bag.map h' ((_ table.aggr 0) (lambda ((t T) (acc S'))
   *                                        (tuple a0 a2'))
   *                                      (tuple i0 i2) X))
   * also under a filter between the map and the aggregate
   */
  AGGREGATE_DEAD_COLUMNS,
  /**
   * FOLD_CONSTANT_STEP:
   *   (bag.fold (lambda ((t T) (acc S)) c) i X)
   *   ---> (ite (= X (as bag.empty (Bag T))) i c)
   * for c reading neither t nor acc
   */
  FOLD_CONSTANT_STEP,
  /**
   * MAP_FIXED_COLUMNS, the constants the filter fixes columns to:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 1) t)))
   *            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                        X))
   *   ---> (bag.map (lambda ((t T)) (tuple 5))
   *                 (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s)
   *                                                5))
   *                             X))
   * and, over an aggregate whose counter the filter tests, the constants
   * its groups compute (see reachedGroupConstants)
   */
  MAP_FIXED_COLUMNS,
  /**
   * MAP_IDENTITY_ON_FILTER, the identity on the rows that pass:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t) 5))
   *            (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5))
   *                        X))
   *   ---> (bag.filter (lambda ((s T)) (= ((_ tuple.select 1) s) 5)) X)
   */
  MAP_IDENTITY_ON_FILTER,
  /**
   * SETOF_PROJECTION_SORT, the set of a projection onto columns in another
   * order than theirs as the set of the projection onto the sorted columns,
   * mapped back by the permutation (see rewriteSetofOfMap):
   *   (bag.setof (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)
   *                                              ((_ tuple.select 0) t)))
   *                       Y))
   *   ---> (bag.map (lambda ((r U)) (tuple ((_ tuple.select 1) r)
   *                                        ((_ tuple.select 0) r)))
   *                 (bag.setof (bag.map (lambda ((t T))
   *                                       (tuple ((_ tuple.select 0) t)
   *                                              ((_ tuple.select 2) t)))
   *                                     Y)))
   */
  SETOF_PROJECTION_SORT,
  /**
   * AGGREGATE_UNION_OF_MAPS, a union of maps by one g is the map of the
   *   union, which AGGREGATE_MAP then absorbs:
   *     ((_ table.aggr K) f i (bag.union_disjoint (bag.map g X1)
   *                                               (bag.map g X2)))
   *     ---> the AGGREGATE_MAP rewrite of
   *          ((_ table.aggr K) f i (bag.map g (bag.union_disjoint X1 X2)))
   */
  AGGREGATE_UNION_OF_MAPS,
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
  AGGREGATE_COLLAPSE,
  /**
   * SETOF_ABSORB, an inner bag.setof under maps, filters and unions:
   *     (bag.setof (bag.map f (bag.setof X))) ---> (bag.setof (bag.map f X))
   */
  SETOF_ABSORB,
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
  FILTER_KNOWN_MEMBERSHIP,
  /**
   * FILTER_DE_MORGAN:
   *   (bag.filter (lambda ((t T)) (and p (not (or a b)))) X)
   *   ---> (bag.filter (lambda ((t T)) (and p (not a) (not b))) X)
   */
  FILTER_DE_MORGAN,
  /**
   * COUNT_MAP_DUPLICATE_COLUMNS, a map that makes columns i < j equal:
   *     (bag.count (tuple a b c) (bag.map (lambda ((t T)) (tuple u v u)) X))
   *     ---> (ite (= a c)
   *               (bag.count (tuple a b)
   *                          (bag.map (lambda ((t T)) (tuple u v)) X))
   *               0)
   */
  COUNT_MAP_DUPLICATE_COLUMNS,
  /**
   * SETOF_OF_SET, a bag with no element twice (see isSet):
   *     (bag.setof X) ---> X
   */
  SETOF_OF_SET,
  /**
   * COUNT_MAP_CONST_PROBE, a constant in the probe selects rows of X:
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
   */
  COUNT_MAP_CONST_PROBE,
  /**
   * AGGREGATE_KEYED, see keyedAggregateRows: under a filter that drops the
   * row of initial values (see rejectsInitialRow),
   *   (bag.filter Q ((_ table.aggr 0) (lambda ((t T) (acc S)) b) i X))
   *   ---> (bag.filter Q (bag.map (lambda ((t T)) b[acc := i]) X))
   * for 0 a key of X, and for an aggregate component of a product whose
   * groups the filter keeps reached ones of (see reachedComponents)
   */
  AGGREGATE_KEYED,
  /**
   * NOT_NULL_COLUMNS, the null tests of columns that are never null decided,
   * in filters, maps, folds and aggregates (see assumeNonNull,
   * nonNullColumns); with column 1 of X never null,
   *   (bag.filter (lambda ((t T))
   *                 (and (nullable.is_some ((_ tuple.select 1) t)) p))
   *               X)
   *   ---> (bag.filter (lambda ((t T)) (and true p)) X)
   */
  NOT_NULL_COLUMNS,
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
  AGGREGATE_INTEGER_SUM,
  /**
   * FILTER_NULLABLE_TRUTH, the two conjuncts that say a nullable Boolean X
   * holds as the one formula they say (see normalizeTruth):
   *   (bag.filter (lambda ((t T)) (and (nullable.is_some X) (nullable.val X)))
   *               A)
   *   ---> (bag.filter (lambda ((t T)) (ite c b false)) A)
   * for X = (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
   */
  FILTER_NULLABLE_TRUTH,
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
  AGGREGATE_ROLLUP,
  /**
   * AGGREGATE_SETOF_IDEMPOTENT, for an aggregate that is a component of a
   * product under (bag.map h (bag.filter P ..)) and computes only copies of
   * the row's columns, minimums, maximums and a counter that h does not read
   * and P reads only through (>= c 1): duplicate rows change none of those
   * (see rewriteAggregateJoinMerge),
   *   ((_ table.aggr 0) f i (bag.setof Y)) ---> ((_ table.aggr 0) f i Y)
   */
  AGGREGATE_SETOF_IDEMPOTENT,
  /**
   * AGGREGATE_JOIN_MERGE, two aggregates over one X by the same columns K,
   * both copying every group column and seeding the copies alike, joined on
   * those copies, as one aggregate computing the columns of both (see
   * rewriteAggregateJoinMerge):
   *   (bag.map h (bag.filter (lambda ((p W)) (= ((_ tuple.select 0) p)
   *                                             ((_ tuple.select 3) p)))
   *                          (table.product ((_ table.aggr 0) fa ia X)
   *                                         ((_ table.aggr 0) fb ib X))))
   *   ---> (bag.map h' ((_ table.aggr 0) fm im X))
   * where fm's rows are those of fa followed by fb's columns other than the
   * copies, and h' reads fb's copies from fa's
   */
  AGGREGATE_JOIN_MERGE,
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
  AGGREGATE_UNION_SPLIT,
  /**
   * AGGREGATE_GROUP_KEYS, see keysOfReachedGroups:
   *     (bag.setof (bag.map h (bag.filter Q ((_ table.aggr K) f i X))))
   *     ---> (bag.setof (bag.map h' X))
   */
  AGGREGATE_GROUP_KEYS,
  /**
   * MAP_EQUAL_COLUMNS, the first of the columns the filter equates:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 2) t)))
   *            (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                           ((_ tuple.select 2) s)))
   *                        X))
   *   ---> (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)))
   *                 (bag.filter (lambda ((s T)) (= ((_ tuple.select 0) s)
   *                                                ((_ tuple.select 2) s)))
   *                             X))
   */
  MAP_EQUAL_COLUMNS,
  /**
   * FOLD_MAP:
   *   (bag.fold (lambda ((t U) (acc S)) b) i
   *             (bag.map (lambda ((s T)) e) Y))
   *   ---> (bag.fold (lambda ((s T) (acc S)) b[t := e]) i Y)
   */
  FOLD_MAP,
  /**
   * SETOF_UNION_SAME:
   *     (bag.setof (bag.union_disjoint A A)) ---> (bag.setof A)
   */
  SETOF_UNION_SAME,
  /**
   * AGGREGATE_UNION_DISJOINT_KEYS, an aggregate over a union of parts no two
   * of which share a key value:
   *   (bag.map h (bag.filter Q ((_ table.aggr 0) f i
   *                               (bag.union_disjoint U1 U2))))
   *   ---> (bag.map h (bag.filter Q (bag.union_disjoint
   *                                   ((_ table.aggr 0) f i U1)
   *                                   ((_ table.aggr 0) f i U2))))
   */
  AGGREGATE_UNION_DISJOINT_KEYS,
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
  FILTER_JOIN_TRANSITIVE,
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
  PRODUCT_AGGREGATE_DEAD_COLUMN,
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
  AGGREGATE_DUPLICATE_COLUMN,
  /**
   * MAP_IDENTITY:
   *   (bag.map (lambda ((t T)) (tuple ((_ tuple.select 0) t)
   *                                   ((_ tuple.select 1) t)))
   *            X)
   *   ---> X
   */
  MAP_IDENTITY,
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
  FILTER_IMPLIED_COUNTER,
  /**
   * FILTER_CONFLICTING_CONSTANTS:
   *   (bag.filter (lambda ((t T)) (and (= ((_ tuple.select 0) t) 1)
   *                                    (= ((_ tuple.select 0) t) 2)))
   *               X)
   *   ---> (as bag.empty (Bag T))
   * and the conjuncts the others imply go: (nullable.is_some a) beside
   * (= a (nullable.some 5)), the null test of a value that a membership
   * puts in a never-null column, (>= (* a b) 1) beside (>= a 1) and
   * (>= b 1)
   */
  FILTER_CONFLICTING_CONSTANTS,
  /**
   * PROJECT_TO_MAP: a projection is a map, which the map rules then reach:
   *   ((_ table.project 1 0) X)
   *   ---> (bag.map (lambda ((t T)) ((_ tuple.project 1 0) t)) X)
   */
  PROJECT_TO_MAP,
  /**
   * ALL_EMPTY:
   *   (bag.all p (as bag.empty (Bag T))) ---> true
   */
  ALL_EMPTY,
  /**
   * ALL_BAG_MAKE:
   *   (bag.all p (bag x c)) ---> (or (p x) (<= c 0))
   */
  ALL_BAG_MAKE,
  /**
   * ALL_UNION_DISJOINT:
   *   (bag.all p (bag.union_disjoint A B))
   *   ---> (and (bag.all p A) (bag.all p B))
   */
  ALL_UNION_DISJOINT,
  /**
   * ALL_FILTER:
   *   (bag.all p A) ---> (= (bag.filter p A) A)
   */
  ALL_FILTER,
  /**
   * SOME_EMPTY:
   *   (bag.some p (as bag.empty (Bag T))) ---> false
   */
  SOME_EMPTY,
  /**
   * SOME_BAG_MAKE:
   *   (bag.some p (bag x c)) ---> (and (> c 0) (p x))
   */
  SOME_BAG_MAKE,
  /**
   * SOME_UNION_DISJOINT:
   *   (bag.some p (bag.union_disjoint A B))
   *   ---> (or (bag.some p A) (bag.some p B))
   */
  SOME_UNION_DISJOINT,
  /**
   * SOME_FILTER:
   *   (bag.some p A)
   *   ---> (not (= (bag.filter p A) (as bag.empty (Bag T))))
   */
  SOME_FILTER,
  FROM_SINGLETON,
  /**
   * FOLD_BAG: for a constant c > 0,
   *   (bag.fold f t (bag x c)) ---> (f x (f x .. (f x t))), c times
   */
  FOLD_BAG,
  /**
   * FOLD_CONST: a fold over a constant is evaluated
   */
  FOLD_CONST,
  /**
   * FOLD_UNION_DISJOINT: for A < B,
   *   (bag.fold f t (bag.union_disjoint A B))
   *   ---> (bag.fold f (bag.fold f t A) B)
   */
  FOLD_UNION_DISJOINT,
  /**
   * IDENTICAL_NODES: for bags A,
   *   (= A A) ---> true
   */
  IDENTICAL_NODES,
  /**
   * INTERSECTION_EMPTY_LEFT:
   *   (bag.inter_min (as bag.empty (Bag T)) A)
   *   ---> (as bag.empty (Bag T))
   */
  INTERSECTION_EMPTY_LEFT,
  /**
   * INTERSECTION_EMPTY_RIGHT:
   *   (bag.inter_min A (as bag.empty (Bag T)))
   *   ---> (as bag.empty (Bag T))
   */
  INTERSECTION_EMPTY_RIGHT,
  /**
   * INTERSECTION_SAME:
   *   (bag.inter_min A A) ---> A
   */
  INTERSECTION_SAME,
  /**
   * INTERSECTION_SHARED_LEFT:
   *   (bag.inter_min A (bag.union_disjoint A B)) ---> A
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  INTERSECTION_SHARED_LEFT,
  /**
   * INTERSECTION_SHARED_RIGHT:
   *   (bag.inter_min (bag.union_disjoint A B) A) ---> A
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_BAG_MAKE,
  /**
   * MAP_CONST: a map of a constant is evaluated:
   *   (bag.map f (bag "a" 3)) ---> (bag (f "a") 3)
   */
  MAP_CONST,
  /**
   * MAP_BAG_MAKE:
   *   (bag.map f (bag x c)) ---> (bag (f x) c)
   */
  MAP_BAG_MAKE,
  /**
   * MAP_UNION_DISJOINT:
   *   (bag.map f (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.map f A) (bag.map f B))
   */
  MAP_UNION_DISJOINT,
  /**
   * MEMBER:
   *   (bag.member x A) ---> (>= (bag.count x A) 1)
   */
  MEMBER,
  /**
   * PARTITION_CONST: a partition of a constant is evaluated
   */
  PARTITION_CONST,
  /**
   * PRODUCT_EMPTY:
   *   (table.product (as bag.empty (Bag T)) B) ---> (as bag.empty (Bag V))
   * and with the empty bag second
   */
  PRODUCT_EMPTY,
  /**
   * REMOVE_FROM_UNION:
   *   (bag.difference_remove A (bag.union_disjoint A B))
   *   ---> (as bag.empty (Bag T))
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  REMOVE_FROM_UNION,
  /**
   * REMOVE_MIN:
   *   (bag.difference_remove (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag T))
   * and for (bag.inter_min B A)
   */
  REMOVE_MIN,
  /**
   * REMOVE_RETURN_LEFT:
   *   (bag.difference_remove A (as bag.empty (Bag T))) ---> A
   *   (bag.difference_remove (as bag.empty (Bag T)) B)
   *   ---> (as bag.empty (Bag T))
   */
  REMOVE_RETURN_LEFT,
  /**
   * REMOVE_SAME:
   *   (bag.difference_remove A A) ---> (as bag.empty (Bag T))
   */
  REMOVE_SAME,
  /**
   * SUB_BAG:
   *   (bag.subbag A B)
   *   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag T)))
   */
  SUB_BAG,
  /**
   * SUBTRACT_DISJOINT_SHARED_LEFT:
   *   (bag.difference_subtract (bag.union_disjoint A B) A) ---> B
   */
  SUBTRACT_DISJOINT_SHARED_LEFT,
  /**
   * SUBTRACT_DISJOINT_SHARED_RIGHT:
   *   (bag.difference_subtract (bag.union_disjoint B A) A) ---> B
   */
  SUBTRACT_DISJOINT_SHARED_RIGHT,
  /**
   * SUBTRACT_FROM_UNION:
   *   (bag.difference_subtract A (bag.union_disjoint A B))
   *   ---> (as bag.empty (Bag T))
   * also for bag.union_max and for (bag.union_disjoint B A)
   */
  SUBTRACT_FROM_UNION,
  /**
   * SUBTRACT_MIN:
   *   (bag.difference_subtract (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag T))
   * and for (bag.inter_min B A)
   */
  SUBTRACT_MIN,
  /**
   * SUBTRACT_RETURN_LEFT:
   *   (bag.difference_subtract A (as bag.empty (Bag T))) ---> A
   *   (bag.difference_subtract (as bag.empty (Bag T)) B)
   *   ---> (as bag.empty (Bag T))
   */
  SUBTRACT_RETURN_LEFT,
  /**
   * SUBTRACT_SAME:
   *   (bag.difference_subtract A A) ---> (as bag.empty (Bag T))
   */
  SUBTRACT_SAME,
  TO_SINGLETON,
  /**
   * UNION_DISJOINT_EMPTY_LEFT:
   *   (bag.union_disjoint (as bag.empty (Bag T)) A) ---> A
   */
  UNION_DISJOINT_EMPTY_LEFT,
  /**
   * UNION_DISJOINT_EMPTY_RIGHT:
   *   (bag.union_disjoint A (as bag.empty (Bag T))) ---> A
   */
  UNION_DISJOINT_EMPTY_RIGHT,
  /**
   * UNION_DISJOINT_MAX_MIN:
   *   (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B))
   *   ---> (bag.union_disjoint A B)
   */
  UNION_DISJOINT_MAX_MIN,
  /**
   * UNION_MAX_EMPTY:
   *   (bag.union_max (as bag.empty (Bag T)) A) ---> A
   */
  UNION_MAX_EMPTY,
  /**
   * UNION_MAX_SAME_OR_EMPTY:
   *   (bag.union_max A A) ---> A
   *   (bag.union_max A (as bag.empty (Bag T))) ---> A
   */
  UNION_MAX_SAME_OR_EMPTY,
  /**
   * UNION_MAX_UNION_LEFT:
   *   (bag.union_max A (bag.union_max A B)) ---> (bag.union_max A B)
   * also for bag.union_disjoint and for (bag.union_max B A)
   */
  UNION_MAX_UNION_LEFT,
  /**
   * UNION_MAX_UNION_RIGHT:
   *   (bag.union_max (bag.union_max A B) A) ---> (bag.union_max A B)
   * also for bag.union_disjoint and for (bag.union_max B A)
   */
  UNION_MAX_UNION_RIGHT,
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

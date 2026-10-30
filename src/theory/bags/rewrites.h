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
 * The rewrite rules of the bags rewriter, one id per rule, which
 * BagsRewriter reports for every step it takes. Each rule is documented by an
 * example in SMT-LIB: the sorts of its symbols, a term, and, after --->, what
 * the rule rewrites the term to, which is equivalent to it. The examples can
 * be checked with cvc5, as (assert (not (= term result))) is unsatisfiable.
 */
enum class Rewrite : uint32_t
{
  /** no rewrite happened */
  NONE,
  /**
   * An aggregate of a constant table is evaluated.
   *
   * For f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *           (tuple ((_ tuple.select 0) t)
   *                  (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))),
   *
   *   ((_ table.aggr 0) f
   *                     (tuple 0 0)
   *                     (bag.union_disjoint
   *                       (bag (tuple 1 2) 1)
   *                       (bag (tuple 1 3) 1)))
   *   ---> (bag (tuple 1 5) 1)
   */
  AGGREGATE_CONST,
  /**
   * A bag with an element a non-positive constant number of times is empty.
   *
   * For x : Int,
   *
   *   (bag x 0)
   *   ---> (as bag.empty (Bag Int))
   */
  BAG_MAKE_COUNT_NEGATIVE,
  CARD_DISJOINT,
  /**
   * The cardinality of a bag with one element, a positive constant number of
   * times.
   *
   * For x : Int,
   *
   *   (bag.card (bag x 3))
   *   ---> 3
   */
  CARD_BAG_MAKE,
  /**
   * The element chosen from a bag with one element.
   *
   * For x : Int,
   *
   *   (bag.choose (bag x 3))
   *   ---> x
   */
  CHOOSE_BAG_MAKE,
  /**
   * A bag operator applied to constants is evaluated.
   *
   *   (bag.union_disjoint (bag 1 2) (bag 1 3))
   *   ---> (bag 1 5)
   */
  CONSTANT_EVALUATION,
  /**
   * Nothing occurs in the empty bag.
   *
   * For x : Int,
   *
   *   (bag.count x (as bag.empty (Bag Int)))
   *   ---> 0
   */
  COUNT_EMPTY,
  /**
   * The count of the element of a bag with one element, a positive constant
   * number of times.
   *
   * For x : Int,
   *
   *   (bag.count x (bag x 3))
   *   ---> 3
   */
  COUNT_BAG_MAKE,
  /**
   * The set of a bag with one element has it once, when it occurs at all.
   *
   * For x : Int and c : Int,
   *
   *   (bag.setof (bag x 3))
   *   ---> (bag x 1)
   *
   *   (bag.setof (bag x c))
   *   ---> (bag x (ite (>= c 1) 1 0))
   */
  SETOF_BAG_MAKE,
  /**
   * Two distinct bag constants are not equal.
   *
   *   (= (bag 1 2) (bag 1 3))
   *   ---> false
   */
  EQ_CONST_FALSE,
  /**
   * An equality whose sides rewrite to one term is true. (An equality of one
   * term with itself is IDENTICAL_NODES, before its sides are rewritten.)
   *
   * For A : (Bag Int),
   *
   *   (= (bag.union_disjoint A (as bag.empty (Bag Int))) A)
   *   ---> true
   */
  EQ_REFL,
  /**
   * An equality of bags with its sides in one order: the smaller node first.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (= B A)
   *   ---> (= A B)
   */
  EQ_SYM,
  /**
   * A filter of a constant bag is evaluated.
   *
   * For p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.filter p (bag.union_disjoint (bag 1 2) (bag (- 3) 1)))
   *   ---> (bag 1 2)
   */
  FILTER_CONST,
  /**
   * A filter of a bag with one element keeps the element as often as it passes.
   *
   * For x : Int and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.filter p (bag x 2))
   *   ---> (bag x (ite (> x 0) 2 0))
   */
  FILTER_BAG_MAKE,
  /**
   * A filter of a union is the union of the filters.
   *
   * For A : (Bag Int) and B : (Bag Int) and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.filter p (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.filter p A) (bag.filter p B))
   */
  FILTER_UNION_DISJOINT,
  /**
   * A filter of a filter is one filter, by the conjunction.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
   *               (bag.filter
   *                 (lambda ((t (Tuple Int Int))) (< ((_ tuple.select 1) t) 7))
   *                 X))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int)))
   *            (and (> ((_ tuple.select 0) t) 3) (< ((_ tuple.select 1) t) 7)))
   *          X)
   *
   * Both predicates must be lambdas; it applies only with the higher-order
   * flag, see the constructor of BagsRewriter.
   */
  FILTER_FILTER,
  /**
   * A filter of a map is a map of a filter: the filter reads the map's result.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((s (Tuple Int))) (> ((_ tuple.select 0) s) 3))
   *               (bag.map
   *                 (lambda ((t (Tuple Int Int)))
   *                   (tuple ((_ tuple.select 1) t)))
   *                 X))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 1) t) 3))
   *            X))
   *
   * The map must be a lambda; it applies only with the higher-order flag, see
   * the constructor of BagsRewriter.
   */
  FILTER_MAP,
  /**
   * A filter of a set is the set of the filter.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
   *               (bag.setof X))
   *   ---> (bag.setof
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
   *            X))
   */
  FILTER_SETOF,
  /**
   * A map of a map is one map, by the composition.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.map (lambda ((s (Tuple Int))) (tuple (+ ((_ tuple.select 0) s) 1)))
   *            (bag.map
   *              (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
   *              X))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int)))
   *            (tuple (+ ((_ tuple.select 1) t) 1)))
   *          X)
   *
   * Both functions must be lambdas; it applies only with the higher-order flag,
   * see the constructor of BagsRewriter.
   */
  MAP_MAP,
  /**
   * A map of the left factor of a product is a map of the product
   * (see BagsRewriter::rewriteProductOfMap), so that the maps of a query end up
   * above its product.
   *
   * For A : (Bag (Tuple Int Int)) and B : (Bag (Tuple Int Int)),
   *
   *   (table.product
   *     (bag.map (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 1) s)))
   *              A)
   *     B)
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (tuple ((_ tuple.select 1) t)
   *                   ((_ tuple.select 2) t)
   *                   ((_ tuple.select 3) t)))
   *          (table.product A B))
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PRODUCT_MAP_LEFT,
  /**
   * A map of the right factor of a product is a map of the product, reading the
   * columns of the right factor after those of the left
   * (see BagsRewriter::rewriteProductOfMap).
   *
   * For A : (Bag (Tuple Int Int)) and B : (Bag (Tuple Int Int)),
   *
   *   (table.product A
   *                  (bag.map
   *                    (lambda ((s (Tuple Int Int)))
   *                      (tuple ((_ tuple.select 1) s)))
   *                    B))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   ((_ tuple.select 1) t)
   *                   ((_ tuple.select 3) t)))
   *          (table.product A B))
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PRODUCT_MAP_RIGHT,
  /**
   * A filter of the left factor of a product is a filter of the product
   * (see BagsRewriter::rewriteProductOfFilter), so that the filters of a query
   * end up above its product.
   *
   * For A : (Bag (Tuple Int Int)) and B : (Bag (Tuple Int Int)),
   *
   *   (table.product
   *     (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3))
   *                 A)
   *     B)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (> ((_ tuple.select 1) t) 3))
   *          (table.product A B))
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PRODUCT_FILTER_LEFT,
  /**
   * A filter of the right factor of a product is a filter of the product,
   * reading the columns of the right factor after those of the left
   * (see BagsRewriter::rewriteProductOfFilter).
   *
   * For A : (Bag (Tuple Int Int)) and B : (Bag (Tuple Int Int)),
   *
   *   (table.product A
   *                  (bag.filter
   *                    (lambda ((s (Tuple Int Int)))
   *                      (> ((_ tuple.select 1) s) 3))
   *                    B))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (> ((_ tuple.select 3) t) 3))
   *          (table.product A B))
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PRODUCT_FILTER_RIGHT,
  /**
   * A product of a union, on either side, is the union of the products.
   *
   * For A : (Bag (Tuple Int)) and B : (Bag (Tuple Int)) and
   * C : (Bag (Tuple Int)),
   *
   *   (table.product (bag.union_disjoint A B) C)
   *   ---> (bag.union_disjoint (table.product A C) (table.product B C))
   */
  PRODUCT_UNION_DISJOINT,
  /**
   * Products are nested to the right: the rows are flat tuples, so the nesting
   * is only a spelling.
   *
   * For A : (Bag (Tuple Int)) and B : (Bag (Tuple Int)) and
   * C : (Bag (Tuple Int)),
   *
   *   (table.product (table.product A B) C)
   *   ---> (table.product A (table.product B C))
   */
  PRODUCT_ASSOC,
  /**
   * The factors of a product in one order, the smaller node first, under a map
   * that puts the columns back, so that two queries that list their tables in
   * different orders have one product.
   *
   * For A : (Bag (Tuple Int)) and B : (Bag (Tuple Int)),
   *
   *   (table.product B A)
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int)))
   *            (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
   *          (table.product A B))
   *
   * Here A is the smaller node. It applies only with the higher-order flag, see
   * the constructor of BagsRewriter.
   */
  PRODUCT_SWAP,
  /**
   * A map, or a bag.setof, is empty when its argument is.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (= (bag.map (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
   *               X)
   *      (as bag.empty (Bag (Tuple Int))))
   *   ---> (= X (as bag.empty (Bag (Tuple Int Int))))
   *
   *   (= (bag.setof X) (as bag.empty (Bag (Tuple Int Int))))
   *   ---> (= X (as bag.empty (Bag (Tuple Int Int))))
   */
  EQ_EMPTY_ARG,
  /**
   * An aggregate of a map groups the rows of the map's argument, by the columns
   * the map copies to the group columns, and folds them through the map.
   *
   * For X : (Bag (Tuple Int Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))),
   *
   *   ((_ table.aggr 0) f
   *                     (tuple 0 0)
   *                     (bag.map
   *                       (lambda ((t (Tuple Int Int Int)))
   *                         (tuple ((_ tuple.select 2) t)
   *                                ((_ tuple.select 0) t)))
   *                       X))
   *   ---> ((_ table.aggr 2)
   *          (lambda ((t (Tuple Int Int Int)) (acc (Tuple Int Int)))
   *            (tuple ((_ tuple.select 2) t)
   *                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) t))))
   *          (tuple 0 0)
   *          X)
   */
  AGGREGATE_MAP,
  /**
   * A filter that every row passes is its argument.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((t (Tuple Int Int))) true) X)
   *   ---> X
   */
  FILTER_TRUE,
  /**
   * A filter that no row passes is empty.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((t (Tuple Int Int))) false) X)
   *   ---> (as bag.empty (Bag (Tuple Int Int)))
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int)))
   *       (and (> ((_ tuple.select 0) t) 3)
   *            (not (> ((_ tuple.select 0) t) 3))))
   *     X)
   *   ---> (as bag.empty (Bag (Tuple Int Int)))
   */
  FILTER_FALSE,
  /**
   * The conjuncts of a filter in one order, that of their alpha keys
   * (see BagsRewriter::alphaKey), and without duplicates, so that two filters
   * by the same conjuncts are one term.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int)))
   *       (and (< ((_ tuple.select 1) t) 7)
   *            (> ((_ tuple.select 0) t) 3)
   *            (< ((_ tuple.select 1) t) 7)))
   *     X)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int)))
   *            (and (> ((_ tuple.select 0) t) 3) (< ((_ tuple.select 1) t) 7)))
   *          X)
   */
  FILTER_SORT_CONJUNCTS,
  /**
   * Lambdas that differ only in the names of their variables become one node:
   * their variables are renamed to t_N and acc_N, with N the id of the lambda's
   * alpha key (see BagsRewriter::canonicalLambda). The solver then treats them
   * as one function.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
   *               X)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
   *          X)
   *
   * Both filters have the lambda
   * (lambda ((t_N (Tuple Int Int))) (> ((_ tuple.select 0) t_N) 3)), for the
   * same N.
   */
  CANONICAL_VARIABLE,
  /**
   * The columns of an aggregate's rows in one order, the copies of the group
   * columns first, with a map above it that puts them back.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   ((_ table.aggr 0)
   *     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *       (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t))
   *              ((_ tuple.select 0) t)))
   *     (tuple 0 0)
   *     X)
   *   ---> (bag.map
   *          (lambda ((r (Tuple Int Int)))
   *            (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *          ((_ table.aggr 0)
   *            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t)
   *                     (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
   *            (tuple 0 0)
   *            X))
   */
  AGGREGATE_SORT_OUTPUT,
  /**
   * An aggregate grouped by no column has one group, all of its table, even
   * when the table is empty.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int)))
   *         (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t)))),
   *
   *   (table.aggr f (tuple 0) X)
   *   ---> (bag (bag.fold f (tuple 0) X) 1)
   */
  AGGREGATE_NO_KEYS,
  /**
   * A fold of tuples whose components each read only their own accumulator is
   * the tuple of the folds of the components.
   *
   * For X : (Bag (Tuple Int)),
   *
   *   (bag.fold
   *     (lambda ((t (Tuple Int)) (acc (Tuple Int Int)))
   *       (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t))
   *              (+ ((_ tuple.select 1) acc) 1)))
   *     (tuple 0 0)
   *     X)
   *   ---> (tuple (bag.fold
   *                 (lambda ((t (Tuple Int)) (a Int))
   *                   (+ a ((_ tuple.select 0) t)))
   *                 0
   *                 X)
   *               (bag.fold (lambda ((t (Tuple Int)) (a Int)) (+ a 1)) 0 X))
   *
   * Here the sum and the count of the rows of X.
   */
  FOLD_TUPLE,
  /**
   * The set of a map with constant columns: of a map to a constant, that
   * constant once, unless the argument is empty; and otherwise the set of the
   * map without the constant columns, under a map that puts them back.
   *
   * For Y : (Bag (Tuple Int Int)),
   *
   *   (bag.setof (bag.map (lambda ((t (Tuple Int Int))) (tuple 5)) Y))
   *   ---> (bag (tuple 5) (ite (= Y (as bag.empty (Bag (Tuple Int Int)))) 0 1))
   *
   *   (bag.setof
   *     (bag.map
   *       (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t) 5))
   *       Y))
   *   ---> (bag.map (lambda ((r (Tuple Int))) (tuple ((_ tuple.select 0) r) 5))
   *                 (bag.setof
   *                   (bag.map
   *                     (lambda ((t (Tuple Int Int)))
   *                       (tuple ((_ tuple.select 1) t)))
   *                     Y)))
   */
  SETOF_MAP_CONSTANT,
  /**
   * A filter by a disjunction with a disjunct c that does not read the row,
   * such as SQL's EXISTS (subquery), is the union of the filter by c and the
   * filter by the rest without c: every row passes one of the two exactly when
   * it passes the disjunction, and never both.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int)) and
   *   c = (not (= Y (as bag.empty (Bag (Tuple Int))))),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int))) (or c (> ((_ tuple.select 0) t) 3)))
   *     X)
   *   ---> (bag.union_disjoint (bag.filter (lambda ((t (Tuple Int Int))) c) X)
   *                            (bag.filter
   *                              (lambda ((t (Tuple Int Int)))
   *                                (and (not c) (> ((_ tuple.select 0) t) 3)))
   *                              X))
   *
   * Also for a disjunct that asks about a bag and reads nothing but the row,
   * such as IN (subquery).
   */
  FILTER_SPLIT_CLOSED,
  /**
   * A join with a set Z whose row the join's equations fix, by all its columns
   * or by a key, and whose columns the map above does not read, is a filter by
   * the existence of the matching row of Z (see BagsRewriter::rewriteSemiJoin).
   *
   * For Y : (Bag (Tuple Int Int)) and Z : (Bag (Tuple Int)),
   *
   * given the assertion that column 0 is a key of Z, which makes Z a set
   * (see BagsRewriter::recordFacts):
   *
   *   (assert (= (bag.setof ((_ table.project 0) Z)) ((_ table.project 0) Z)))
   *
   *   (bag.map
   *     (lambda ((t (Tuple Int Int Int))) (tuple ((_ tuple.select 1) t)))
   *     (bag.filter
   *       (lambda ((t (Tuple Int Int Int)))
   *         (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *       (table.product Y Z)))
   *   ---> (bag.map
   *          (lambda ((a (Tuple Int Int))) (tuple ((_ tuple.select 1) a)))
   *          (bag.filter
   *            (lambda ((a (Tuple Int Int)))
   *              (not (= (bag.filter
   *                        (lambda ((b (Tuple Int)))
   *                          (= ((_ tuple.select 0) a) ((_ tuple.select 0) b)))
   *                        Z)
   *                      (as bag.empty (Bag (Tuple Int))))))
   *            Y))
   */
  SEMI_JOIN,
  /**
   * In the body of a filter or a map over the rows r of Y, the emptiness of a
   * filter of X that compares a column of X with a column of r becomes a
   * membership of that column of r in the projection of X, which reads no r
   * (see BagsRewriter::normalizeEmptiness).
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.filter
   *     (lambda ((r (Tuple Int Int)))
   *       (not (= (bag.filter
   *                 (lambda ((s (Tuple Int Int)))
   *                   (= ((_ tuple.select 1) s) ((_ tuple.select 0) r)))
   *                 X)
   *               (as bag.empty (Bag (Tuple Int Int))))))
   *     Y)
   *   ---> (bag.filter
   *          (lambda ((r (Tuple Int Int)))
   *            (>= (bag.count (tuple ((_ tuple.select 0) r))
   *                           (bag.map
   *                             (lambda ((s (Tuple Int Int)))
   *                               (tuple ((_ tuple.select 1) s)))
   *                             X))
   *                1))
   *          Y)
   *
   * This is SQL's Y WHERE EXISTS (SELECT * FROM X WHERE X.c1 = Y.c0),
   * decorrelated.
   */
  EQ_EMPTY_FILTER_DECORRELATE,
  /**
   * A column of an aggregate that the map above it does not read is not
   * computed. Also with a filter between the map and the aggregate that does
   * not read it.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))),
   *
   *   (bag.map
   *     (lambda ((r (Tuple Int Int Int)))
   *       (tuple ((_ tuple.select 0) r) ((_ tuple.select 2) r)))
   *     ((_ table.aggr 0) f (tuple 0 0 0) X))
   *   ---> (bag.map
   *          (lambda ((r (Tuple Int Int)))
   *            (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
   *          ((_ table.aggr 0)
   *            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
   *            (tuple 0 0)
   *            X))
   *
   * Here the map reads the group column and the count of rows, not the sum.
   */
  AGGREGATE_DEAD_COLUMNS,
  /**
   * A fold whose step reads neither the row nor the accumulator gives the step
   * after any row, and the initial value for no row.
   *
   * For X : (Bag Int),
   *
   *   (bag.fold (lambda ((t Int) (acc Int)) 7) 0 X)
   *   ---> (ite (= X (as bag.empty (Bag Int))) 0 7)
   */
  FOLD_CONSTANT_STEP,
  /**
   * A map over a filter that fixes a column to a constant reads the constant.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   P = (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 1) s) 5)),
   *
   *   (bag.map
   *     (lambda ((t (Tuple Int Int)))
   *       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0))
   *     (bag.filter P X))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t) 5 0))
   *          (bag.filter P X))
   *
   * Also, over an aggregate whose count of rows the filter tests positive, for
   * the columns every group computes as a constant.
   */
  MAP_FIXED_COLUMNS,
  /**
   * The set of a projection onto columns in another order than theirs is the
   * set of the projection onto the sorted columns, with a map above it that
   * puts them back. The map is injective, so it commutes with removing
   * duplicates.
   *
   * For X : (Bag (Tuple Int Int Int)),
   *
   *   (bag.setof
   *     (bag.map
   *       (lambda ((t (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
   *       X))
   *   ---> (bag.map
   *          (lambda ((r (Tuple Int Int)))
   *            (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
   *          (bag.setof
   *            (bag.map
   *              (lambda ((t (Tuple Int Int Int)))
   *                (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *              X)))
   */
  SETOF_PROJECTION_SORT,
  /**
   * A conjunct that every row satisfies goes: here that column 0 of a row of
   * (table.product X Y), which comes from X, is in the projection of X onto
   * column 0 (see BagsRewriter::dropKnownMemberships).
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int Int Int)))
   *       (and (>= (bag.count (tuple ((_ tuple.select 0) t))
   *                           (bag.map
   *                             (lambda ((s (Tuple Int Int)))
   *                               (tuple ((_ tuple.select 0) s)))
   *                             X))
   *                1)
   *            (> ((_ tuple.select 3) t) 2)))
   *     (table.product X Y))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (> ((_ tuple.select 3) t) 2))
   *          (table.product X Y))
   *
   * Also a membership that another conjunct implies.
   */
  FILTER_KNOWN_MEMBERSHIP,
  /**
   * A count in a map whose probe has a constant where the map copies a column
   * of its argument: only the rows with that constant in that column can match,
   * and the column leaves the probe and the map.
   *
   * For X : (Bag (Tuple Int Int)) and b : Int,
   *
   *   (bag.count (tuple 5 b)
   *              (bag.map
   *                (lambda ((t (Tuple Int Int)))
   *                  (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
   *                X))
   *   ---> (bag.count (tuple b)
   *                   (bag.map
   *                     (lambda ((t (Tuple Int Int)))
   *                       (tuple ((_ tuple.select 0) t)))
   *                     (bag.filter
   *                       (lambda ((t (Tuple Int Int)))
   *                         (= ((_ tuple.select 1) t) 5))
   *                       X)))
   *
   * Also for X a table constant, as its own identity map; that form builds a
   * lambda, so it needs the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  COUNT_MAP_CONST_PROBE,
  /**
   * An aggregate grouped by a key of its table folds every group, one row,
   * once. Under a filter that drops the row the aggregate of an empty table
   * has, made of the initial values, it is a map of the table.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))) and
   *   Q = (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1)),
   *
   * given the assertion that column 0 is a key of X
   * (see BagsRewriter::recordFacts):
   *
   *   (assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
   *
   *   (bag.filter Q ((_ table.aggr 0) f (tuple 0 0 0) X))
   *   ---> (bag.filter Q
   *                    (bag.map
   *                      (lambda ((t (Tuple Int Int)))
   *                        (tuple ((_ tuple.select 0) t)
   *                               ((_ tuple.select 1) t)
   *                               1))
   *                      X))
   *
   * Q keeps the groups whose count of rows, column 2, is positive, as SQL's
   * GROUP BY does. Also for an aggregate among the factors of a product under
   * such a filter.
   */
  AGGREGATE_KEYED,
  /**
   * The null tests of columns that are never null are decided, in the lambdas
   * of filters, maps, folds and aggregates.
   *
   * For Y : (Bag (Tuple Int (Nullable Int))),
   *
   * given the assertion that column 1 of Y is NOT NULL
   * (see BagsRewriter::recordFacts):
   *
   *   (assert (= (bag.filter
   *                (lambda ((t (Tuple Int (Nullable Int))))
   *                  (= ((_ tuple.select 1) t)
   *                     (as nullable.null (Nullable Int))))
   *                Y)
   *              (as bag.empty (Bag (Tuple Int (Nullable Int))))))
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int (Nullable Int))))
   *       (and (nullable.is_some ((_ tuple.select 1) t))
   *            (> ((_ tuple.select 0) t) 3)))
   *     Y)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int (Nullable Int))))
   *            (> ((_ tuple.select 0) t) 3))
   *          Y)
   *
   * A column is also never null in the rows of a filter that tests it, and of
   * maps, products and unions that keep a never-null column.
   */
  NOT_NULL_COLUMNS,
  /**
   * The two conjuncts that say a nullable Boolean b holds, (nullable.is_some b)
   * and (nullable.val b), become the one formula they say
   * (see BagsRewriter::normalizeTruth).
   *
   * For Y : (Bag (Tuple Int (Nullable Int))) and
   *   b = (ite (nullable.is_some ((_ tuple.select 1) t))
   *            (nullable.some (> (nullable.val ((_ tuple.select 1) t)) 3))
   *            (as nullable.null (Nullable Bool))),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int (Nullable Int))))
   *       (and (nullable.is_some b) (nullable.val b)))
   *     Y)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int (Nullable Int))))
   *            (and (nullable.is_some ((_ tuple.select 1) t))
   *                 (> (nullable.val ((_ tuple.select 1) t)) 3)))
   *          Y)
   *
   * b is SQL's three-valued test that column 1 is greater than 3; the row
   * passes when b is true, not when it is false or null.
   */
  FILTER_NULLABLE_TRUTH,
  /**
   * A map over a filter that equates two columns reads the first of them, so
   * that two queries that read either become one term.
   *
   * For X : (Bag (Tuple Int Int Int)) and
   *   P = (lambda ((s (Tuple Int Int Int)))
   *         (= ((_ tuple.select 0) s) ((_ tuple.select 2) s))),
   *
   *   (bag.map
   *     (lambda ((t (Tuple Int Int Int))) (tuple ((_ tuple.select 2) t)))
   *     (bag.filter P X))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int Int))) (tuple ((_ tuple.select 0) t)))
   *          (bag.filter P X))
   */
  MAP_EQUAL_COLUMNS,
  /**
   * A fold of a map folds the map's argument, reading each row through the map.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.fold
   *     (lambda ((t (Tuple Int)) (acc Int)) (+ acc ((_ tuple.select 0) t)))
   *     0
   *     (bag.map (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 1) s)))
   *              X))
   *   ---> (bag.fold
   *          (lambda ((s (Tuple Int Int)) (acc Int))
   *            (+ acc ((_ tuple.select 1) s)))
   *          0
   *          X)
   *
   * The map's function must be a lambda that does not read the accumulator.
   */
  FOLD_MAP,
  /**
   * An aggregate over a union of parts that share no value of the group
   * columns, under a filter that keeps the groups some row reached, is the
   * union of the aggregates of the parts: every group is one part's.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))) and
   *   Q = (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1)) and
   *   h = (lambda ((r (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r))) and
   *   U1 = (bag.filter
   *          (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 0) s) 1))
   *          X) and
   *   U2 = (bag.filter
   *          (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 0) s) 2))
   *          Y),
   *
   *   (bag.map h
   *            (bag.filter Q
   *                        ((_ table.aggr 0)
   *                          f
   *                          (tuple 0 0 0)
   *                          (bag.union_disjoint U1 U2))))
   *   ---> (bag.map h
   *                 (bag.filter Q
   *                             (bag.union_disjoint
   *                               ((_ table.aggr 0) f (tuple 0 0 0) U1)
   *                               ((_ table.aggr 0) f (tuple 0 0 0) U2))))
   *
   * Here the rows of U1 have 1 in the group column and those of U2 have 2.
   */
  AGGREGATE_UNION_DISJOINT_KEYS,
  /**
   * A condition that the rows of one side of a join satisfy on a column the
   * join equates holds of the other side's column too, and joins the join's
   * predicate, so that a condition written on either side of a join is on both.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)) and
   *   Z = (bag.setof
   *         (bag.filter
   *           (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
   *           Y)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int Int Int)))
   *       (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *     (table.product X Z))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (and (= ((_ tuple.select 0) t) ((_ tuple.select 2) t))
   *                 (> ((_ tuple.select 0) t) 3)))
   *          (table.product X Z))
   *
   * The rows of Z have column 0 greater than 3, so the rows that pass have
   * column 0 of X greater than 3 as well.
   */
  FILTER_JOIN_TRANSITIVE,
  /**
   * A map that copies every column of its argument, in order, is its argument.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.map
   *     (lambda ((t (Tuple Int Int)))
   *       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
   *     X)
   *   ---> X
   *
   * The map's tuple has all the columns of X, here both of them.
   */
  MAP_IDENTITY,
  /**
   * A filter whose conjuncts fix one term to two distinct constants keeps no
   * row; and a conjunct that another one implies goes.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int (Nullable Int))),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int)))
   *       (and (= ((_ tuple.select 0) t) 1) (= ((_ tuple.select 0) t) 2)))
   *     X)
   *   ---> (as bag.empty (Bag (Tuple Int Int)))
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int (Nullable Int))))
   *       (and (nullable.is_some ((_ tuple.select 1) t))
   *            (= ((_ tuple.select 1) t) (nullable.some 5))))
   *     Y)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int (Nullable Int))))
   *            (= ((_ tuple.select 1) t) (nullable.some 5)))
   *          Y)
   */
  FILTER_CONFLICTING_CONSTANTS,
  /**
   * A projection is a map, which the rules for maps then reach.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   ((_ table.project 1 0) X)
   *   ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t)) X)
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PROJECT_TO_MAP,
  /**
   * Every element of the empty bag satisfies any predicate.
   *
   * For p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.all p (as bag.empty (Bag Int)))
   *   ---> true
   */
  ALL_EMPTY,
  /**
   * Every element of a bag with one element satisfies p when it does, or when
   * it does not occur.
   *
   * For x : Int and c : Int and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.all p (bag x c))
   *   ---> (or (> x 0) (<= c 0))
   */
  ALL_BAG_MAKE,
  /**
   * Every element of a union satisfies p when every element of each side does.
   *
   * For A : (Bag Int) and B : (Bag Int) and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.all p (bag.union_disjoint A B))
   *   ---> (and (bag.all p A) (bag.all p B))
   */
  ALL_UNION_DISJOINT,
  /**
   * Every element of A satisfies p when filtering A by p keeps all of it.
   *
   * For A : (Bag Int) and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.all p A)
   *   ---> (= (bag.filter p A) A)
   */
  ALL_FILTER,
  /**
   * No element of the empty bag satisfies a predicate.
   *
   * For p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.some p (as bag.empty (Bag Int)))
   *   ---> false
   */
  SOME_EMPTY,
  /**
   * Some element of a bag with one element satisfies p when it occurs and
   * satisfies p.
   *
   * For x : Int and c : Int and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.some p (bag x c))
   *   ---> (and (> c 0) (> x 0))
   */
  SOME_BAG_MAKE,
  /**
   * Some element of a union satisfies p when some element of either side does.
   *
   * For A : (Bag Int) and B : (Bag Int) and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.some p (bag.union_disjoint A B))
   *   ---> (or (bag.some p A) (bag.some p B))
   */
  SOME_UNION_DISJOINT,
  /**
   * Some element of A satisfies p when filtering A by p keeps something.
   *
   * For A : (Bag Int) and
   *   p = (lambda ((y Int)) (> y 0)),
   *
   *   (bag.some p A)
   *   ---> (not (= (bag.filter p A) (as bag.empty (Bag Int))))
   */
  SOME_FILTER,
  FROM_SINGLETON,
  /**
   * A fold over a bag with one element, a positive constant number of times, is
   * unrolled.
   *
   * For x : Int and
   *   f = (lambda ((y Int) (a Int)) (+ y a)),
   *
   *   (bag.fold f 0 (bag x 2))
   *   ---> (+ x (+ x 0))
   */
  FOLD_BAG,
  /**
   * A fold over a constant bag is evaluated.
   *
   * For f = (lambda ((y Int) (a Int)) (+ y a)),
   *
   *   (bag.fold f 0 (bag.union_disjoint (bag 3 2) (bag 4 1)))
   *   ---> 10
   */
  FOLD_CONST,
  /**
   * A fold over a union folds one side, then the other from its result; the
   * sides are ordered, the smaller node first.
   *
   * For A : (Bag Int) and B : (Bag Int) and
   *   f = (lambda ((y Int) (a Int)) (+ y a)),
   *
   *   (bag.fold f 0 (bag.union_disjoint A B))
   *   ---> (bag.fold f (bag.fold f 0 A) B)
   */
  FOLD_UNION_DISJOINT,
  /**
   * A bag equals itself, before its sides are rewritten.
   *
   * For A : (Bag Int),
   *
   *   (= A A)
   *   ---> true
   */
  IDENTICAL_NODES,
  /**
   * The intersection with the empty bag, on the left, is empty.
   *
   * For A : (Bag Int),
   *
   *   (bag.inter_min (as bag.empty (Bag Int)) A)
   *   ---> (as bag.empty (Bag Int))
   */
  INTERSECTION_EMPTY_LEFT,
  /**
   * The intersection with the empty bag, on the right, is empty.
   *
   * For A : (Bag Int),
   *
   *   (bag.inter_min A (as bag.empty (Bag Int)))
   *   ---> (as bag.empty (Bag Int))
   */
  INTERSECTION_EMPTY_RIGHT,
  /**
   * The intersection of a bag with itself is the bag.
   *
   * For A : (Bag Int),
   *
   *   (bag.inter_min A A)
   *   ---> A
   */
  INTERSECTION_SAME,
  /**
   * The intersection of A with a union that contains A is A; also for
   * bag.union_max, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.inter_min A (bag.union_disjoint A B))
   *   ---> A
   */
  INTERSECTION_SHARED_LEFT,
  /**
   * The intersection of a union that contains A with A is A; also for
   * bag.union_max, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.inter_min (bag.union_max A B) A)
   *   ---> A
   */
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_BAG_MAKE,
  /**
   * A map of a constant bag is evaluated.
   *
   *   (bag.map (lambda ((y Int)) (+ y 1)) (bag 1 3))
   *   ---> (bag 2 3)
   */
  MAP_CONST,
  /**
   * A map of a bag with one element maps the element.
   *
   * For x : Int,
   *
   *   (bag.map (lambda ((y Int)) (+ y 1)) (bag x 3))
   *   ---> (bag (+ x 1) 3)
   */
  MAP_BAG_MAKE,
  /**
   * A map of a union is the union of the maps.
   *
   * For A : (Bag Int) and B : (Bag Int) and
   *   g = (lambda ((y Int)) (+ y 1)),
   *
   *   (bag.map g (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint (bag.map g A) (bag.map g B))
   */
  MAP_UNION_DISJOINT,
  /**
   * Membership is a positive count.
   *
   * For x : Int and A : (Bag Int),
   *
   *   (bag.member x A)
   *   ---> (>= (bag.count x A) 1)
   */
  MEMBER,
  /**
   * A partition of a constant bag is evaluated: its parts are the classes of
   * the equivalence relation.
   *
   * For r = (lambda ((a Int) (b Int)) (= (mod a 2) (mod b 2))),
   *
   *   (bag.partition r (bag.union_disjoint (bag 1 1) (bag 2 1)))
   *   ---> (bag.union_disjoint (bag (bag 1 1) 1) (bag (bag 2 1) 1))
   */
  PARTITION_CONST,
  /**
   * A product with the empty table, on either side, is empty.
   *
   * For X : (Bag (Tuple Int)),
   *
   *   (table.product X (as bag.empty (Bag (Tuple Int))))
   *   ---> (as bag.empty (Bag (Tuple Int Int)))
   */
  PRODUCT_EMPTY,
  /**
   * Removing from A a union that contains A leaves nothing; also for
   * bag.union_max, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_remove A (bag.union_disjoint A B))
   *   ---> (as bag.empty (Bag Int))
   */
  REMOVE_FROM_UNION,
  /**
   * Removing A from an intersection with A leaves nothing, on either side of
   * the intersection.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_remove (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag Int))
   */
  REMOVE_MIN,
  /**
   * Removing the empty bag changes nothing, and removing from the empty bag
   * leaves it empty.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_remove A (as bag.empty (Bag Int)))
   *   ---> A
   *
   *   (bag.difference_remove (as bag.empty (Bag Int)) B)
   *   ---> (as bag.empty (Bag Int))
   */
  REMOVE_RETURN_LEFT,
  /**
   * Removing a bag from itself leaves nothing.
   *
   * For A : (Bag Int),
   *
   *   (bag.difference_remove A A)
   *   ---> (as bag.empty (Bag Int))
   */
  REMOVE_SAME,
  /**
   * A is a subbag of B when subtracting B from A leaves nothing.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.subbag A B)
   *   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag Int)))
   */
  SUB_BAG,
  /**
   * Subtracting A from a union of A and B, A on the left, leaves B.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_subtract (bag.union_disjoint A B) A)
   *   ---> B
   */
  SUBTRACT_DISJOINT_SHARED_LEFT,
  /**
   * Subtracting A from a union of B and A, A on the right, leaves B.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_subtract (bag.union_disjoint B A) A)
   *   ---> B
   */
  SUBTRACT_DISJOINT_SHARED_RIGHT,
  /**
   * Subtracting from A a union that contains A leaves nothing; also for
   * bag.union_max, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_subtract A (bag.union_max A B))
   *   ---> (as bag.empty (Bag Int))
   */
  SUBTRACT_FROM_UNION,
  /**
   * Subtracting A from an intersection with A leaves nothing, on either side of
   * the intersection.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_subtract (bag.inter_min A B) A)
   *   ---> (as bag.empty (Bag Int))
   */
  SUBTRACT_MIN,
  /**
   * Subtracting the empty bag changes nothing, and subtracting from the empty
   * bag leaves it empty.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.difference_subtract A (as bag.empty (Bag Int)))
   *   ---> A
   *
   *   (bag.difference_subtract (as bag.empty (Bag Int)) B)
   *   ---> (as bag.empty (Bag Int))
   */
  SUBTRACT_RETURN_LEFT,
  /**
   * Subtracting a bag from itself leaves nothing.
   *
   * For A : (Bag Int),
   *
   *   (bag.difference_subtract A A)
   *   ---> (as bag.empty (Bag Int))
   */
  SUBTRACT_SAME,
  TO_SINGLETON,
  /**
   * The union with the empty bag, on the left, is the other side.
   *
   * For A : (Bag Int),
   *
   *   (bag.union_disjoint (as bag.empty (Bag Int)) A)
   *   ---> A
   */
  UNION_DISJOINT_EMPTY_LEFT,
  /**
   * The union with the empty bag, on the right, is the other side.
   *
   * For A : (Bag Int),
   *
   *   (bag.union_disjoint A (as bag.empty (Bag Int)))
   *   ---> A
   */
  UNION_DISJOINT_EMPTY_RIGHT,
  /**
   * The maximum and the minimum of two counts add up to their sum.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B))
   *   ---> (bag.union_disjoint A B)
   */
  UNION_DISJOINT_MAX_MIN,
  /**
   * The maximum union with the empty bag, on the left, is the other side.
   *
   * For A : (Bag Int),
   *
   *   (bag.union_max (as bag.empty (Bag Int)) A)
   *   ---> A
   */
  UNION_MAX_EMPTY,
  /**
   * The maximum union of a bag with itself, or with the empty bag on the right,
   * is the bag.
   *
   * For A : (Bag Int),
   *
   *   (bag.union_max A A)
   *   ---> A
   *
   *   (bag.union_max A (as bag.empty (Bag Int)))
   *   ---> A
   */
  UNION_MAX_SAME_OR_EMPTY,
  /**
   * The maximum union of A with a union that contains A is that union; also for
   * bag.union_disjoint, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.union_max A (bag.union_disjoint A B))
   *   ---> (bag.union_disjoint A B)
   */
  UNION_MAX_UNION_LEFT,
  /**
   * The maximum union of a union that contains A with A is that union; also for
   * bag.union_disjoint, and with A second in the union.
   *
   * For A : (Bag Int) and B : (Bag Int),
   *
   *   (bag.union_max (bag.union_max A B) A)
   *   ---> (bag.union_max A B)
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

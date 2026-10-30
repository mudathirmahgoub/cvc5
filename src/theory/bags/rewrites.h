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
   * The set of a set is the set.
   *
   * For A : (Bag (Tuple Int Int)),
   *
   *   (bag.setof (bag.setof A))
   *   ---> (bag.setof A)
   */
  SETOF_SETOF,
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
   * A conjunct of a filter over an aggregate that reads only copies of group
   * columns filters the rows of the table before grouping, when the conjuncts
   * that stay reject the row of initial values
   * (see BagsRewriter::rejectsInitialRow).
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))),
   *
   *   (bag.filter
   *     (lambda ((r (Tuple Int Int Int)))
   *       (and (> ((_ tuple.select 0) r) 3) (>= ((_ tuple.select 2) r) 1)))
   *     ((_ table.aggr 0) f (tuple 0 0 0) X))
   *   ---> (bag.filter
   *          (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1))
   *          ((_ table.aggr 0) f
   *                            (tuple 0 0 0)
   *                            (bag.filter
   *                              (lambda ((t (Tuple Int Int)))
   *                                (> ((_ tuple.select 0) t) 3))
   *                              X)))
   */
  FILTER_AGGREGATE,
  /**
   * The group columns of an aggregate or a partition, sorted and without
   * repeats.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))),
   *
   *   ((_ table.aggr 1 0 1) f (tuple 0 0) X)
   *   ---> ((_ table.aggr 0 1) f (tuple 0 0) X)
   *
   *   ((_ table.group 1 0) X)
   *   ---> ((_ table.group 0 1) X)
   */
  SORTED_KEYS,
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
   * A product with a bag of one row, present once or when a condition holds, is
   * a map that adds the row's columns, under a filter by the condition.
   *
   * For A : (Bag (Tuple Int Int)) and b : Bool,
   *
   *   (table.product A (bag (tuple 7) (ite b 1 0)))
   *   ---> (bag.filter (lambda ((r (Tuple Int Int Int))) b)
   *                    (bag.map
   *                      (lambda ((t (Tuple Int Int)))
   *                        (tuple ((_ tuple.select 0) t)
   *                               ((_ tuple.select 1) t)
   *                               7))
   *                      A))
   *
   * It applies only with the higher-order flag, see the constructor of
   * BagsRewriter.
   */
  PRODUCT_BAG_MAKE,
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
   * A map whose body asks a question about a bag that reads no variable but the
   * row, as SQL's EXISTS or IN as a column, is the union of the map over the
   * rows where the answer is true and the map over those where it is false,
   * each with the answer in place.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int)),
   *
   *   (bag.map
   *     (lambda ((t (Tuple Int Int)))
   *       (tuple ((_ tuple.select 0) t)
   *              (>= (bag.count (tuple ((_ tuple.select 1) t)) Y) 1)))
   *     X)
   *   ---> (bag.union_disjoint
   *          (bag.map
   *            (lambda ((t (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t) true))
   *            (bag.filter
   *              (lambda ((t (Tuple Int Int)))
   *                (>= (bag.count (tuple ((_ tuple.select 1) t)) Y) 1))
   *              X))
   *          (bag.map
   *            (lambda ((t (Tuple Int Int)))
   *              (tuple ((_ tuple.select 0) t) false))
   *            (bag.filter
   *              (lambda ((t (Tuple Int Int)))
   *                (not (>= (bag.count (tuple ((_ tuple.select 1) t)) Y) 1)))
   *              X)))
   */
  MAP_SPLIT_CLOSED,
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
   * A count in a projection of a filter: a conjunct of the filter that reads
   * only the projected columns holds of all the rows that give the probe or of
   * none, so it is decided on the probe instead.
   *
   * For X : (Bag (Tuple Int Int)) and a : Int,
   *
   *   (bag.count (tuple a)
   *              (bag.map
   *                (lambda ((t (Tuple Int Int)))
   *                  (tuple ((_ tuple.select 0) t)))
   *                (bag.filter
   *                  (lambda ((t (Tuple Int Int)))
   *                    (and (> ((_ tuple.select 0) t) 3)
   *                         (< ((_ tuple.select 1) t) 7)))
   *                  X)))
   *   ---> (ite (> a 3)
   *             (bag.count (tuple a)
   *                        (bag.map
   *                          (lambda ((t (Tuple Int Int)))
   *                            (tuple ((_ tuple.select 0) t)))
   *                          (bag.filter
   *                            (lambda ((t (Tuple Int Int)))
   *                              (< ((_ tuple.select 1) t) 7))
   *                            X)))
   *             0)
   */
  COUNT_MAP_FILTER_KEYS,
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
   * In an aggregate over a filter that fixes a column to a constant, every row
   * has that constant: the step reads it instead of the column, and a group
   * column it fixes splits no group.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                ((_ tuple.select 1) t)
   *                (+ 1 ((_ tuple.select 2) acc)))) and
   *   P = (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 1) s) 5)),
   *
   *   ((_ table.aggr 0 1) f (tuple 0 0 0) (bag.filter P X))
   *   ---> ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *            (tuple ((_ tuple.select 0) t) 5 (+ 1 ((_ tuple.select 2) acc))))
   *          (tuple 0 0 0)
   *          (bag.filter P X))
   */
  AGGREGATE_FIXED_COLUMNS,
  /**
   * A map over a filter that keeps every column of the rows that pass, each
   * either the row's own or the constant the filter fixes it to, is the filter.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   P = (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 1) s) 5)),
   *
   *   (bag.map (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t) 5))
   *            (bag.filter P X))
   *   ---> (bag.filter P X)
   */
  MAP_IDENTITY_ON_FILTER,
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
   * An aggregate over a union of maps by one function is an aggregate over the
   * map of the union, which AGGREGATE_MAP then rewrites; the rule applies only
   * when that one does.
   *
   * For X1 : (Bag (Tuple Int Int Int)) and X2 : (Bag (Tuple Int Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))) and
   *   g = (lambda ((t (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t))),
   *
   *   ((_ table.aggr 0) f
   *                     (tuple 0 0)
   *                     (bag.union_disjoint (bag.map g X1) (bag.map g X2)))
   *   ---> ((_ table.aggr 2)
   *          (lambda ((t (Tuple Int Int Int)) (acc (Tuple Int Int)))
   *            (tuple ((_ tuple.select 2) t)
   *                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) t))))
   *          (tuple 0 0)
   *          (bag.union_disjoint X1 X2))
   */
  AGGREGATE_UNION_OF_MAPS,
  /**
   * An aggregate over a union of aggregates by the same group columns, which
   * merges their columns (a sum of counts or sums, a minimum of minimums, a
   * maximum of maximums), is one aggregate over the union of their tables.
   *
   * For X1 : (Bag (Tuple Int Int)) and X2 : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (nullable.some
   *                  (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                (+ 1 ((_ tuple.select 2) acc)))) and
   *   Q = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (>= ((_ tuple.select 2) r) 1)) and
   *   h = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r))) and
   *   g = (lambda ((t (Tuple Int (Nullable Int) Int))
   *                (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 1) acc))
   *                     ((_ tuple.select 1) t)
   *                     (nullable.some
   *                       (+ (nullable.val ((_ tuple.select 1) acc))
   *                          (nullable.val ((_ tuple.select 1) t)))))
   *                (+ 1 ((_ tuple.select 2) acc)))),
   *
   *   (bag.map h
   *            (bag.filter Q
   *                        ((_ table.aggr 0)
   *                          g
   *                          (tuple 0 (as nullable.null (Nullable Int)) 0)
   *                          (bag.union_disjoint
   *                            (bag.filter
   *                              Q
   *                              ((_ table.aggr 0)
   *                                f
   *                                (tuple 0 (nullable.some 0) 0)
   *                                X1))
   *                            (bag.filter
   *                              Q
   *                              ((_ table.aggr 0)
   *                                f
   *                                (tuple 0 (nullable.some 0) 0)
   *                                X2))))))
   *   ---> (bag.map h
   *                 (bag.filter Q
   *                             ((_ table.aggr 0)
   *                               f
   *                               (tuple 0 (nullable.some 0) 0)
   *                               (bag.union_disjoint X1 X2))))
   *
   * This is SQL's sum by column 0 of the counts by column 0 of X1 and of X2,
   * which is the count by column 0 of both. The rule also passes each row of
   * the one aggregate through g once, from the initial value of g, which
   * changes nothing here.
   */
  AGGREGATE_COLLAPSE,
  /**
   * An inner bag.setof under maps, filters and unions goes, under an outer
   * bag.setof: only whether an element occurs counts there.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   g = (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t))),
   *
   *   (bag.setof (bag.map g (bag.setof X)))
   *   ---> (bag.setof (bag.map g X))
   */
  SETOF_ABSORB,
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
   * A negated disjunction among the conjuncts of a filter is the conjunction of
   * the negations, conjuncts the other rules read one at a time.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int)))
   *       (and (> ((_ tuple.select 0) t) 3)
   *            (not (or (= ((_ tuple.select 1) t) 1)
   *                     (= ((_ tuple.select 1) t) 2)))))
   *     X)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int)))
   *            (and (> ((_ tuple.select 0) t) 3)
   *                 (not (= ((_ tuple.select 1) t) 1))
   *                 (not (= ((_ tuple.select 1) t) 2))))
   *          X)
   */
  FILTER_DE_MORGAN,
  /**
   * A count in a map that makes two columns equal: the probe occurs only when
   * its two columns are equal too, and the second goes from the probe and the
   * map.
   *
   * For X : (Bag (Tuple Int Int)) and a : Int and b : Int and c : Int,
   *
   *   (bag.count (tuple a b c)
   *              (bag.map
   *                (lambda ((t (Tuple Int Int)))
   *                  (tuple ((_ tuple.select 0) t)
   *                         ((_ tuple.select 1) t)
   *                         ((_ tuple.select 0) t)))
   *                X))
   *   ---> (ite (= a c)
   *             (bag.count (tuple a b)
   *                        (bag.map
   *                          (lambda ((t (Tuple Int Int)))
   *                            (tuple ((_ tuple.select 0) t)
   *                                   ((_ tuple.select 1) t)))
   *                          X))
   *             0)
   */
  COUNT_MAP_DUPLICATE_COLUMNS,
  /**
   * A count in a projection of a filter that equates a column with a term of an
   * enclosing row: the column joins the projection and the term the probe, and
   * the equation goes.
   *
   * For X : (Bag (Tuple Int Int)) and a : Int and e : Int,
   *
   *   (bag.count (tuple a)
   *              (bag.map
   *                (lambda ((t (Tuple Int Int)))
   *                  (tuple ((_ tuple.select 0) t)))
   *                (bag.filter
   *                  (lambda ((t (Tuple Int Int)))
   *                    (and (= ((_ tuple.select 1) t) e)
   *                         (> ((_ tuple.select 0) t) 3)))
   *                  X)))
   *   ---> (bag.count (tuple a e)
   *                   (bag.map
   *                     (lambda ((t (Tuple Int Int)))
   *                       (tuple ((_ tuple.select 0) t)
   *                              ((_ tuple.select 1) t)))
   *                     (bag.filter
   *                       (lambda ((t (Tuple Int Int)))
   *                         (> ((_ tuple.select 0) t) 3))
   *                       X)))
   *
   * Here e stands for the term of the enclosing row, as in SQL's correlated
   * subquery WHERE c1 = outer.c.
   */
  COUNT_MAP_FILTER_CORRELATED,
  /**
   * The set of a bag with no element twice is the bag
   * (see BagsRewriter::isSet).
   *
   * For X : (Bag (Tuple Int Int)),
   *
   * given the assertion that column 0 is a key of X, which makes X a set
   * (see BagsRewriter::recordFacts):
   *
   *   (assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
   *
   *   (bag.setof X)
   *   ---> X
   */
  SETOF_OF_SET,
  /**
   * Under duplicate removal, each factor of a product is the set of the columns
   * that the map and the filter read of it.
   *
   * For X : (Bag (Tuple Int Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.setof
   *     (bag.map
   *       (lambda ((t (Tuple Int Int Int Int Int)))
   *         (tuple ((_ tuple.select 0) t) ((_ tuple.select 4) t)))
   *       (bag.filter
   *         (lambda ((t (Tuple Int Int Int Int Int)))
   *           (= ((_ tuple.select 1) t) ((_ tuple.select 3) t)))
   *         (table.product X Y))))
   *   ---> (bag.setof
   *          (bag.map
   *            (lambda ((t (Tuple Int Int Int Int)))
   *              (tuple ((_ tuple.select 0) t) ((_ tuple.select 3) t)))
   *            (bag.filter
   *              (lambda ((t (Tuple Int Int Int Int)))
   *                (= ((_ tuple.select 1) t) ((_ tuple.select 2) t)))
   *              (table.product
   *                (bag.setof
   *                  (bag.map
   *                    (lambda ((t (Tuple Int Int Int)))
   *                      (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
   *                    X))
   *                (bag.setof
   *                  (bag.map
   *                    (lambda ((t (Tuple Int Int)))
   *                      (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
   *                    Y))))))
   */
  SETOF_PUSHDOWN,
  /**
   * A conjunct of a filter over a product that reads only a factor that is a
   * set goes into that factor.
   *
   * For X : (Bag (Tuple Int Int)) and Z : (Bag (Tuple Int)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int Int)))
   *       (and (> ((_ tuple.select 2) t) 3)
   *            (< ((_ tuple.select 0) t) ((_ tuple.select 2) t))))
   *     (table.product X (bag.setof Z)))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int Int)))
   *            (< ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *          (table.product X
   *                         (bag.setof
   *                           (bag.filter
   *                             (lambda ((s (Tuple Int)))
   *                               (> ((_ tuple.select 0) s) 3))
   *                             Z))))
   */
  FILTER_INTO_SETOF,
  /**
   * SEMI_JOIN under an aggregate: a join with a set that the aggregate reads
   * only through the columns the join equates to the other factor is a filter
   * of that factor by EXISTS (see BagsRewriter::rewriteSemiJoin).
   *
   * For A : (Bag (Tuple Int Int)) and Z : (Bag (Tuple Int)) and
   *   f = (lambda ((t (Tuple Int Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ 1 ((_ tuple.select 2) acc)))),
   *
   *   ((_ table.aggr 0) f
   *                     (tuple 0 0 0)
   *                     (bag.filter
   *                       (lambda ((t (Tuple Int Int Int)))
   *                         (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
   *                       (table.product A (bag.setof Z))))
   *   ---> ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                   (+ 1 ((_ tuple.select 2) acc))))
   *          (tuple 0 0 0)
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int)))
   *              (not (= (bag.filter
   *                        (lambda ((s (Tuple Int)))
   *                          (= ((_ tuple.select 0) t) ((_ tuple.select 0) s)))
   *                        (bag.setof Z))
   *                      (as bag.empty (Bag (Tuple Int))))))
   *            A))
   */
  AGGREGATE_SEMI_JOIN,
  /**
   * Under duplicate removal, a projection of a filter by membership of the
   * projected row in a bag is the intersection of the set of projected rows
   * with the set of that bag.
   *
   * For X : (Bag (Tuple Int Int)) and M : (Bag (Tuple Int)),
   *
   *   (bag.setof
   *     (bag.map (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
   *              (bag.filter
   *                (lambda ((t (Tuple Int Int)))
   *                  (>= (bag.count (tuple ((_ tuple.select 0) t)) M) 1))
   *                X)))
   *   ---> (bag.inter_min
   *          (bag.setof
   *            (bag.map
   *              (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
   *              X))
   *          (bag.setof M))
   *
   * Also when the projected rows are a set without duplicate removal.
   */
  SEMI_TO_INTERSECTION,
  /**
   * The arguments of an intersection, in the order of their node ids, so that
   * intersections of the same bags are one term.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.inter_min Y X)
   *   ---> (bag.inter_min X Y)
   */
  INTERSECTION_SORT,
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
   * A count in a map that makes a column a constant: the probe occurs only when
   * its column is that constant, and then as often as the probe without the
   * column occurs in the map without it.
   *
   * For X : (Bag (Tuple Int Int)) and a : Int and b : Int,
   *
   *   (bag.count (tuple a b)
   *              (bag.map
   *                (lambda ((t (Tuple Int Int)))
   *                  (tuple ((_ tuple.select 0) t) 5))
   *                X))
   *   ---> (ite (= b 5)
   *             (bag.count (tuple a)
   *                        (bag.map
   *                          (lambda ((t (Tuple Int Int)))
   *                            (tuple ((_ tuple.select 0) t)))
   *                          X))
   *             0)
   */
  COUNT_MAP_CONST_COLUMN,
  /**
   * A filter of an intersection is the intersection of the filters.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)) and
   *   P = (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3)),
   *
   *   (bag.filter P (bag.inter_min X Y))
   *   ---> (bag.inter_min (bag.filter P X) (bag.filter P Y))
   */
  FILTER_INTER_MIN,
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
   * A sum of integers read as reals is the integer sum, read as a real once.
   *
   * For X : (Bag (Tuple Int (Nullable Int))),
   *
   *   ((_ table.aggr 0)
   *     (lambda ((t (Tuple Int (Nullable Int)))
   *              (acc (Tuple Int (Nullable Real) Int)))
   *       (tuple ((_ tuple.select 0) t)
   *              (ite (= (as nullable.null (Nullable Real))
   *                      ((_ tuple.select 1) acc))
   *                   (nullable.some
   *                     (to_real (nullable.val ((_ tuple.select 1) t))))
   *                   (nullable.some
   *                     (+ (nullable.val ((_ tuple.select 1) acc))
   *                        (nullable.val ((_ tuple.select 1) t)))))
   *              (+ 1 ((_ tuple.select 2) acc))))
   *     (tuple 0 (as nullable.null (Nullable Real)) 0)
   *     X)
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (ite (= (as nullable.null (Nullable Int))
   *                           ((_ tuple.select 1) t))
   *                        (as nullable.null (Nullable Real))
   *                        (nullable.some
   *                          (to_real (nullable.val ((_ tuple.select 1) t)))))
   *                   ((_ tuple.select 2) t)))
   *          ((_ table.aggr 0)
   *            (lambda ((t (Tuple Int (Nullable Int)))
   *                     (acc (Tuple Int (Nullable Int) Int)))
   *              (tuple ((_ tuple.select 0) t)
   *                     (ite (= (as nullable.null (Nullable Int))
   *                             ((_ tuple.select 1) acc))
   *                          (nullable.some
   *                            (nullable.val ((_ tuple.select 1) t)))
   *                          (nullable.some
   *                            (+ (nullable.val ((_ tuple.select 1) t))
   *                               (nullable.val ((_ tuple.select 1) acc)))))
   *                     (+ 1 ((_ tuple.select 2) acc))))
   *            (tuple 0 (as nullable.null (Nullable Int)) 0)
   *            X))
   *
   * Here SQL's SUM(CAST(c1 AS REAL)).
   */
  AGGREGATE_INTEGER_SUM,
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
   * An aggregate of an aggregate, Calcite's form of DISTINCT aggregates, as a
   * join of an aggregate over the table with one over the distinct values the
   * inner aggregate groups by.
   *
   * For X : (Bag (Tuple Int (Nullable Int))) and
   *   fi = (lambda ((t (Tuple Int (Nullable Int)))
   *                 (acc (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *          (tuple ((_ tuple.select 0) t)
   *                 ((_ tuple.select 1) t)
   *                 (nullable.some
   *                   (+ 1 (nullable.val ((_ tuple.select 2) acc))))
   *                 (+ 1 ((_ tuple.select 3) acc)))) and
   *   P = (lambda ((r (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *         (>= ((_ tuple.select 3) r) 1)) and
   *   g = (lambda ((t (Tuple Int (Nullable Int) (Nullable Int) Int))
   *                (acc (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 1) t))
   *                     ((_ tuple.select 1) acc)
   *                     (nullable.some
   *                       (+ 1 (nullable.val ((_ tuple.select 1) acc)))))
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 2) acc))
   *                     ((_ tuple.select 2) t)
   *                     (nullable.some
   *                       (+ (nullable.val ((_ tuple.select 2) acc))
   *                          (nullable.val ((_ tuple.select 2) t)))))
   *                (+ 1 ((_ tuple.select 3) acc)))) and
   *   Q = (lambda ((q (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *         (>= ((_ tuple.select 3) q) 1)) and
   *   h = (lambda ((q (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) q)
   *                ((_ tuple.select 1) q)
   *                ((_ tuple.select 2) q))) and
   *   fA = (lambda ((t (Tuple Int (Nullable Int)))
   *                 (acc (Tuple Int (Nullable Int) Int)))
   *          (tuple ((_ tuple.select 0) t)
   *                 (nullable.some
   *                   (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                 (+ 1 ((_ tuple.select 2) acc)))) and
   *   fB = (lambda ((s (Tuple Int (Nullable Int)))
   *                 (acc (Tuple Int (Nullable Int) Int)))
   *          (tuple ((_ tuple.select 0) s)
   *                 (ite (= (as nullable.null (Nullable Int))
   *                         ((_ tuple.select 1) s))
   *                      ((_ tuple.select 1) acc)
   *                      (nullable.some
   *                        (+ 1 (nullable.val ((_ tuple.select 1) acc)))))
   *                 (+ 1 ((_ tuple.select 2) acc)))) and
   *   R = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (>= ((_ tuple.select 2) r) 1)) and
   *   J = (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int)))
   *         (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))) and
   *   m = (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) p)
   *                ((_ tuple.select 4) p)
   *                ((_ tuple.select 1) p)
   *                1)),
   *
   *   (bag.map h
   *            (bag.filter Q
   *                        ((_ table.aggr 0)
   *                          g
   *                          (tuple 0
   *                                 (nullable.some 0)
   *                                 (as nullable.null (Nullable Int))
   *                                 0)
   *                          (bag.filter
   *                            P
   *                            ((_ table.aggr 0 1)
   *                              fi
   *                              (tuple 0
   *                                     (as nullable.null (Nullable Int))
   *                                     (nullable.some 0)
   *                                     0)
   *                              X)))))
   *   ---> (bag.map h
   *                 (bag.filter
   *                   Q
   *                   (bag.map m
   *                            (bag.filter
   *                              J
   *                              (table.product
   *                                (bag.filter
   *                                  R
   *                                  ((_ table.aggr 0)
   *                                    fA
   *                                    (tuple 0 (nullable.some 0) 0)
   *                                    X))
   *                                (bag.filter
   *                                  R
   *                                  ((_ table.aggr 0)
   *                                    fB
   *                                    (tuple 0 (nullable.some 0) 0)
   *                                    (bag.setof
   *                                      (bag.map
   *                                        (lambda ((t (Tuple Int
   *                                                           (Nullable Int))))
   *                                          (tuple ((_ tuple.select 0) t)
   *                                                 ((_ tuple.select 1) t)))
   *                                        X)))))))))
   *
   * This is SQL's SELECT c0, COUNT(DISTINCT c1), COUNT(*) FROM X GROUP BY c0:
   * the inner aggregate groups X by both columns and counts their rows, the
   * outer one counts the groups of each c0 where c1 is not null, and sums their
   * counts. In the result, fA counts the rows of X by c0, fB counts the
   * distinct c1 by c0, J joins them on c0, and m puts their columns in the
   * order of the outer aggregate, with 1 for its count of rows.
   */
  AGGREGATE_ROLLUP,
  /**
   * An aggregate over a set is the aggregate over the bag when it computes only
   * copies of the row's columns, minimums, maximums, and a count of rows that
   * the map above does not read and the filter reads only through a test that
   * it is positive: duplicate rows change none of those. Also for an aggregate
   * among the factors of a product
   * (see BagsRewriter::rewriteAggregateJoinMerge).
   *
   * For Y : (Bag (Tuple Int (Nullable Int))) and
   *   f = (lambda ((t (Tuple Int (Nullable Int)))
   *                (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 1) acc))
   *                     ((_ tuple.select 1) t)
   *                     (ite (> (nullable.val ((_ tuple.select 1) acc))
   *                             (nullable.val ((_ tuple.select 1) t)))
   *                          ((_ tuple.select 1) t)
   *                          ((_ tuple.select 1) acc)))
   *                (+ 1 ((_ tuple.select 2) acc)))) and
   *   Q = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (>= ((_ tuple.select 2) r) 1)) and
   *   h = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r))),
   *
   *   (bag.map h
   *            (bag.filter Q
   *                        ((_ table.aggr 0)
   *                          f
   *                          (tuple 0 (as nullable.null (Nullable Int)) 0)
   *                          (bag.setof Y))))
   *   ---> (bag.map h
   *                 (bag.filter Q
   *                             ((_ table.aggr 0)
   *                               f
   *                               (tuple 0 (as nullable.null (Nullable Int)) 0)
   *                               Y)))
   *
   * Here SQL's MIN(c1) by c0.
   */
  AGGREGATE_SETOF_IDEMPOTENT,
  /**
   * Two aggregates over one table by the same group columns, both copying every
   * group column and starting the copies alike, joined on those copies, are one
   * aggregate that computes the columns of both: SQL's self-join of two GROUP
   * BY queries over one table.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   fa = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *          (tuple ((_ tuple.select 0) t)
   *                 (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                 (+ 1 ((_ tuple.select 2) acc)))) and
   *   fb = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *          (tuple ((_ tuple.select 0) t)
   *                 (+ 1 ((_ tuple.select 1) acc))
   *                 (ite (> ((_ tuple.select 1) t) ((_ tuple.select 2) acc))
   *                      ((_ tuple.select 1) t)
   *                      ((_ tuple.select 2) acc)))) and
   *   P = (lambda ((p (Tuple Int Int Int Int Int Int)))
   *         (and (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))
   *              (>= ((_ tuple.select 2) p) 1))) and
   *   h = (lambda ((p (Tuple Int Int Int Int Int Int)))
   *         (tuple ((_ tuple.select 0) p)
   *                ((_ tuple.select 1) p)
   *                ((_ tuple.select 2) p)
   *                ((_ tuple.select 3) p)
   *                ((_ tuple.select 5) p)
   *                ((_ tuple.select 4) p))),
   *
   *   (bag.map h
   *            (bag.filter P
   *                        (table.product
   *                          ((_ table.aggr 0) fa (tuple 0 0 0) X)
   *                          ((_ table.aggr 0) fb (tuple 0 0 0) X))))
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int Int Int Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   ((_ tuple.select 1) t)
   *                   ((_ tuple.select 2) t)
   *                   ((_ tuple.select 0) t)
   *                   ((_ tuple.select 3) t)
   *                   ((_ tuple.select 2) t)))
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int Int Int)))
   *              (>= ((_ tuple.select 2) t) 1))
   *            ((_ table.aggr 0)
   *              (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int Int)))
   *                (tuple ((_ tuple.select 0) t)
   *                       (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                       (+ 1 ((_ tuple.select 2) acc))
   *                       (ite (> ((_ tuple.select 1) t)
   *                               ((_ tuple.select 3) acc))
   *                            ((_ tuple.select 1) t)
   *                            ((_ tuple.select 3) acc))))
   *              (tuple 0 0 0 0)
   *              X)))
   *
   * Here the sum and the maximum of column 1 by column 0, each with a count of
   * rows; the one aggregate counts the rows once, for both.
   */
  AGGREGATE_JOIN_MERGE,
  /**
   * An aggregate over a union of parts with the same group values, under a
   * filter that keeps the groups some row reached, is the join of the
   * aggregates of the parts, their columns combined.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (nullable.some
   *                  (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                (+ 1 ((_ tuple.select 2) acc)))) and
   *   Q = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (>= ((_ tuple.select 2) r) 1)) and
   *   h = (lambda ((r (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r))) and
   *   A = ((_ table.aggr 0) f (tuple 0 (nullable.some 0) 0) X) and
   *   J = (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int)))
   *         (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))) and
   *   m = (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) p)
   *                (nullable.some
   *                  (+ (nullable.val ((_ tuple.select 1) p))
   *                     (nullable.val ((_ tuple.select 4) p))))
   *                ((_ tuple.select 2) p))),
   *
   *   (bag.map h
   *            (bag.filter Q
   *                        ((_ table.aggr 0)
   *                          f
   *                          (tuple 0 (nullable.some 0) 0)
   *                          (bag.union_disjoint X X))))
   *   ---> (bag.map h
   *                 (bag.filter Q
   *                             (bag.map
   *                               m
   *                               (bag.filter J (table.product A A)))))
   *
   * Here SQL's COUNT(*) by column 0 over X UNION ALL X: J joins the counts of
   * the two parts on column 0, and m adds them up. Also for parts that each
   * give the arguments of some columns and null for the others.
   */
  AGGREGATE_UNION_SPLIT,
  /**
   * The set of the group columns of the groups some row reached is the set of
   * those columns of the rows (see BagsRewriter::keysOfReachedGroups).
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))) and
   *   Q = (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1)),
   *
   *   (bag.setof
   *     (bag.map
   *       (lambda ((r (Tuple Int Int Int))) (tuple ((_ tuple.select 0) r)))
   *       (bag.filter Q ((_ table.aggr 0) f (tuple 0 0 0) X))))
   *   ---> (bag.setof
   *          (bag.map
   *            (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
   *            X))
   *
   * Q keeps the groups whose count of rows, column 2, is positive; the map
   * reads only the group column.
   */
  AGGREGATE_GROUP_KEYS,
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
   * A fold whose step returns the accumulator is its initial value.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.fold (lambda ((t (Tuple Int Int)) (acc Int)) acc) 7 X)
   *   ---> 7
   */
  FOLD_IDENTITY_STEP,
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
   * The set of the union of a bag with itself is the set of the bag.
   *
   * For A : (Bag (Tuple Int Int)),
   *
   *   (bag.setof (bag.union_disjoint A A))
   *   ---> (bag.setof A)
   */
  SETOF_UNION_SAME,
  /**
   * A fold that is SQL's SUM, MIN, MAX or COUNT over a union combines the folds
   * over the two parts.
   *
   * For A : (Bag (Tuple (Nullable Int))) and B : (Bag (Tuple (Nullable Int)))
   * and
   *   f = (lambda ((t (Tuple (Nullable Int))) (acc (Nullable Int)))
   *         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 0) t))
   *              acc
   *              (ite (= (as nullable.null (Nullable Int)) acc)
   *                   ((_ tuple.select 0) t)
   *                   (nullable.some
   *                     (+ (nullable.val acc)
   *                        (nullable.val ((_ tuple.select 0) t))))))) and
   *   a = (bag.fold f (as nullable.null (Nullable Int)) A) and
   *   b = (bag.fold f (as nullable.null (Nullable Int)) B),
   *
   *   (bag.fold f (as nullable.null (Nullable Int)) (bag.union_disjoint A B))
   *   ---> (ite (= (as nullable.null (Nullable Int)) a)
   *             b
   *             (ite (= (as nullable.null (Nullable Int)) b)
   *                  a
   *                  (nullable.some (+ (nullable.val a) (nullable.val b)))))
   *
   * Here SQL's SUM: a and b are the sums of the parts, null over a part without
   * a value.
   */
  FOLD_UNION_COMBINE,
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
   * An aggregate of a bag of one row, under a filter that keeps the groups some
   * row reached, is the step applied to the row and the initial value.
   *
   * For a : Int and b : Int and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                (+ ((_ tuple.select 2) acc) 1))) and
   *   Q = (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 2) r) 1)),
   *
   *   (bag.filter Q ((_ table.aggr 0) f (tuple 0 0 0) (bag (tuple a b) 1)))
   *   ---> (bag.filter Q (bag (tuple a b 1) 1))
   *
   * Here the step applied to (tuple a b) and (tuple 0 0 0) is (tuple a b 1).
   * Also for a bag of one row present when a condition holds,
   * (bag e (ite c 1 0)).
   */
  FILTER_AGGREGATE_ONE_ROW,
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
   * An aggregate over a join, aggregated eagerly: each factor is aggregated
   * first by the columns that the join and the groups read of it, and the
   * aggregate then reads one row per pair of groups that join, weighted by
   * their counts of rows (see BagsRewriter::eagerAggregation).
   *
   * For X : (Bag (Tuple Int (Nullable Int))) and Y : (Bag (Tuple Int)) and
   *   f = (lambda ((t (Tuple Int (Nullable Int) Int))
   *                (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 1) acc))
   *                     ((_ tuple.select 1) t)
   *                     (nullable.some
   *                       (+ (nullable.val ((_ tuple.select 1) acc))
   *                          (nullable.val ((_ tuple.select 1) t)))))
   *                (+ 1 ((_ tuple.select 2) acc)))) and
   *   P = (lambda ((t (Tuple Int (Nullable Int) Int)))
   *         (= ((_ tuple.select 0) t) ((_ tuple.select 2) t))) and
   *   AX = ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int (Nullable Int)))
   *                   (acc (Tuple Int (Nullable Int) (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (ite (= (as nullable.null (Nullable Int))
   *                           ((_ tuple.select 1) acc))
   *                        ((_ tuple.select 1) t)
   *                        (nullable.some
   *                          (+ (nullable.val ((_ tuple.select 1) acc))
   *                             (nullable.val ((_ tuple.select 1) t)))))
   *                   (nullable.some
   *                     (+ 1 (nullable.val ((_ tuple.select 2) acc))))
   *                   (+ 1 ((_ tuple.select 3) acc))))
   *          (tuple 0 (as nullable.null (Nullable Int)) (nullable.some 0) 0)
   *          X) and
   *   AY = ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int)) (acc (Tuple Int (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (nullable.some
   *                     (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                   (+ 1 ((_ tuple.select 2) acc))))
   *          (tuple 0 (nullable.some 0) 0)
   *          Y) and
   *   J = (lambda ((p (Tuple Int (Nullable Int) (Nullable Int) Int Int
   *                          (Nullable Int) Int)))
   *         (and (= ((_ tuple.select 0) p) ((_ tuple.select 4) p))
   *              (>= ((_ tuple.select 3) p) 1)
   *              (>= ((_ tuple.select 6) p) 1))) and
   *   g = (lambda ((p (Tuple Int (Nullable Int) (Nullable Int) Int Int
   *                          (Nullable Int) Int))
   *                (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) p)
   *                (ite (= (as nullable.null (Nullable Int))
   *                        ((_ tuple.select 1) acc))
   *                     (ite (= (as nullable.null (Nullable Int))
   *                             ((_ tuple.select 1) p))
   *                          (as nullable.null (Nullable Int))
   *                          (nullable.some
   *                            (* (nullable.val ((_ tuple.select 1) p))
   *                               (nullable.val ((_ tuple.select 5) p)))))
   *                     (nullable.some
   *                       (+ (nullable.val ((_ tuple.select 1) acc))
   *                          (nullable.val
   *                            (ite (= (as nullable.null (Nullable Int))
   *                                    ((_ tuple.select 1) p))
   *                                 (as nullable.null (Nullable Int))
   *                                 (nullable.some
   *                                   (* (nullable.val ((_ tuple.select 1) p))
   *                                      (nullable.val
   *                                        ((_ tuple.select 5) p)))))))))
   *                (+ ((_ tuple.select 2) acc)
   *                   (* ((_ tuple.select 3) p) ((_ tuple.select 6) p))))),
   *
   *   ((_ table.aggr 0) f
   *                     (tuple 0 (as nullable.null (Nullable Int)) 0)
   *                     (bag.filter P (table.product X Y)))
   *   ---> ((_ table.aggr 0) g
   *                          (tuple 0 (as nullable.null (Nullable Int)) 0)
   *                          (bag.filter J (table.product AX AY)))
   *
   * Here SQL's SUM(c1) by c0 over the join of X and Y on c0. AX sums c1 by c0
   * over X and counts its rows, with COUNT(*) and a count of rows, AY counts
   * the rows of Y by c0, J keeps the pairs of groups that join, and g adds up
   * the sums of X times the counts of Y, and the counts of rows of X times
   * those of Y.
   */
  AGGREGATE_OVER_JOIN,
  /**
   * A fold over a join, aggregated eagerly: each factor is aggregated first by
   * its join columns, and the fold then reads one row per pair of groups that
   * join, weighted by their counts of rows
   * (see BagsRewriter::eagerAggregation).
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int)) and
   *   P = (lambda ((t (Tuple Int Int Int)))
   *         (= ((_ tuple.select 0) t) ((_ tuple.select 2) t))) and
   *   AX = ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (nullable.some
   *                     (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                   (+ 1 ((_ tuple.select 2) acc))))
   *          (tuple 0 (nullable.some 0) 0)
   *          X) and
   *   AY = ((_ table.aggr 0)
   *          (lambda ((t (Tuple Int)) (acc (Tuple Int (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   (nullable.some
   *                     (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                   (+ 1 ((_ tuple.select 2) acc))))
   *          (tuple 0 (nullable.some 0) 0)
   *          Y) and
   *   J = (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int)))
   *         (and (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))
   *              (>= ((_ tuple.select 2) p) 1)
   *              (>= ((_ tuple.select 5) p) 1))),
   *
   *   (bag.fold
   *     (lambda ((t (Tuple Int Int Int)) (acc (Nullable Int)))
   *       (nullable.some (+ 1 (nullable.val acc))))
   *     (nullable.some 0)
   *     (bag.filter P (table.product X Y)))
   *   ---> (bag.fold
   *          (lambda ((p (Tuple Int (Nullable Int) Int Int (Nullable Int) Int))
   *                   (acc (Nullable Int)))
   *            (nullable.some
   *              (+ (nullable.val acc)
   *                 (* (nullable.val ((_ tuple.select 1) p))
   *                    (nullable.val ((_ tuple.select 4) p))))))
   *          (nullable.some 0)
   *          (bag.filter J (table.product AX AY)))
   *
   * Here SQL's COUNT(*) over the join of X and Y on c0. AX and AY count the
   * rows of X and of Y by c0, J keeps the pairs of groups that join, and the
   * fold adds up the products of their counts.
   */
  FOLD_OVER_JOIN,
  /**
   * A column of an aggregate among the factors of a product that the map above
   * it does not read is not computed; also with a filter between the map and
   * the product that does not read it.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int)) and
   *   h = (lambda ((p (Tuple Int Int Int Int)))
   *         (tuple ((_ tuple.select 1) p)
   *                ((_ tuple.select 3) p)
   *                ((_ tuple.select 0) p))),
   *
   *   (bag.map h
   *            (table.product Y
   *                           ((_ table.aggr 0)
   *                             (lambda ((t (Tuple Int Int))
   *                                      (acc (Tuple Int Int Int)))
   *                               (tuple ((_ tuple.select 0) t)
   *                                      (+ ((_ tuple.select 1) acc)
   *                                         ((_ tuple.select 1) t))
   *                                      (+ 1 ((_ tuple.select 2) acc))))
   *                             (tuple 0 0 0)
   *                             X)))
   *   ---> (bag.map
   *          (lambda ((p (Tuple Int Int Int)))
   *            (tuple ((_ tuple.select 1) p)
   *                   ((_ tuple.select 2) p)
   *                   ((_ tuple.select 0) p)))
   *          (table.product Y
   *                         ((_ table.aggr 0)
   *                           (lambda ((t (Tuple Int Int))
   *                                    (acc (Tuple Int Int)))
   *                             (tuple ((_ tuple.select 0) t)
   *                                    (+ 1 ((_ tuple.select 1) acc))))
   *                           (tuple 0 0)
   *                           X)))
   *
   * Here the map does not read the sum, column 2 of the product.
   */
  PRODUCT_AGGREGATE_DEAD_COLUMN,
  /**
   * Two columns of an aggregate that fold alike, with the same step and initial
   * value, are one column read twice.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (nullable.some
   *                  (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                (+ 1 ((_ tuple.select 2) acc)))),
   *
   *   ((_ table.aggr 0)
   *     (lambda ((t (Tuple Int Int))
   *              (acc (Tuple Int (Nullable Int) Int (Nullable Int))))
   *       (tuple ((_ tuple.select 0) t)
   *              (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *              (+ 1 ((_ tuple.select 2) acc))
   *              (nullable.some
   *                (+ 1 (nullable.val ((_ tuple.select 3) acc))))))
   *     (tuple 0 (nullable.some 0) 0 (nullable.some 0))
   *     X)
   *   ---> (bag.map
   *          (lambda ((t (Tuple Int (Nullable Int) Int)))
   *            (tuple ((_ tuple.select 0) t)
   *                   ((_ tuple.select 1) t)
   *                   ((_ tuple.select 2) t)
   *                   ((_ tuple.select 1) t)))
   *          ((_ table.aggr 0) f (tuple 0 (nullable.some 0) 0) X))
   *
   * Here SQL's COUNT(*) twice.
   */
  AGGREGATE_DUPLICATE_COLUMN,
  /**
   * A sum from 0 is the sum from null, which skips nulls, or 0 where that is
   * null.
   *
   * For X : (Bag (Tuple Int)) and
   *   S = (bag.fold
   *         (lambda ((t (Tuple Int)) (acc (Nullable Int)))
   *           (ite (= (as nullable.null (Nullable Int)) acc)
   *                (nullable.some ((_ tuple.select 0) t))
   *                (nullable.some
   *                  (+ (nullable.val acc) ((_ tuple.select 0) t)))))
   *         (as nullable.null (Nullable Int))
   *         X),
   *
   *   (bag.fold
   *     (lambda ((t (Tuple Int)) (acc (Nullable Int)))
   *       (nullable.some (+ (nullable.val acc) ((_ tuple.select 0) t))))
   *     (nullable.some 0)
   *     X)
   *   ---> (ite (= (as nullable.null (Nullable Int)) S) (nullable.some 0) S)
   *
   * S is SQL's SUM, null over a table without rows.
   */
  FOLD_SUM_FROM_ZERO,
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
   * SQL's COUNT(*) of an aggregate that also counts its rows, in a filter over
   * it, is read off the count of rows.
   *
   * For X : (Bag (Tuple Int Int)) and
   *   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
   *         (tuple ((_ tuple.select 0) t)
   *                (nullable.some
   *                  (+ 1 (nullable.val ((_ tuple.select 1) acc))))
   *                (+ 1 ((_ tuple.select 2) acc)))),
   *
   *   (bag.filter
   *     (lambda ((r (Tuple Int (Nullable Int) Int)))
   *       (= ((_ tuple.select 1) r) (nullable.some 3)))
   *     ((_ table.aggr 0) f (tuple 0 (nullable.some 0) 0) X))
   *   ---> (bag.filter
   *          (lambda ((r (Tuple Int (Nullable Int) Int)))
   *            (= (nullable.some ((_ tuple.select 2) r)) (nullable.some 3)))
   *          ((_ table.aggr 0) f (tuple 0 (nullable.some 0) 0) X))
   */
  FILTER_COUNT_AS_COUNTER,
  /**
   * A union of two filters of one bag that differ in a conjunct and its
   * negation is the filter by the other conjuncts.
   *
   * For X : (Bag (Tuple Int Int)),
   *
   *   (bag.union_disjoint
   *     (bag.filter
   *       (lambda ((t (Tuple Int Int)))
   *         (and (> ((_ tuple.select 0) t) 3) (< ((_ tuple.select 1) t) 7)))
   *       X)
   *     (bag.filter
   *       (lambda ((t (Tuple Int Int)))
   *         (and (not (> ((_ tuple.select 0) t) 3))
   *              (< ((_ tuple.select 1) t) 7)))
   *       X))
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int))) (< ((_ tuple.select 1) t) 7))
   *          X)
   *
   * Also under one map of both, and for two parts of a longer union.
   */
  UNION_COMPLEMENTARY_FILTERS,
  /**
   * A conjunct that a bag is not empty goes from a filter when another conjunct
   * finds a row in it.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)) and
   *   g = (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 0) s))),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int)))
   *       (and (>= (bag.count (tuple ((_ tuple.select 1) t)) (bag.map g Y)) 1)
   *            (not (= Y (as bag.empty (Bag (Tuple Int Int)))))))
   *     X)
   *   ---> (bag.filter
   *          (lambda ((t (Tuple Int Int)))
   *            (>= (bag.count (tuple ((_ tuple.select 1) t)) (bag.map g Y)) 1))
   *          X)
   *
   * The filter is empty instead when a conjunct says that the bag is empty.
   */
  FILTER_KNOWN_NONEMPTY,
  /**
   * A test that the count of rows of a factor is positive goes when the filter
   * joins that factor, on all its group columns, with a factor whose groups
   * some row reached and whose table is the same: every group of the one meets
   * a group of the other (see BagsRewriter::reachedComponents).
   *
   * For X : (Bag (Tuple Int Int)) and
   *   A = ((_ table.aggr 0)
   *         (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *           (tuple ((_ tuple.select 0) t)
   *                  (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
   *                  (+ 1 ((_ tuple.select 2) acc))))
   *         (tuple 0 0 0)
   *         X) and
   *   B = ((_ table.aggr 0)
   *         (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
   *           (tuple ((_ tuple.select 0) t)
   *                  (+ 1 ((_ tuple.select 1) acc))
   *                  (ite (> ((_ tuple.select 1) t) ((_ tuple.select 2) acc))
   *                       ((_ tuple.select 1) t)
   *                       ((_ tuple.select 2) acc))))
   *         (tuple 0 0 0)
   *         X),
   *
   *   (bag.filter
   *     (lambda ((p (Tuple Int Int Int Int Int Int)))
   *       (and (>= ((_ tuple.select 2) p) 1)
   *            (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))
   *            (>= ((_ tuple.select 4) p) 1)))
   *     (table.product A B))
   *   ---> (bag.filter
   *          (lambda ((p (Tuple Int Int Int Int Int Int)))
   *            (and (>= ((_ tuple.select 2) p) 1)
   *                 (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))))
   *          (table.product A B))
   *
   * Here column 2 counts the rows of A and column 4 those of B: the groups of A
   * that a row reached are those of B.
   */
  FILTER_IMPLIED_COUNTER,
  /**
   * A row with a null in a column that the table never has null in does not
   * occur in it.
   *
   * For Y : (Bag (Tuple Int (Nullable Int))) and a : Int,
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
   *   (bag.count (tuple a (as nullable.null (Nullable Int))) Y)
   *   ---> 0
   */
  COUNT_NULL_IN_NOT_NULL,
  /**
   * A join of two sets of one row sort on all their columns is their
   * intersection, each row twice over.
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.filter
   *     (lambda ((t (Tuple Int Int Int Int)))
   *       (and (= ((_ tuple.select 0) t) ((_ tuple.select 2) t))
   *            (= ((_ tuple.select 1) t) ((_ tuple.select 3) t))))
   *     (table.product (bag.setof X) (bag.setof Y)))
   *   ---> (bag.map
   *          (lambda ((w (Tuple Int Int)))
   *            (tuple ((_ tuple.select 0) w)
   *                   ((_ tuple.select 1) w)
   *                   ((_ tuple.select 0) w)
   *                   ((_ tuple.select 1) w)))
   *          (bag.inter_min (bag.setof X) (bag.setof Y)))
   */
  FILTER_EQUI_JOIN_SETS,
  /**
   * The filters of the two sides of an intersection each get the conditions of
   * the other: a row in both satisfies both
   * (see BagsRewriter::elementConditions).
   *
   * For X : (Bag (Tuple Int Int)) and Y : (Bag (Tuple Int Int)),
   *
   *   (bag.inter_min
   *     (bag.filter (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
   *                 X)
   *     (bag.filter (lambda ((t (Tuple Int Int))) (< ((_ tuple.select 1) t) 7))
   *                 Y))
   *   ---> (bag.inter_min
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int)))
   *              (and (> ((_ tuple.select 0) t) 3)
   *                   (< ((_ tuple.select 1) t) 7)))
   *            X)
   *          (bag.filter
   *            (lambda ((t (Tuple Int Int)))
   *              (and (> ((_ tuple.select 0) t) 3)
   *                   (< ((_ tuple.select 1) t) 7)))
   *            Y))
   */
  INTERSECTION_SHARE_CONDITIONS,
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

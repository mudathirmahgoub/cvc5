; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; FOLD_OVER_JOIN over a join on Int columns, not Nullable ones: SQL's
; COUNT(*) over the join of X and Y on c0 is the sum, over the pairs of
; groups of X and of Y by c0 that join, of the products of their counts of
; rows. eagerAggregation seeds the group columns of the aggregates of the two
; sides with values of their sorts.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(declare-const Y (Bag (Tuple Int)))
(define-fun count ((t (Tuple Int Int Int)) (acc (Nullable Int))) (Nullable Int)
  (nullable.some (+ 1 (nullable.val acc))))
(define-fun query () (Nullable Int)
  (bag.fold count
            (nullable.some 0)
            (bag.filter (lambda ((t (Tuple Int Int Int)))
                          (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
                        (table.product X Y))))
; COUNT(*) and a count of rows by c0, of X and of Y
(define-fun fx ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int) Int)))
               (Tuple Int (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc))))
         (+ 1 ((_ tuple.select 2) acc))))
(define-fun fy ((t (Tuple Int)) (acc (Tuple Int (Nullable Int) Int)))
               (Tuple Int (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc))))
         (+ 1 ((_ tuple.select 2) acc))))
(define-sort Pair () (Tuple Int (Nullable Int) Int Int (Nullable Int) Int))
(define-fun pairs () (Bag Pair)
  (bag.filter
    (lambda ((p Pair))
      (and (= ((_ tuple.select 0) p) ((_ tuple.select 3) p))
           (>= ((_ tuple.select 2) p) 1)
           (>= ((_ tuple.select 5) p) 1)))
    (table.product ((_ table.aggr 0) fx (tuple 0 (nullable.some 0) 0) X)
                   ((_ table.aggr 0) fy (tuple 0 (nullable.some 0) 0) Y))))
(define-fun result () (Nullable Int)
  (bag.fold (lambda ((p Pair) (acc (Nullable Int)))
              (nullable.some (+ (nullable.val acc)
                                (* (nullable.val ((_ tuple.select 1) p))
                                   (nullable.val ((_ tuple.select 4) p))))))
            (nullable.some 0)
            pairs))
(assert (not (= query result)))
(check-sat)

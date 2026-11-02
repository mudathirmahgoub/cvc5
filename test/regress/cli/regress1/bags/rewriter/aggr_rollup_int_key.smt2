; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; AGGREGATE_ROLLUP over a table whose group column c0 is an Int, not a
; Nullable Int: SELECT c0, COUNT(DISTINCT c1), COUNT(*) FROM X GROUP BY c0,
; as an aggregate by c0 of an aggregate by (c0, c1), is the join of the
; COUNT(*) by c0 and the COUNT(c1) by c0 over the distinct (c0, c1). The rule
; seeds the group columns of the two new aggregates with the seeds of the
; inner aggregate, which have their sorts.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int (Nullable Int))))
; the inner aggregate, by (c0, c1): COUNT(*) and a count of rows
(define-fun fi ((t (Tuple Int (Nullable Int)))
                (acc (Tuple Int (Nullable Int) (Nullable Int) Int)))
                (Tuple Int (Nullable Int) (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t)
         ((_ tuple.select 1) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 2) acc))))
         (+ 1 ((_ tuple.select 3) acc))))
; the outer aggregate, by c0: COUNT(c1), the SUM of the counts, a count of rows
(define-fun g ((t (Tuple Int (Nullable Int) (Nullable Int) Int))
               (acc (Tuple Int (Nullable Int) (Nullable Int) Int)))
               (Tuple Int (Nullable Int) (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t)
         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) t))
              ((_ tuple.select 1) acc)
              (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc)))))
         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 2) acc))
              ((_ tuple.select 2) t)
              (nullable.some (+ (nullable.val ((_ tuple.select 2) acc))
                                (nullable.val ((_ tuple.select 2) t)))))
         (+ 1 ((_ tuple.select 3) acc))))
(define-fun inner () (Bag (Tuple Int (Nullable Int) (Nullable Int) Int))
  (bag.filter (lambda ((r (Tuple Int (Nullable Int) (Nullable Int) Int)))
                (>= ((_ tuple.select 3) r) 1))
              ((_ table.aggr 0 1) fi
                                  (tuple 0 (as nullable.null (Nullable Int))
                                         (nullable.some 0) 0)
                                  X)))
(define-sort Out () (Tuple Int (Nullable Int) (Nullable Int) Int))
(define-fun h ((q Out)) (Tuple Int (Nullable Int) (Nullable Int))
  (tuple ((_ tuple.select 0) q) ((_ tuple.select 1) q) ((_ tuple.select 2) q)))
(define-fun Q ((q Out)) Bool (>= ((_ tuple.select 3) q) 1))
(define-fun query () (Bag (Tuple Int (Nullable Int) (Nullable Int)))
  (bag.map h
           (bag.filter Q
                       ((_ table.aggr 0)
                         g
                         (tuple 0 (nullable.some 0)
                                (as nullable.null (Nullable Int)) 0)
                         inner))))
; COUNT(*) by c0 over X, and COUNT(c1) by c0 over the distinct (c0, c1)
(define-fun fA ((t (Tuple Int (Nullable Int)))
                (acc (Tuple Int (Nullable Int) Int)))
                (Tuple Int (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc))))
         (+ 1 ((_ tuple.select 2) acc))))
(define-fun fB ((s (Tuple Int (Nullable Int)))
                (acc (Tuple Int (Nullable Int) Int)))
                (Tuple Int (Nullable Int) Int)
  (tuple ((_ tuple.select 0) s)
         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) s))
              ((_ tuple.select 1) acc)
              (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc)))))
         (+ 1 ((_ tuple.select 2) acc))))
(define-fun reached ((r (Tuple Int (Nullable Int) Int))) Bool
  (>= ((_ tuple.select 2) r) 1))
(define-sort Row () (Tuple Int (Nullable Int) Int Int (Nullable Int) Int))
(define-fun joined () (Bag Row)
  (bag.filter
    (lambda ((p Row)) (= ((_ tuple.select 0) p) ((_ tuple.select 3) p)))
    (table.product
      (bag.filter reached
                  ((_ table.aggr 0) fA (tuple 0 (nullable.some 0) 0) X))
      (bag.filter reached
                  ((_ table.aggr 0) fB (tuple 0 (nullable.some 0) 0)
                                    (bag.setof X))))))
; the rows of the join in the order of the outer aggregate, with 1 for its
; count of rows, under its filter and map
(define-fun m ((p Row)) Out
  (tuple ((_ tuple.select 0) p)
         ((_ tuple.select 4) p)
         ((_ tuple.select 1) p)
         1))
(define-fun result () (Bag (Tuple Int (Nullable Int) (Nullable Int)))
  (bag.map h (bag.filter Q (bag.map m joined))))
(assert (not (= query result)))
(check-sat)

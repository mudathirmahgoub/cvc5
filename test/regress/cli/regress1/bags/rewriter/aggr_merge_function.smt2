; REQUIRES: unrestricted-mode
; AGGREGATE_COLLAPSE and AGGREGATE_ROLLUP merge an aggregate of aggregates
; into one aggregate only when the outer step merges an inner column itself.
; A sum of the squares of counts is not the square of the count: over groups
; of 1 and 2 rows it is 5, not 9 (collapse) or 3 (rollup).
; The terms are ground: a wrong value makes the problem unsat.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X1 (Bag (Tuple Int Int)))
(declare-const X2 (Bag (Tuple Int Int)))
(declare-const X (Bag (Tuple Int (Nullable Int))))
(assert (= X1 (bag (tuple 1 7) 1)))
(assert (= X2 (bag (tuple 1 8) 2)))
(assert (= X (bag.union_disjoint (bag (tuple 1 (nullable.some 4)) 2)
                                 (bag (tuple 1 (nullable.some 6)) 1))))
; COUNT(*) by column 0
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int (Nullable Int))))
              (Tuple Int (Nullable Int))
  (tuple ((_ tuple.select 0) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 1) acc))))))
; the sum of the squares of column 1, by column 0
(define-fun g ((t (Tuple Int (Nullable Int))) (acc (Tuple Int (Nullable Int))))
              (Tuple Int (Nullable Int))
  (tuple ((_ tuple.select 0) t)
         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) acc))
              (nullable.some (* (nullable.val ((_ tuple.select 1) t))
                                (nullable.val ((_ tuple.select 1) t))))
              (nullable.some
                (+ (nullable.val ((_ tuple.select 1) acc))
                   (* (nullable.val ((_ tuple.select 1) t))
                      (nullable.val ((_ tuple.select 1) t))))))))
(define-fun collapse () (Bag (Tuple Int (Nullable Int)))
  ((_ table.aggr 0)
    g
    (tuple 0 (as nullable.null (Nullable Int)))
    (bag.union_disjoint
      ((_ table.aggr 0) f (tuple 0 (nullable.some 0)) X1)
      ((_ table.aggr 0) f (tuple 0 (nullable.some 0)) X2))))
; COUNT(*) by columns 0 and 1
(define-fun fi ((t (Tuple Int (Nullable Int)))
                (acc (Tuple Int (Nullable Int) (Nullable Int))))
               (Tuple Int (Nullable Int) (Nullable Int))
  (tuple ((_ tuple.select 0) t)
         ((_ tuple.select 1) t)
         (nullable.some (+ 1 (nullable.val ((_ tuple.select 2) acc))))))
; the sum of the squares of column 2, by column 0
(define-fun go ((t (Tuple Int (Nullable Int) (Nullable Int)))
                (acc (Tuple Int (Nullable Int))))
               (Tuple Int (Nullable Int))
  (tuple ((_ tuple.select 0) t)
         (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) acc))
              (nullable.some (* (nullable.val ((_ tuple.select 2) t))
                                (nullable.val ((_ tuple.select 2) t))))
              (nullable.some
                (+ (nullable.val ((_ tuple.select 1) acc))
                   (* (nullable.val ((_ tuple.select 2) t))
                      (nullable.val ((_ tuple.select 2) t))))))))
(define-fun rollup () (Bag (Tuple Int (Nullable Int)))
  ((_ table.aggr 0)
    go
    (tuple 0 (as nullable.null (Nullable Int)))
    ((_ table.aggr 0 1)
      fi
      (tuple 0 (as nullable.null (Nullable Int)) (nullable.some 0))
      X)))
(assert (= (bag.count (tuple 1 (nullable.some 5)) collapse) 1))
(assert (= (bag.count (tuple 1 (nullable.some 5)) rollup) 1))
(check-sat)

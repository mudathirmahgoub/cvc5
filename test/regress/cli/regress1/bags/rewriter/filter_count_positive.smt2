; REQUIRES: unrestricted-mode
; FILTER_COUNT_POSITIVE: every group of an aggregate has a row, so a filter
; that keeps the groups whose count of rows is at least 1 keeps them all.
; SELECT c0, SUM(c1) FROM X GROUP BY c0 with such a count and filter, as
; translators wrote it when the aggregate of an empty table had a row, is the
; aggregate without them.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
; column 0 of X, the sum of column 1, and a count of rows
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
; column 0 of X and the sum of column 1
(define-fun g ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= (bag.map
                  (lambda ((r (Tuple Int Int Int)))
                    (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
                  (bag.filter
                    (lambda ((r (Tuple Int Int Int)))
                      (>= ((_ tuple.select 2) r) 1))
                    ((_ table.aggr 0) f (tuple 0 0 0) X)))
                ((_ table.aggr 0) g (tuple 0 0) X))))
(check-sat)

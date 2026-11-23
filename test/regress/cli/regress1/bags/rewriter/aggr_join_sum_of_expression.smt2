; AGGREGATE_OVER_JOIN over a sum of an expression of one side's column,
;   SELECT x.k, SUM(y.b * 2) FROM x JOIN y ON x.a = y.a GROUP BY x.k
; The outer step takes the inner sum in place of the summed expression: in
; place of the column, it doubled the sum again, and x = {(1, 5)},
; y = {(5, 3)} gave 12 for 6
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const x (Bag (Tuple (Nullable Int) (Nullable Int))))
(declare-const y (Bag (Tuple (Nullable Int) (Nullable Int))))
(define-fun f ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))
               (acc (Tuple (Nullable Int) (Nullable Int) Int)))
  (Tuple (Nullable Int) (Nullable Int) Int)
  (let ((v (ite (nullable.is_null ((_ tuple.select 3) t))
                (as nullable.null (Nullable Int))
                (nullable.some (* 2 (nullable.val ((_ tuple.select 3) t))))))
        (s ((_ tuple.select 1) acc)))
    (tuple ((_ tuple.select 0) t)
           (ite (nullable.is_null v) s
                (ite (nullable.is_null s) v (nullable.some (+ (nullable.val v) (nullable.val s)))))
           (+ ((_ tuple.select 2) acc) 1))))
(define-fun q () (Bag (Tuple (Nullable Int) (Nullable Int) Int))
  ((_ table.aggr 0) f (tuple (as nullable.null (Nullable Int)) (as nullable.null (Nullable Int)) 0)
    (bag.filter (lambda ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
                  (and (nullable.is_some ((_ tuple.select 1) t))
                       (= ((_ tuple.select 1) t) ((_ tuple.select 2) t))))
                (table.product x y))))
(assert (= x (bag (tuple (nullable.some 1) (nullable.some 5)) 1)))
(assert (= y (bag (tuple (nullable.some 5) (nullable.some 3)) 1)))
(assert (not (bag.member (tuple (nullable.some 1) (nullable.some 6) 1) q)))
(check-sat)

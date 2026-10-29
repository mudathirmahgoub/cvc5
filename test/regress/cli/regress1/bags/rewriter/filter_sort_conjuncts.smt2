; FILTER_SORT_CONJUNCTS: the conjuncts of a filter are in one order, so the
; aggregates over two filters that list them in different orders are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (bag.filter (lambda ((t (Tuple Int Int))) (and (> ((_ tuple.select 0) t) 3) (< ((_ tuple.select 1) t) 7))) X))
                ((_ table.aggr 0) f (tuple 0 0) (bag.filter (lambda ((t (Tuple Int Int))) (and (< ((_ tuple.select 1) t) 7) (> ((_ tuple.select 0) t) 3))) X)))))
(check-sat)

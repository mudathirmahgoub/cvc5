; REQUIRES: unrestricted-mode
; AGGREGATE_COLLAPSE applies the outer step once, to the inner row of the
; union of the inputs, so it collapses only an outer step that reads the
; inner column as it is: for
;   SELECT k, MAX(0 - m) FROM (SELECT k, MAX(a) AS m FROM X1 GROUP BY k
;   UNION ALL SELECT k, MAX(a) AS m FROM X2 GROUP BY k) GROUP BY k
; it gave -max(m1, m2) for -min(m1, m2): -5 for -3 on X1 = {(1, 3)},
; X2 = {(1, 5)}
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X1 (Bag (Tuple (Nullable Int) (Nullable Int))))
(declare-const X2 (Bag (Tuple (Nullable Int) (Nullable Int))))
(define-fun mx ((a (Nullable Int)) (s (Nullable Int))) (Nullable Int)
  (ite (nullable.is_null a) s
       (ite (nullable.is_null s) a (ite (> (nullable.val a) (nullable.val s)) a s))))
(define-fun f ((t (Tuple (Nullable Int) (Nullable Int))) (acc (Tuple (Nullable Int) (Nullable Int) Int)))
  (Tuple (Nullable Int) (Nullable Int) Int)
  (tuple ((_ tuple.select 0) t) (mx ((_ tuple.select 1) t) ((_ tuple.select 1) acc)) (+ ((_ tuple.select 2) acc) 1)))
(define-fun part ((X (Bag (Tuple (Nullable Int) (Nullable Int))))) (Bag (Tuple (Nullable Int) (Nullable Int)))
  (bag.map (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int))) (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
    (bag.filter (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int))) (>= ((_ tuple.select 2) r) 1))
      ((_ table.aggr 0) f (tuple (as nullable.null (Nullable Int)) (as nullable.null (Nullable Int)) 0) X))))
(define-fun g ((u (Tuple (Nullable Int) (Nullable Int))) (acc (Tuple (Nullable Int) (Nullable Int) Int)))
  (Tuple (Nullable Int) (Nullable Int) Int)
  (tuple ((_ tuple.select 0) u)
         (mx (ite (nullable.is_null ((_ tuple.select 1) u)) (as nullable.null (Nullable Int))
                  (nullable.some (- 0 (nullable.val ((_ tuple.select 1) u)))))
             ((_ tuple.select 1) acc))
         (+ ((_ tuple.select 2) acc) 1)))
(define-fun q () (Bag (Tuple (Nullable Int) (Nullable Int)))
  (bag.map (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int))) (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
    (bag.filter (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int))) (>= ((_ tuple.select 2) r) 1))
      ((_ table.aggr 0) g (tuple (as nullable.null (Nullable Int)) (as nullable.null (Nullable Int)) 0)
        (bag.union_disjoint (part X1) (part X2))))))
(assert (= X1 (bag (tuple (nullable.some 1) (nullable.some 3)) 1)))
(assert (= X2 (bag (tuple (nullable.some 1) (nullable.some 5)) 1)))
(assert (not (bag.member (tuple (nullable.some 1) (nullable.some (- 3))) q)))
(check-sat)

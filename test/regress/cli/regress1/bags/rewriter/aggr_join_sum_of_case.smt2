; REQUIRES: unrestricted-mode
; CPC checking fails because the signature types (table.product x y) with the
; columns of y first (proofs/eo/cpc/expert/theories/Bags.eo), which only
; tables with different columns show.
; DISABLE-TESTER: cpc
; AGGREGATE_OVER_JOIN over a sum of a CASE on a string column of one side,
;   SELECT x.k, SUM(CASE WHEN y.s = 'S8' THEN 1 ELSE 0 END)
;   FROM x JOIN y ON x.a = y.a GROUP BY x.k
; The outer step takes the inner sum in place of the CASE: in place of the
; column, it put an integer where the string was, an ill-sorted term. Here
; that gave a wrong sat; on larger problems the arithmetic rewriter read the
; term's constants as rationals and crashed
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const x (Bag (Tuple (Nullable Int) (Nullable Int))))
(declare-const y (Bag (Tuple (Nullable Int) (Nullable String))))
(define-fun f ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int) (Nullable String)))
               (acc (Tuple (Nullable Int) (Nullable Int) Int)))
  (Tuple (Nullable Int) (Nullable Int) Int)
  (let ((v (nullable.some (ite (= ((_ tuple.select 3) t) (nullable.some "S8")) 1 0)))
        (s ((_ tuple.select 1) acc)))
    (tuple ((_ tuple.select 0) t)
           (ite (nullable.is_null v) s
                (ite (nullable.is_null s) v (nullable.some (+ (nullable.val v) (nullable.val s)))))
           (+ ((_ tuple.select 2) acc) 1))))
(define-fun q () (Bag (Tuple (Nullable Int) (Nullable Int) Int))
  ((_ table.aggr 0) f (tuple (as nullable.null (Nullable Int)) (as nullable.null (Nullable Int)) 0)
    (bag.filter (lambda ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int) (Nullable String))))
                  (and (nullable.is_some ((_ tuple.select 1) t))
                       (= ((_ tuple.select 1) t) ((_ tuple.select 2) t))))
                (table.product x y))))
(assert (= x (bag (tuple (nullable.some 1) (nullable.some 5)) 1)))
(assert (= y (bag.union_disjoint (bag (tuple (nullable.some 5) (nullable.some "S8")) 1)
                                 (bag (tuple (nullable.some 5) (nullable.some "A")) 1))))
(assert (not (bag.member (tuple (nullable.some 1) (nullable.some 1) 2) q)))
(check-sat)

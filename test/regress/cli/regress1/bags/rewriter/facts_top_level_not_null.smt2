; COMMAND-LINE: --learned-rewrite
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; A NOT NULL column asserted at the top level has no null
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple (Nullable Int))))
; column 0 of X is NOT NULL, asserted
(assert (= (bag.filter (lambda ((t (Tuple (Nullable Int)))) (= ((_ tuple.select 0) t) (as nullable.null (Nullable Int)))) X)
           (as bag.empty (Bag (Tuple (Nullable Int))))))
(assert (>= (bag.count (tuple (as nullable.null (Nullable Int))) X) 1))
(check-sat)

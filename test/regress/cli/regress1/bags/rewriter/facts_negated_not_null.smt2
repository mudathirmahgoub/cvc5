; A not-null equality under a negation is no fact, as in facts_negated_key.smt2
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple (Nullable Int))))
; column 0 of X has a null: the rewriter must not record it as NOT NULL
(assert (not (= (bag.filter (lambda ((t (Tuple (Nullable Int)))) (= (as nullable.null (Nullable Int)) ((_ tuple.select 0) t))) X)
                (as bag.empty (Bag (Tuple (Nullable Int)))))))
(assert (>= (bag.count (tuple (as nullable.null (Nullable Int))) X) 1))
(check-sat)

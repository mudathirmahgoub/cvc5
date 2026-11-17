; REQUIRES: unrestricted-mode
; The bag solver reduces the disequality of the map with (bag 0 p), which is
; empty for p = 0, to a lemma whose premise is that the map is not empty. Were
; that premise rewritten to (not (= s bag.empty)), the solver could assume s
; empty and the map not empty, and answer sat
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const s (Bag Int))
(declare-const p Int)
(assert (not (= (bag.map (lambda ((x Int)) (+ x 1)) s) (bag 0 p))))
(assert (>= p 0))
(assert (< p 1))
(assert (or (= s (as bag.empty (Bag Int))) (= p 7)))
(check-sat)

; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; COMMAND-LINE: --rels-acyclic-hammer --rels-tc-down-lazy
; EXPECT: unsat
; Closure grounding conflict of --rels-acyclic-hammer: the premise is the cut
; a /= d, b /= d (no member leaves {a, b}) and b /= c (c is not reached), not
; distinct(a, b, c, d).
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Relation U U))
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= R (set.union (set.singleton (tuple a b)) (set.singleton (tuple d c)))))
(assert (set.member (tuple a c) (rel.tclosure R)))
(assert (not (= a d)))
(assert (not (= b d)))
(assert (not (= b c)))
(check-sat)

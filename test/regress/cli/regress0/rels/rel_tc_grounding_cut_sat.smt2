; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: sat
; Companion of rel_tc_grounding_cut without b /= d: with b = d, (a, b) and
; (b, c) are in R and (a, c) is in TC(R). The conflict must not refute it.
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
(assert (not (= b c)))
(check-sat)

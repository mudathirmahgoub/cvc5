; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset --rels-cycle-def-union
; EXPECT: unsat
;
; A cycle of A U B lies in the transitive, acyclic H. With
; --rels-cycle-def-union, (rel.cyclic (set.union A B)) also gives
; (s1, s1) in TC(A U B), and closure induction turns it into (s1, s1) in H,
; which contradicts (not (rel.cyclic H)). Without the option the witness
; s1 -> s2 -> ... is refuted one length at a time and the problem times out.
(set-logic ALL)
(declare-sort E 0)
(declare-const A (Relation E E))
(declare-const B (Relation E E))
(declare-const H (Relation E E))
(assert (set.subset (set.union A B) H))
(assert (set.subset (rel.join H H) H))
(assert (not (rel.cyclic H)))
(assert (rel.cyclic (set.union A B)))
(check-sat)

; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: unsat
; Companion of rel_join_grounding_merge (join grounding conflict of
; --rels-acyclic-hammer, an option of this branch): with a, b, c, d distinct,
; A;B = {(a, b)};{(d, c)} is empty, and the conflict refutes (a, c) in A;B.
(set-logic ALL)
(declare-sort U 0)
(declare-const A (Relation U U))
(declare-const B (Relation U U))
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= A (set.singleton (tuple a b))))
(assert (= B (set.singleton (tuple d c))))
(assert (set.member (tuple a c) (rel.join A B)))
(assert (distinct a b c d))
(check-sat)

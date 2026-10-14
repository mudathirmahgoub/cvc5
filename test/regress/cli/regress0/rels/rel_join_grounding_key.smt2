; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: unsat
; Join grounding conflict of --rels-acyclic-hammer: only the disequality that
; blocks the one way of deriving (a, c) is a premise, b /= d (the shared
; element), not distinct(a, b, c, d). So a single conflict refutes the
; membership, whatever the other elements are equal to.
(set-logic ALL)
(declare-sort U 0)
(declare-fun A () (Relation U U))
(declare-fun B () (Relation U U))
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= A (set.singleton (tuple a b))))
(assert (= B (set.singleton (tuple d c))))
(assert (set.member (tuple a c) (rel.join A B)))
(assert (not (= b d)))
(check-sat)

; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: sat
; Tests the join grounding conflict of --rels-acyclic-hammer, an option of
; this branch (cvc5 main has neither the option nor the conflict, and answers
; sat here because it always splits join memberships). The hammer does not
; split (a, c) in A;B, so b = d is not derived and the membership looks
; unexplained at last call. The conflict must not refute it: in the model with
; b = d, A = {(a, b)}, B = {(b, c)} and A;B = {(a, c)}. The earlier version of
; the conflict, without the distinctness of the elements, did, and the answer
; was unsat.
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
(check-sat)

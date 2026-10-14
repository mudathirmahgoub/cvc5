; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; EXPECT: unsat
;
; Every edge of (rel.join (rel.iden A) po) is an edge of po, so a cycle of it
; would be a cycle of po, which is asserted acyclic. The contradiction only
; appears when the cycle witness closes, so unrolling the witness edge by edge
; never terminates: each unrolled edge is shown to be a po edge, but the cycle
; can always be assumed longer. The anchoring rule derives the contradiction
; directly from the two acyclicity constraints (the cyclic relation is
; syntactically included in the closure of the acyclic one).
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort Atom 0)
(declare-fun po () (Relation Atom Atom))
(declare-fun A () (Set (Tuple Atom)))
(declare-fun B () (Set (Tuple Atom)))
(assert (not (rel.cyclic po)))
(assert (rel.cyclic (set.union (rel.join (rel.iden A) po) (rel.join (rel.join (rel.iden B) po) (rel.iden A)))))
(check-sat)

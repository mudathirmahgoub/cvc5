; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-cycle-len-decide
; EXPECT: sat
;
; Satisfiable with A = {(a, a)}. Without --rels-cycle-len-decide every
; candidate model gives the length l of the witness a new, larger value, the
; last call completes the witness to that length, and the search does not
; terminate. The decision strategy decides l <= 2, l <= 3, ... first.
(set-logic ALL)
(declare-sort E 0)
(declare-const A (Relation E E))
(declare-const B (Relation E E))
(assert (rel.cyclic (set.union A B)))
(check-sat)

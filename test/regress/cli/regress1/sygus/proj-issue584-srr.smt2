; REQUIRES: unrestricted-mode
; SCRUBBER: grep -v -E '.*'
; EXIT: 0
; the checker of candidate rewrites asks for a model when it refutes one
(set-option :produce-models true)
(set-logic ALL)
(declare-const x (Bag Bool))
(assert (> (bag.card (bag.inter_min x bag.empty)) (bag.card (bag.inter_min x bag.empty))))
(find-synth :rewrite_input)

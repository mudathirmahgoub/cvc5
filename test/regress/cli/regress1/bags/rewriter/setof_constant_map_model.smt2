; REQUIRES: unrestricted-mode
; SETOF_MAP_CONSTANT rewrites the bag.setof of the map to (bag 0 p), with p = 0
; for an empty s; the model must still give s two rows, so that the map has
; the row 0 twice
(set-logic HO_ALL)
(set-info :status sat)
(declare-const s (Bag Int))
(assert (not (= (bag.setof (bag.map (lambda ((x Int)) 0) s))
                (bag.map (lambda ((x Int)) 0) s))))
(check-sat)

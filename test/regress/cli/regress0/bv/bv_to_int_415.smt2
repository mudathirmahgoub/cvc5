; REQUIRES: unrestricted-mode
; EXPECT: 
; SCRUBBER: grep -v "higher.order"
; EXIT: 1
(set-option :solve-bv-as-int sum)
(set-logic HO_ALL)
(declare-const _x108 (Bag (_ BitVec 4)) )
(declare-fun _x113 ((_ BitVec 4)) (_ BitVec 4))
; the map is compared with a nonempty bag: the bags rewriter turns
; (= (bag.map f X) bag.empty) into (= X bag.empty), which has no map
(assert (= (bag.map _x113 _x108) (bag #b0001 1)))
(check-sat)

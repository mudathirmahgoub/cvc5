; REQUIRES: unrestricted-mode
; DISABLE-TESTER: model
; (the debug model check warns that the lambda of the aggregates' reduction,
; (lambda ((t (Bag (Tuple Int Int)))) (bag.fold f i t)), has no constant
; value)
; AGGREGATE_JOIN_MERGE merges two aggregates joined on their group columns only
; when they seed their copies of those columns alike: here (tuple 1 0) and
; (tuple 2 0), and for an empty X the join of their rows of initial values is
; empty
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int Int)))
(define-fun fa ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
(define-fun fb ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
; two aggregates over X by column 0, whose seeds differ in the key copy
(define-fun A () (Bag (Tuple Int Int)) ((_ table.aggr 0) fa (tuple 1 0) X))
(define-fun B () (Bag (Tuple Int Int)) ((_ table.aggr 0) fb (tuple 2 0) X))
(define-fun Q () (Bag (Tuple Int))
  (bag.map (lambda ((r (Tuple Int Int Int Int))) (tuple ((_ tuple.select 3) r)))
    (bag.filter (lambda ((r (Tuple Int Int Int Int))) (= ((_ tuple.select 0) r) ((_ tuple.select 2) r)))
      (table.product A B))))
; X empty: A = {(1, 0)}, B = {(2, 0)}, the join (= 1 2) is false and Q is empty, so this is sat
(assert (= (bag.card X) 0))
(assert (= Q (as bag.empty (Bag (Tuple Int)))))
(check-sat)

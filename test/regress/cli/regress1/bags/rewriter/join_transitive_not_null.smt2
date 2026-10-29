; FILTER_JOIN_TRANSITIVE carries a condition across a join, and NOT_NULL_COLUMNS
; decides the null tests of columns that are never null: the null test of Y's
; column 0, carried to X's column 0 by the join, is one the rows of the product
; satisfy, so it is not added, and the two rules do not undo each other
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple (Nullable Int) Int)))
(declare-const Y (Bag (Tuple (Nullable Int) Int)))
(define-fun J () (Bag (Tuple (Nullable Int) Int (Nullable Int) Int))
  (bag.filter (lambda ((t (Tuple (Nullable Int) Int (Nullable Int) Int)))
                (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
    (table.product
      (bag.filter (lambda ((s (Tuple (Nullable Int) Int))) (nullable.is_some ((_ tuple.select 0) s))) X)
      (bag.filter (lambda ((s (Tuple (Nullable Int) Int))) (nullable.is_some ((_ tuple.select 0) s))) Y))))
(assert (distinct J (as bag.empty (Bag (Tuple (Nullable Int) Int (Nullable Int) Int)))))
(check-sat)

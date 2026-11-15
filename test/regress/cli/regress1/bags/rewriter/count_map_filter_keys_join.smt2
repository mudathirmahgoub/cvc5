; REQUIRES: unrestricted-mode
; COUNT_MAP_FILTER_KEYS moves a conjunct of a filter that reads only the
; projected columns onto the probe. It must not when the filter's own rules
; bring the conjunct back: here the join equations and the null test of
; column 1 imply the null test of column 0, which FILTER_JOIN_TRANSITIVE adds
; again, and the two rules undid each other forever.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const u (Bag (Tuple (Nullable Int))))
(declare-const v (Bag (Tuple (Nullable Int))))
(declare-const w (Bag (Tuple (Nullable Int))))
(declare-const p (Tuple (Nullable Int)))
(assert
  (= (bag.count
       p
       (bag.map
         (lambda ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int))))
           (tuple ((_ tuple.select 0) t)))
         (bag.filter
           (lambda ((t (Tuple (Nullable Int) (Nullable Int) (Nullable Int))))
             (and (nullable.is_some ((_ tuple.select 1) t))
                  (= ((_ tuple.select 1) t) ((_ tuple.select 2) t))
                  (= ((_ tuple.select 1) t) ((_ tuple.select 0) t))))
           (table.product u (table.product v w)))))
     1))
(check-sat)

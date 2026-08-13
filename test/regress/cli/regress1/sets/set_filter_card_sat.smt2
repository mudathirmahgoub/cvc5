; EXPECT: sat
(set-logic HO_ALL)
(set-option :sets-exp true)
(set-info :status sat)
; Cardinality combined with set.filter. The cardinality solver has to pad S with
; a slack element, which must satisfy the filter predicates for the model to be
; correct. See CardinalityExtension::mkConstrainedSlackElement.
(declare-fun S () (Set String))
(assert (= (set.filter (lambda ((x String)) (str.prefixof "foo" x)) S) S))
(assert (= (set.filter (lambda ((x String)) (str.suffixof "bar" x)) S) S))
(assert (> (set.card S) 1))
(check-sat)

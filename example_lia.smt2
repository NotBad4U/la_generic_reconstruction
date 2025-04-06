(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

(assert (= x 2))
(assert (= 0 y))
(assert (or (< (+ x y) 1) (< 3 x)))

(check-sat)
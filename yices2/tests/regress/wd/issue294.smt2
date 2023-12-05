(set-logic QF_ALIA)
(declare-fun x0 () (Array Bool Bool))
(declare-const v16 Bool)
(declare-const A1 (Array Bool Bool))
(declare-const A2 (Array Bool Bool))
(declare-const A3 (Array (Array Bool Bool) Bool))

(assert (= (select (store (store A1 false false) true true) v16) true))
(assert (= (select (store (store A3 A2 (select A1 true)) x0 true) (store (store A1 false false) true true)) true))
(assert (select A3 (store A1 v16 false)))
(check-sat)

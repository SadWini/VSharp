(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(assert (< (* x x) 2))
(check-sat)
(exit)

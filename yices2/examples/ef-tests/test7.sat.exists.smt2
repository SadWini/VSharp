;; test7.sat.ys converted to the SMT-LIB2 notation
(set-logic LRA)

(assert (exists ((x Real) (y Real)) (and (not (= x y)) (forall ((z Real)) (=> (> y z) (> x z))))))
(check-sat)
(get-model)

(set-logic QF_UFLIA)
(set-info :source |
  These benchmarks were obtained from the KIND tool during verification of
  Lustre programs.  See also the lustre family of benchmarks in QF_LIA.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(declare-fun _base () Int)
(declare-fun _n () Int)
(assert (<= 0 _n))
(declare-fun ___z2z___ (Int) Bool)
(declare-fun ___z3z___ (Int) Bool)
(declare-fun ___z4z___ (Int) Bool)
(declare-fun ___z5z___ (Int) Bool)
(declare-fun ___z6z___ (Int) Int)
(declare-fun ___z7z___ (Int) Int)
(declare-fun ___z8z___ (Int) Int)
(declare-fun ___z9z___ (Int) Int)
(declare-fun ___z10z___ (Int) Int)
(declare-fun ___z11z___ (Int) Bool)
(declare-fun ___z12z___ (Int) Bool)
(declare-fun ___z13z___ (Int) Bool)
(declare-fun ___z14z___ (Int) Bool)
(declare-fun ___z15z___ (Int) Bool)
(declare-fun ___z16z___ (Int) Bool)
(declare-fun ___z17z___ (Int) Bool)
(declare-fun ___z18z___ (Int) Bool)
(declare-fun ___z19z___ (Int) Int)
(declare-fun ___z20z___ (Int) Int)
(declare-fun ___z21z___ (Int) Bool)
(declare-fun ___z22z___ (Int) Bool)
(push 1)
(assert (= (+ (___z8z___ 0) (+ (* (- 1) (___z7z___ 0)) (___z10z___ 0))) 0))
(assert (let ((?v_0 (___z20z___ (- 1)))) (= (ite (= _base 0) 0 (ite (and (___z12z___ 0) (___z12z___ (- 1))) (ite (___z3z___ 0) (+ 1 (+ 1 ?v_0)) ?v_0) 0)) (___z20z___ 0))))
(assert (let ((?v_0 (= _base 0)) (?v_1 (___z9z___ 0)) (?v_2 (___z11z___ (- 1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_1) ?v_2) (or (not (<= ?v_1 0)) (not ?v_2))))) (___z11z___ 0))))
(assert (= (and (not (<= 32767 (___z9z___ 0))) (and (not (<= 1 (___z8z___ 0))) (and (not (<= 1 (___z7z___ 0))) (and (not (<= 1 (___z6z___ 0))) (___z16z___ 0))))) (___z21z___ 0)))
(assert (let ((?v_1 (___z10z___ 0)) (?v_0 (= _base 0)) (?v_2 (___z12z___ (- 1)))) (= (___z12z___ 0) (and (not ?v_0) (or ?v_0 (and (or ?v_2 (<= 10 ?v_1)) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (let ((?v_0 (= _base 0)) (?v_1 (___z21z___ 0))) (= (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (- 1))))) (___z22z___ 0))))
(assert (let ((?v_0 (= _base 0)) (?v_1 (___z9z___ 0)) (?v_2 (___z13z___ (- 1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z13z___ 0))))
(assert (let ((?v_1 (___z10z___ 0)) (?v_0 (= _base 0)) (?v_2 (___z14z___ (- 1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z14z___ 0))))
(assert (= (or (not (___z22z___ 0)) (or (= _base 0) (___z15z___ (- 1)))) (___z5z___ 0)))
(assert (= (or (= _base 0) (not (or (and (___z11z___ 0) (___z13z___ (- 1))) (and (___z11z___ (- 1)) (___z13z___ 0))))) (___z15z___ 0)))
(assert (let ((?v_0 (___z6z___ (- 1)))) (= (___z6z___ 0) (ite (= _base 0) 0 (ite (___z2z___ 0) (+ 1 (+ 1 ?v_0)) ?v_0)))))
(assert (= (___z16z___ 0) (and (___z18z___ 0) (___z17z___ 0))))
(assert (let ((?v_0 (___z7z___ (- 1)))) (= (___z7z___ 0) (ite (= _base 0) 0 (ite (___z3z___ 0) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z17z___ 0) (or (= _base 0) (and (or (not (<= 9 (___z19z___ (- 1)))) (not (___z2z___ 0))) (or (not (___z13z___ (- 1))) (not (___z4z___ 0)))))))
(assert (let ((?v_0 (___z8z___ (- 1)))) (= (___z8z___ 0) (ite (= _base 0) 0 (ite (___z4z___ 0) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z18z___ 0) (or (= _base 0) (and (or (not (<= 9 (___z20z___ (- 1)))) (not (___z3z___ 0))) (or (not (___z14z___ (- 1))) (not (___z4z___ 0)))))))
(assert (= (+ (___z8z___ 0) (+ (___z9z___ 0) (* (- 1) (___z6z___ 0)))) 0))
(assert (let ((?v_0 (___z19z___ (- 1)))) (= (ite (= _base 0) 0 (ite (and (___z11z___ (- 1)) (___z11z___ 0)) (ite (___z2z___ 0) (+ 1 (+ 1 ?v_0)) ?v_0) 0)) (___z19z___ 0))))
(assert (= (+ (___z7z___ (- 1)) (+ (* (- 1) (___z8z___ (- 1))) (* (- 1) (___z10z___ (- 1))))) 0))
(assert (let ((?v_0 (___z20z___ (- 2)))) (= (___z20z___ (- 1)) (ite (= _base (- 1)) 0 (ite (and (___z12z___ (- 1)) (___z12z___ (- 2))) (ite (___z3z___ (- 1)) (+ 1 (+ 1 ?v_0)) ?v_0) 0)))))
(assert (let ((?v_0 (= _base (- 1))) (?v_1 (___z9z___ (- 1))) (?v_2 (___z11z___ (- 2)))) (= (___z11z___ (- 1)) (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_1) ?v_2) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (= (and (not (<= 32767 (___z9z___ (- 1)))) (and (not (<= 1 (___z8z___ (- 1)))) (and (not (<= 1 (___z7z___ (- 1)))) (and (not (<= 1 (___z6z___ (- 1)))) (___z16z___ (- 1)))))) (___z21z___ (- 1))))
(assert (let ((?v_1 (___z10z___ (- 1))) (?v_0 (= _base (- 1))) (?v_2 (___z12z___ (- 2)))) (= (___z12z___ (- 1)) (and (not ?v_0) (or ?v_0 (and (or ?v_2 (<= 10 ?v_1)) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (let ((?v_0 (= _base (- 1))) (?v_1 (___z21z___ (- 1)))) (= (___z22z___ (- 1)) (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (- 2))))))))
(assert (let ((?v_0 (= _base (- 1))) (?v_1 (___z9z___ (- 1))) (?v_2 (___z13z___ (- 2)))) (= (___z13z___ (- 1)) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))))))
(assert (let ((?v_1 (___z10z___ (- 1))) (?v_0 (= _base (- 1))) (?v_2 (___z14z___ (- 2)))) (= (___z14z___ (- 1)) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))))))
(assert (= (or (not (___z22z___ (- 1))) (or (= _base (- 1)) (___z15z___ (- 2)))) (___z5z___ (- 1))))
(assert (= (___z15z___ (- 1)) (or (= _base (- 1)) (not (or (and (___z11z___ (- 1)) (___z13z___ (- 2))) (and (___z13z___ (- 1)) (___z11z___ (- 2))))))))
(assert (let ((?v_0 (___z6z___ (- 2)))) (= (___z6z___ (- 1)) (ite (= _base (- 1)) 0 (ite (___z2z___ (- 1)) (+ 1 (+ 1 ?v_0)) ?v_0)))))
(assert (= (___z16z___ (- 1)) (and (___z18z___ (- 1)) (___z17z___ (- 1)))))
(assert (let ((?v_0 (___z7z___ (- 2)))) (= (___z7z___ (- 1)) (ite (= _base (- 1)) 0 (ite (___z3z___ (- 1)) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z17z___ (- 1)) (or (= _base (- 1)) (and (or (not (<= 9 (___z19z___ (- 2)))) (not (___z2z___ (- 1)))) (or (not (___z13z___ (- 2))) (not (___z4z___ (- 1))))))))
(assert (let ((?v_0 (___z8z___ (- 2)))) (= (___z8z___ (- 1)) (ite (= _base (- 1)) 0 (ite (___z4z___ (- 1)) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z18z___ (- 1)) (or (= _base (- 1)) (and (or (not (<= 9 (___z20z___ (- 2)))) (not (___z3z___ (- 1)))) (or (not (___z14z___ (- 2))) (not (___z4z___ (- 1))))))))
(assert (= (+ (___z6z___ (- 1)) (+ (* (- 1) (___z8z___ (- 1))) (* (- 1) (___z9z___ (- 1))))) 0))
(assert (let ((?v_0 (___z19z___ (- 2)))) (= (___z19z___ (- 1)) (ite (= _base (- 1)) 0 (ite (and (___z11z___ (- 1)) (___z11z___ (- 2))) (ite (___z2z___ (- 1)) (+ 1 (+ 1 ?v_0)) ?v_0) 0)))))
(push 1)
(assert (not (or (not (= _base (- 1))) (and (___z5z___ 0) (___z5z___ (- 1))))))
(assert true)
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (___z5z___ (- 1)))
(assert (___z5z___ (- 2)))
(push 1)
(assert (= (+ (___z8z___ _n) (+ (* (- 1) (___z7z___ _n)) (___z10z___ _n))) 0))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z20z___ ?v_0))) (= (ite (= _n _base) 0 (ite (and (___z12z___ _n) (___z12z___ ?v_0)) (ite (___z3z___ _n) (+ 1 (+ 1 ?v_1)) ?v_1) 0)) (___z20z___ _n)))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z9z___ _n)) (?v_2 (___z11z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_1) ?v_2) (or (not (<= ?v_1 0)) (not ?v_2))))) (___z11z___ _n))))
(assert (= (and (not (<= 32767 (___z9z___ _n))) (and (not (<= 1 (___z8z___ _n))) (and (not (<= 1 (___z7z___ _n))) (and (not (<= 1 (___z6z___ _n))) (___z16z___ _n))))) (___z21z___ _n)))
(assert (let ((?v_1 (___z10z___ _n)) (?v_0 (= _n _base)) (?v_2 (___z12z___ (+ _n (- 1))))) (= (___z12z___ _n) (and (not ?v_0) (or ?v_0 (and (or ?v_2 (<= 10 ?v_1)) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z21z___ _n))) (= (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (+ _n (- 1)))))) (___z22z___ _n))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z9z___ _n)) (?v_2 (___z13z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z13z___ _n))))
(assert (let ((?v_1 (___z10z___ _n)) (?v_0 (= _n _base)) (?v_2 (___z14z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z14z___ _n))))
(assert (= (or (not (___z22z___ _n)) (or (= _n _base) (___z15z___ (+ _n (- 1))))) (___z5z___ _n)))
(assert (let ((?v_0 (+ _n (- 1)))) (= (or (= _n _base) (not (or (and (___z11z___ _n) (___z13z___ ?v_0)) (and (___z11z___ ?v_0) (___z13z___ _n))))) (___z15z___ _n))))
(assert (let ((?v_0 (___z6z___ (+ _n (- 1))))) (= (___z6z___ _n) (ite (= _n _base) 0 (ite (___z2z___ _n) (+ 1 (+ 1 ?v_0)) ?v_0)))))
(assert (= (___z16z___ _n) (and (___z18z___ _n) (___z17z___ _n))))
(assert (let ((?v_0 (___z7z___ (+ _n (- 1))))) (= (___z7z___ _n) (ite (= _n _base) 0 (ite (___z3z___ _n) (+ 1 ?v_0) ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z17z___ _n) (or (= _n _base) (and (or (not (<= 9 (___z19z___ ?v_0))) (not (___z2z___ _n))) (or (not (___z13z___ ?v_0)) (not (___z4z___ _n))))))))
(assert (let ((?v_0 (___z8z___ (+ _n (- 1))))) (= (___z8z___ _n) (ite (= _n _base) 0 (ite (___z4z___ _n) (+ 1 ?v_0) ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z18z___ _n) (or (= _n _base) (and (or (not (<= 9 (___z20z___ ?v_0))) (not (___z3z___ _n))) (or (not (___z14z___ ?v_0)) (not (___z4z___ _n))))))))
(assert (= (+ (___z8z___ _n) (+ (___z9z___ _n) (* (- 1) (___z6z___ _n)))) 0))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z19z___ ?v_0))) (= (ite (= _n _base) 0 (ite (and (___z11z___ ?v_0) (___z11z___ _n)) (ite (___z2z___ _n) (+ 1 (+ 1 ?v_1)) ?v_1) 0)) (___z19z___ _n)))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (+ (___z7z___ ?v_0) (+ (* (- 1) (___z8z___ ?v_0)) (* (- 1) (___z10z___ ?v_0)))) 0)))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z20z___ ?v_1))) (= (___z20z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (and (___z12z___ ?v_0) (___z12z___ ?v_1)) (ite (___z3z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)))))))
(assert (let ((?v_1 (+ _n (- 1))) (?v_0 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z11z___ (+ (- 1) ?v_1)))) (= (___z11z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_2) ?v_3) (or (not (<= ?v_2 0)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (and (not (<= 32767 (___z9z___ ?v_0))) (and (not (<= 1 (___z8z___ ?v_0))) (and (not (<= 1 (___z7z___ ?v_0))) (and (not (<= 1 (___z6z___ ?v_0))) (___z16z___ ?v_0))))) (___z21z___ ?v_0))))
(assert (let ((?v_1 (+ _n (- 1)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 1)) (?v_3 (___z12z___ (+ (- 1) ?v_1)))) (= (___z12z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or ?v_3 (<= 10 ?v_2)) (or (not (<= ?v_2 0)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1))) (?v_1 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z21z___ ?v_0))) (= (___z22z___ ?v_0) (and (or (not ?v_1) ?v_2) (or ?v_1 (and ?v_2 (___z22z___ (+ (- 1) ?v_0)))))))))
(assert (let ((?v_1 (+ _n (- 1))) (?v_0 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z13z___ (+ (- 1) ?v_1)))) (= (___z13z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3)))))))))
(assert (let ((?v_1 (+ _n (- 1)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 1)) (?v_3 (___z14z___ (+ (- 1) ?v_1)))) (= (___z14z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (or (not (___z22z___ ?v_0)) (or (= (+ _n (* (- 1) _base)) 1) (___z15z___ (+ (- 1) ?v_0)))) (___z5z___ ?v_0))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z15z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (not (or (and (___z11z___ ?v_0) (___z13z___ ?v_1)) (and (___z13z___ ?v_0) (___z11z___ ?v_1)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z6z___ (+ (- 1) ?v_0)))) (= (___z6z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_1)) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z16z___ ?v_0) (and (___z18z___ ?v_0) (___z17z___ ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z7z___ (+ (- 1) ?v_0)))) (= (___z7z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z3z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z17z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (and (or (not (<= 9 (___z19z___ ?v_1))) (not (___z2z___ ?v_0))) (or (not (___z13z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z8z___ (+ (- 1) ?v_0)))) (= (___z8z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z4z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z18z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (and (or (not (<= 9 (___z20z___ ?v_1))) (not (___z3z___ ?v_0))) (or (not (___z14z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (+ (___z6z___ ?v_0) (+ (* (- 1) (___z8z___ ?v_0)) (* (- 1) (___z9z___ ?v_0)))) 0)))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z19z___ ?v_1))) (= (___z19z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (and (___z11z___ ?v_0) (___z11z___ ?v_1)) (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)))))))
(assert (___z5z___ (+ _n (- 1))))
(assert (not (or (not (= _base (- 1))) (___z5z___ _n))))
(assert true)
(set-info :status sat)
(check-sat)
(pop 1)
(assert (___z5z___ (+ _n (- 1))))
(assert (___z5z___ (+ _n (- 2))))
(assert (= (+ (___z7z___ (- 2)) (+ (* (- 1) (___z8z___ (- 2))) (* (- 1) (___z10z___ (- 2))))) 0))
(assert (let ((?v_0 (___z20z___ (- 3)))) (= (___z20z___ (- 2)) (ite (= _base (- 2)) 0 (ite (and (___z12z___ (- 2)) (___z12z___ (- 3))) (ite (___z3z___ (- 2)) (+ 1 (+ 1 ?v_0)) ?v_0) 0)))))
(assert (let ((?v_0 (= _base (- 2))) (?v_1 (___z9z___ (- 2))) (?v_2 (___z11z___ (- 3)))) (= (___z11z___ (- 2)) (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_1) ?v_2) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (= (and (not (<= 32767 (___z9z___ (- 2)))) (and (not (<= 1 (___z8z___ (- 2)))) (and (not (<= 1 (___z7z___ (- 2)))) (and (not (<= 1 (___z6z___ (- 2)))) (___z16z___ (- 2)))))) (___z21z___ (- 2))))
(assert (let ((?v_1 (___z10z___ (- 2))) (?v_0 (= _base (- 2))) (?v_2 (___z12z___ (- 3)))) (= (___z12z___ (- 2)) (and (not ?v_0) (or ?v_0 (and (or ?v_2 (<= 10 ?v_1)) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (let ((?v_0 (= _base (- 2))) (?v_1 (___z21z___ (- 2)))) (= (___z22z___ (- 2)) (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (- 3))))))))
(assert (let ((?v_0 (= _base (- 2))) (?v_1 (___z9z___ (- 2))) (?v_2 (___z13z___ (- 3)))) (= (___z13z___ (- 2)) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))))))
(assert (let ((?v_1 (___z10z___ (- 2))) (?v_0 (= _base (- 2))) (?v_2 (___z14z___ (- 3)))) (= (___z14z___ (- 2)) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))))))
(assert (= (___z5z___ (- 2)) (or (not (___z22z___ (- 2))) (or (= _base (- 2)) (___z15z___ (- 3))))))
(assert (= (___z15z___ (- 2)) (or (= _base (- 2)) (not (or (and (___z11z___ (- 2)) (___z13z___ (- 3))) (and (___z13z___ (- 2)) (___z11z___ (- 3))))))))
(assert (let ((?v_0 (___z6z___ (- 3)))) (= (___z6z___ (- 2)) (ite (= _base (- 2)) 0 (ite (___z2z___ (- 2)) (+ 1 (+ 1 ?v_0)) ?v_0)))))
(assert (= (___z16z___ (- 2)) (and (___z18z___ (- 2)) (___z17z___ (- 2)))))
(assert (let ((?v_0 (___z7z___ (- 3)))) (= (___z7z___ (- 2)) (ite (= _base (- 2)) 0 (ite (___z3z___ (- 2)) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z17z___ (- 2)) (or (= _base (- 2)) (and (or (not (<= 9 (___z19z___ (- 3)))) (not (___z2z___ (- 2)))) (or (not (___z13z___ (- 3))) (not (___z4z___ (- 2))))))))
(assert (let ((?v_0 (___z8z___ (- 3)))) (= (___z8z___ (- 2)) (ite (= _base (- 2)) 0 (ite (___z4z___ (- 2)) (+ 1 ?v_0) ?v_0)))))
(assert (= (___z18z___ (- 2)) (or (= _base (- 2)) (and (or (not (<= 9 (___z20z___ (- 3)))) (not (___z3z___ (- 2)))) (or (not (___z14z___ (- 3))) (not (___z4z___ (- 2))))))))
(assert (= (+ (___z6z___ (- 2)) (+ (* (- 1) (___z8z___ (- 2))) (* (- 1) (___z9z___ (- 2))))) 0))
(assert (let ((?v_0 (___z19z___ (- 3)))) (= (___z19z___ (- 2)) (ite (= _base (- 2)) 0 (ite (and (___z11z___ (- 2)) (___z11z___ (- 3))) (ite (___z2z___ (- 2)) (+ 1 (+ 1 ?v_0)) ?v_0) 0)))))
(assert (= (+ (___z8z___ _n) (+ (* (- 1) (___z7z___ _n)) (___z10z___ _n))) 0))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z20z___ ?v_0))) (= (ite (= _n _base) 0 (ite (and (___z12z___ _n) (___z12z___ ?v_0)) (ite (___z3z___ _n) (+ 1 (+ 1 ?v_1)) ?v_1) 0)) (___z20z___ _n)))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z9z___ _n)) (?v_2 (___z11z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_1) ?v_2) (or (not (<= ?v_1 0)) (not ?v_2))))) (___z11z___ _n))))
(assert (= (and (not (<= 32767 (___z9z___ _n))) (and (not (<= 1 (___z8z___ _n))) (and (not (<= 1 (___z7z___ _n))) (and (not (<= 1 (___z6z___ _n))) (___z16z___ _n))))) (___z21z___ _n)))
(assert (let ((?v_1 (___z10z___ _n)) (?v_0 (= _n _base)) (?v_2 (___z12z___ (+ _n (- 1))))) (= (___z12z___ _n) (and (not ?v_0) (or ?v_0 (and (or ?v_2 (<= 10 ?v_1)) (or (not (<= ?v_1 0)) (not ?v_2))))))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z21z___ _n))) (= (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (+ _n (- 1)))))) (___z22z___ _n))))
(assert (let ((?v_0 (= _n _base)) (?v_1 (___z9z___ _n)) (?v_2 (___z13z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z13z___ _n))))
(assert (let ((?v_1 (___z10z___ _n)) (?v_0 (= _n _base)) (?v_2 (___z14z___ (+ _n (- 1))))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_1 (- 10)) ?v_2) (or (not (<= 0 ?v_1)) (not ?v_2))))) (___z14z___ _n))))
(assert (= (or (not (___z22z___ _n)) (or (= _n _base) (___z15z___ (+ _n (- 1))))) (___z5z___ _n)))
(assert (let ((?v_0 (+ _n (- 1)))) (= (or (= _n _base) (not (or (and (___z11z___ _n) (___z13z___ ?v_0)) (and (___z11z___ ?v_0) (___z13z___ _n))))) (___z15z___ _n))))
(assert (let ((?v_0 (___z6z___ (+ _n (- 1))))) (= (___z6z___ _n) (ite (= _n _base) 0 (ite (___z2z___ _n) (+ 1 (+ 1 ?v_0)) ?v_0)))))
(assert (= (___z16z___ _n) (and (___z18z___ _n) (___z17z___ _n))))
(assert (let ((?v_0 (___z7z___ (+ _n (- 1))))) (= (___z7z___ _n) (ite (= _n _base) 0 (ite (___z3z___ _n) (+ 1 ?v_0) ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z17z___ _n) (or (= _n _base) (and (or (not (<= 9 (___z19z___ ?v_0))) (not (___z2z___ _n))) (or (not (___z13z___ ?v_0)) (not (___z4z___ _n))))))))
(assert (let ((?v_0 (___z8z___ (+ _n (- 1))))) (= (___z8z___ _n) (ite (= _n _base) 0 (ite (___z4z___ _n) (+ 1 ?v_0) ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z18z___ _n) (or (= _n _base) (and (or (not (<= 9 (___z20z___ ?v_0))) (not (___z3z___ _n))) (or (not (___z14z___ ?v_0)) (not (___z4z___ _n))))))))
(assert (= (+ (___z8z___ _n) (+ (___z9z___ _n) (* (- 1) (___z6z___ _n)))) 0))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z19z___ ?v_0))) (= (ite (= _n _base) 0 (ite (and (___z11z___ ?v_0) (___z11z___ _n)) (ite (___z2z___ _n) (+ 1 (+ 1 ?v_1)) ?v_1) 0)) (___z19z___ _n)))))
(push 1)
(assert (not (or (___z5z___ 0) (not (= _base (- 2))))))
(assert true)
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (___z5z___ (- 3)))
(push 1)
(assert (let ((?v_0 (+ _n (- 1)))) (= (+ (___z7z___ ?v_0) (+ (* (- 1) (___z8z___ ?v_0)) (* (- 1) (___z10z___ ?v_0)))) 0)))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z20z___ ?v_1))) (= (___z20z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (and (___z12z___ ?v_0) (___z12z___ ?v_1)) (ite (___z3z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)))))))
(assert (let ((?v_1 (+ _n (- 1))) (?v_0 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z11z___ (+ (- 1) ?v_1)))) (= (___z11z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_2) ?v_3) (or (not (<= ?v_2 0)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (and (not (<= 32767 (___z9z___ ?v_0))) (and (not (<= 1 (___z8z___ ?v_0))) (and (not (<= 1 (___z7z___ ?v_0))) (and (not (<= 1 (___z6z___ ?v_0))) (___z16z___ ?v_0))))) (___z21z___ ?v_0))))
(assert (let ((?v_1 (+ _n (- 1)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 1)) (?v_3 (___z12z___ (+ (- 1) ?v_1)))) (= (___z12z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or ?v_3 (<= 10 ?v_2)) (or (not (<= ?v_2 0)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1))) (?v_1 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z21z___ ?v_0))) (= (___z22z___ ?v_0) (and (or (not ?v_1) ?v_2) (or ?v_1 (and ?v_2 (___z22z___ (+ (- 1) ?v_0)))))))))
(assert (let ((?v_1 (+ _n (- 1))) (?v_0 (= (+ _n (* (- 1) _base)) 1))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z13z___ (+ (- 1) ?v_1)))) (= (___z13z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3)))))))))
(assert (let ((?v_1 (+ _n (- 1)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 1)) (?v_3 (___z14z___ (+ (- 1) ?v_1)))) (= (___z14z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (or (not (___z22z___ ?v_0)) (or (= (+ _n (* (- 1) _base)) 1) (___z15z___ (+ (- 1) ?v_0)))) (___z5z___ ?v_0))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z15z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (not (or (and (___z11z___ ?v_0) (___z13z___ ?v_1)) (and (___z13z___ ?v_0) (___z11z___ ?v_1)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z6z___ (+ (- 1) ?v_0)))) (= (___z6z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_1)) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (___z16z___ ?v_0) (and (___z18z___ ?v_0) (___z17z___ ?v_0)))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z7z___ (+ (- 1) ?v_0)))) (= (___z7z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z3z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z17z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (and (or (not (<= 9 (___z19z___ ?v_1))) (not (___z2z___ ?v_0))) (or (not (___z13z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (___z8z___ (+ (- 1) ?v_0)))) (= (___z8z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (___z4z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z18z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 1) (and (or (not (<= 9 (___z20z___ ?v_1))) (not (___z3z___ ?v_0))) (or (not (___z14z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 1)))) (= (+ (___z6z___ ?v_0) (+ (* (- 1) (___z8z___ ?v_0)) (* (- 1) (___z9z___ ?v_0)))) 0)))
(assert (let ((?v_0 (+ _n (- 1)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z19z___ ?v_1))) (= (___z19z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 1) 0 (ite (and (___z11z___ ?v_0) (___z11z___ ?v_1)) (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)))))))
(assert (let ((?v_0 (+ _n (- 2)))) (= (+ (___z8z___ ?v_0) (+ (* (- 1) (___z7z___ ?v_0)) (___z10z___ ?v_0))) 0)))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z20z___ ?v_1))) (= (ite (= (+ _n (* (- 1) _base)) 2) 0 (ite (and (___z12z___ ?v_0) (___z12z___ ?v_1)) (ite (___z3z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)) (___z20z___ ?v_0))))))
(assert (let ((?v_1 (+ _n (- 2))) (?v_0 (= (+ _n (* (- 1) _base)) 2))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z11z___ (+ (- 1) ?v_1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= 10 ?v_2) ?v_3) (or (not (<= ?v_2 0)) (not ?v_3))))) (___z11z___ ?v_1)))))
(assert (let ((?v_0 (+ _n (- 2)))) (= (and (not (<= 32767 (___z9z___ ?v_0))) (and (not (<= 1 (___z8z___ ?v_0))) (and (not (<= 1 (___z7z___ ?v_0))) (and (not (<= 1 (___z6z___ ?v_0))) (___z16z___ ?v_0))))) (___z21z___ ?v_0))))
(assert (let ((?v_1 (+ _n (- 2)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 2)) (?v_3 (___z12z___ (+ (- 1) ?v_1)))) (= (___z12z___ ?v_1) (and (not ?v_0) (or ?v_0 (and (or ?v_3 (<= 10 ?v_2)) (or (not (<= ?v_2 0)) (not ?v_3)))))))))
(assert (let ((?v_2 (+ _n (- 2))) (?v_0 (= (+ _n (* (- 1) _base)) 2))) (let ((?v_1 (___z21z___ ?v_2))) (= (and (or (not ?v_0) ?v_1) (or ?v_0 (and ?v_1 (___z22z___ (+ (- 1) ?v_2))))) (___z22z___ ?v_2)))))
(assert (let ((?v_1 (+ _n (- 2))) (?v_0 (= (+ _n (* (- 1) _base)) 2))) (let ((?v_2 (___z9z___ ?v_1)) (?v_3 (___z13z___ (+ (- 1) ?v_1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3))))) (___z13z___ ?v_1)))))
(assert (let ((?v_1 (+ _n (- 2)))) (let ((?v_2 (___z10z___ ?v_1)) (?v_0 (= (+ _n (* (- 1) _base)) 2)) (?v_3 (___z14z___ (+ (- 1) ?v_1)))) (= (and (not ?v_0) (or ?v_0 (and (or (<= ?v_2 (- 10)) ?v_3) (or (not (<= 0 ?v_2)) (not ?v_3))))) (___z14z___ ?v_1)))))
(assert (let ((?v_0 (+ _n (- 2)))) (= (___z5z___ ?v_0) (or (not (___z22z___ ?v_0)) (or (= (+ _n (* (- 1) _base)) 2) (___z15z___ (+ (- 1) ?v_0)))))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (or (= (+ _n (* (- 1) _base)) 2) (not (or (and (___z11z___ ?v_0) (___z13z___ ?v_1)) (and (___z11z___ ?v_1) (___z13z___ ?v_0))))) (___z15z___ ?v_0)))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (___z6z___ (+ (- 1) ?v_0)))) (= (___z6z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 2) 0 (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_1)) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 2)))) (= (___z16z___ ?v_0) (and (___z18z___ ?v_0) (___z17z___ ?v_0)))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (___z7z___ (+ (- 1) ?v_0)))) (= (___z7z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 2) 0 (ite (___z3z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z17z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 2) (and (or (not (<= 9 (___z19z___ ?v_1))) (not (___z2z___ ?v_0))) (or (not (___z13z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (___z8z___ (+ (- 1) ?v_0)))) (= (___z8z___ ?v_0) (ite (= (+ _n (* (- 1) _base)) 2) 0 (ite (___z4z___ ?v_0) (+ 1 ?v_1) ?v_1))))))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (+ (- 1) ?v_0))) (= (___z18z___ ?v_0) (or (= (+ _n (* (- 1) _base)) 2) (and (or (not (<= 9 (___z20z___ ?v_1))) (not (___z3z___ ?v_0))) (or (not (___z14z___ ?v_1)) (not (___z4z___ ?v_0)))))))))
(assert (let ((?v_0 (+ _n (- 2)))) (= (+ (___z8z___ ?v_0) (+ (___z9z___ ?v_0) (* (- 1) (___z6z___ ?v_0)))) 0)))
(assert (let ((?v_0 (+ _n (- 2)))) (let ((?v_1 (+ (- 1) ?v_0))) (let ((?v_2 (___z19z___ ?v_1))) (= (ite (= (+ _n (* (- 1) _base)) 2) 0 (ite (and (___z11z___ ?v_1) (___z11z___ ?v_0)) (ite (___z2z___ ?v_0) (+ 1 (+ 1 ?v_2)) ?v_2) 0)) (___z19z___ ?v_0))))))
(assert (not (or (___z5z___ _n) (not (= _base (- 2))))))
(assert true)
(set-info :status unsat)
(check-sat)
(exit)

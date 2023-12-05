(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 14))
(declare-fun v1 () (_ BitVec 9))
(declare-fun v2 () (_ BitVec 12))
(declare-fun v3 () (_ BitVec 8))
(assert (let ((e4(_ bv3 2)))
(let ((e5 ((_ repeat 3) e4)))
(let ((e6 (bvneg v2)))
(let ((e7 (ite (bvsgt ((_ zero_extend 7) e4) v1) (_ bv1 1) (_ bv0 1))))
(let ((e8 (bvxnor e4 ((_ sign_extend 1) e7))))
(let ((e9 (bvadd e5 e5)))
(let ((e10 (bvcomp e8 e4)))
(let ((e11 (bvneg e6)))
(let ((e12 (bvcomp e6 v2)))
(let ((e13 (bvashr e11 ((_ sign_extend 4) v3))))
(let ((e14 (bvashr ((_ zero_extend 2) e13) v0)))
(let ((e15 (bvslt ((_ zero_extend 5) e7) e9)))
(let ((e16 (bvule e14 e14)))
(let ((e17 (bvult e6 ((_ sign_extend 3) v1))))
(let ((e18 (bvslt ((_ sign_extend 12) e4) e14)))
(let ((e19 (bvslt v2 ((_ sign_extend 11) e7))))
(let ((e20 (bvugt ((_ sign_extend 7) e8) v1)))
(let ((e21 (bvult ((_ zero_extend 6) e9) e11)))
(let ((e22 (bvslt ((_ zero_extend 5) v1) e14)))
(let ((e23 (bvuge e12 e12)))
(let ((e24 (bvugt e8 e4)))
(let ((e25 (bvsle ((_ zero_extend 10) e4) e6)))
(let ((e26 (bvult ((_ zero_extend 2) e11) v0)))
(let ((e27 (bvugt v2 v2)))
(let ((e28 (bvuge v3 ((_ zero_extend 6) e4))))
(let ((e29 (bvsgt ((_ zero_extend 4) v3) e6)))
(let ((e30 (distinct ((_ zero_extend 2) e11) e14)))
(let ((e31 (bvuge ((_ zero_extend 6) e5) v2)))
(let ((e32 (bvugt e14 ((_ sign_extend 13) e12))))
(let ((e33 (bvugt ((_ zero_extend 5) e12) e5)))
(let ((e34 (distinct e14 ((_ zero_extend 13) e7))))
(let ((e35 (bvugt e7 e10)))
(let ((e36 (bvule ((_ sign_extend 10) e8) v2)))
(let ((e37 (bvuge ((_ sign_extend 8) e9) e14)))
(let ((e38 (distinct e11 ((_ sign_extend 11) e12))))
(let ((e39 (bvsge ((_ zero_extend 6) e9) v2)))
(let ((e40 (bvsge e14 ((_ zero_extend 6) v3))))
(let ((e41 (bvsle ((_ sign_extend 10) e8) e6)))
(let ((e42 (bvsge ((_ sign_extend 10) e4) e11)))
(let ((e43 (bvsgt v2 ((_ zero_extend 11) e12))))
(let ((e44 (bvugt v3 ((_ zero_extend 2) e9))))
(let ((e45 (bvslt ((_ zero_extend 6) e4) v3)))
(let ((e46 (bvsgt v3 ((_ sign_extend 7) e12))))
(let ((e47 (bvsgt ((_ zero_extend 2) e11) v0)))
(let ((e48 (= v3 v3)))
(let ((e49 (distinct v2 ((_ zero_extend 6) e9))))
(let ((e50 (bvuge e6 ((_ sign_extend 11) e10))))
(let ((e51 (bvsle v0 ((_ zero_extend 2) e13))))
(let ((e52 (or e18 e18)))
(let ((e53 (=> e15 e35)))
(let ((e54 (and e29 e24)))
(let ((e55 (=> e44 e53)))
(let ((e56 (xor e31 e48)))
(let ((e57 (ite e52 e28 e17)))
(let ((e58 (or e57 e26)))
(let ((e59 (ite e45 e25 e46)))
(let ((e60 (xor e40 e47)))
(let ((e61 (or e19 e58)))
(let ((e62 (=> e41 e39)))
(let ((e63 (=> e21 e54)))
(let ((e64 (= e38 e23)))
(let ((e65 (not e16)))
(let ((e66 (ite e65 e56 e36)))
(let ((e67 (not e33)))
(let ((e68 (not e22)))
(let ((e69 (xor e27 e66)))
(let ((e70 (and e64 e63)))
(let ((e71 (ite e69 e55 e68)))
(let ((e72 (=> e67 e43)))
(let ((e73 (=> e59 e30)))
(let ((e74 (ite e60 e62 e51)))
(let ((e75 (=> e32 e74)))
(let ((e76 (ite e20 e61 e71)))
(let ((e77 (=> e73 e76)))
(let ((e78 (xor e72 e50)))
(let ((e79 (xor e42 e37)))
(let ((e80 (and e79 e34)))
(let ((e81 (or e77 e78)))
(let ((e82 (or e49 e70)))
(let ((e83 (and e82 e82)))
(let ((e84 (and e83 e75)))
(let ((e85 (xor e80 e84)))
(let ((e86 (and e81 e81)))
(let ((e87 (not e85)))
(let ((e88 (or e86 e86)))
(let ((e89 (and e87 e87)))
(let ((e90 (=> e88 e88)))
(let ((e91 (xor e89 e89)))
(let ((e92 (xor e91 e90)))
e92
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)

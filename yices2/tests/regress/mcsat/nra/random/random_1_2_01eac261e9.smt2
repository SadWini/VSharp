(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(assert (let ((e2 1))
(let ((e3 1))
(let ((e4 7))
(let ((e5 (- v0 v1)))
(let ((e6 (* e5 v0)))
(let ((e7 (* e6 e5)))
(let ((e8 (/ e2 e3)))
(let ((e9 (* e6 e5)))
(let ((e10 (- v0)))
(let ((e11 (- v0 e10)))
(let ((e12 (* e7 e6)))
(let ((e13 (* e6 e2)))
(let ((e14 (- e12)))
(let ((e15 (* e12 e13)))
(let ((e16 (- e15 e15)))
(let ((e17 (- e15)))
(let ((e18 (* v0 e15)))
(let ((e19 (/ e3 (- e3))))
(let ((e20 (/ e4 e4)))
(let ((e21 (= e12 e12)))
(let ((e22 (= e6 e5)))
(let ((e23 (< e8 e7)))
(let ((e24 (>= e6 e16)))
(let ((e25 (< e11 e10)))
(let ((e26 (distinct e11 v0)))
(let ((e27 (> v0 e19)))
(let ((e28 (<= e18 e10)))
(let ((e29 (> e12 e12)))
(let ((e30 (< e10 e9)))
(let ((e31 (> e10 e17)))
(let ((e32 (<= e13 e8)))
(let ((e33 (= e13 e20)))
(let ((e34 (>= e8 e18)))
(let ((e35 (>= e8 e9)))
(let ((e36 (> e10 e8)))
(let ((e37 (distinct e14 e18)))
(let ((e38 (= e12 e6)))
(let ((e39 (<= e17 e11)))
(let ((e40 (= e6 e11)))
(let ((e41 (<= e11 e10)))
(let ((e42 (distinct v0 e17)))
(let ((e43 (> e13 e17)))
(let ((e44 (< e12 v1)))
(let ((e45 (<= e13 e8)))
(let ((e46 (> e14 v1)))
(let ((e47 (= e8 e19)))
(let ((e48 (< e17 e20)))
(let ((e49 (> e12 e12)))
(let ((e50 (> e14 e16)))
(let ((e51 (>= e7 e5)))
(let ((e52 (= e8 v1)))
(let ((e53 (< e20 e6)))
(let ((e54 (< e15 e19)))
(let ((e55 (>= v1 e20)))
(let ((e56 (distinct e8 v0)))
(let ((e57 (distinct e11 e12)))
(let ((e58 (<= e7 e12)))
(let ((e59 (>= e14 e19)))
(let ((e60 (> e5 e8)))
(let ((e61 (= e5 e8)))
(let ((e62 (> e6 e13)))
(let ((e63 (> e10 e17)))
(let ((e64 (distinct e17 e18)))
(let ((e65 (> e12 e6)))
(let ((e66 (distinct e19 e10)))
(let ((e67 (distinct e11 e13)))
(let ((e68 (> e12 e6)))
(let ((e69 (>= e20 e5)))
(let ((e70 (distinct e7 e11)))
(let ((e71 (< e12 e9)))
(let ((e72 (distinct e7 e18)))
(let ((e73 (> e17 e14)))
(let ((e74 (distinct e15 e5)))
(let ((e75 (= e20 e10)))
(let ((e76 (> e13 e5)))
(let ((e77 (>= v0 e10)))
(let ((e78 (= e15 e16)))
(let ((e79 (=> e69 e33)))
(let ((e80 (ite e46 e74 e63)))
(let ((e81 (= e54 e54)))
(let ((e82 (and e51 e32)))
(let ((e83 (and e25 e56)))
(let ((e84 (=> e79 e65)))
(let ((e85 (ite e81 e36 e38)))
(let ((e86 (not e30)))
(let ((e87 (xor e73 e22)))
(let ((e88 (xor e78 e47)))
(let ((e89 (ite e77 e67 e57)))
(let ((e90 (ite e75 e42 e35)))
(let ((e91 (ite e34 e86 e23)))
(let ((e92 (and e84 e90)))
(let ((e93 (and e41 e55)))
(let ((e94 (= e28 e82)))
(let ((e95 (=> e43 e93)))
(let ((e96 (and e87 e24)))
(let ((e97 (and e26 e66)))
(let ((e98 (= e52 e53)))
(let ((e99 (ite e80 e64 e91)))
(let ((e100 (ite e44 e96 e37)))
(let ((e101 (= e70 e31)))
(let ((e102 (and e48 e83)))
(let ((e103 (and e39 e97)))
(let ((e104 (not e98)))
(let ((e105 (or e102 e103)))
(let ((e106 (ite e29 e62 e88)))
(let ((e107 (=> e95 e71)))
(let ((e108 (and e89 e58)))
(let ((e109 (xor e106 e40)))
(let ((e110 (or e92 e105)))
(let ((e111 (xor e27 e109)))
(let ((e112 (xor e108 e100)))
(let ((e113 (and e68 e68)))
(let ((e114 (and e59 e94)))
(let ((e115 (= e21 e21)))
(let ((e116 (xor e111 e50)))
(let ((e117 (not e61)))
(let ((e118 (xor e99 e107)))
(let ((e119 (and e113 e72)))
(let ((e120 (xor e104 e104)))
(let ((e121 (and e76 e115)))
(let ((e122 (xor e120 e112)))
(let ((e123 (not e117)))
(let ((e124 (or e60 e114)))
(let ((e125 (or e118 e119)))
(let ((e126 (or e101 e45)))
(let ((e127 (= e123 e121)))
(let ((e128 (or e122 e110)))
(let ((e129 (xor e124 e85)))
(let ((e130 (xor e116 e126)))
(let ((e131 (and e129 e49)))
(let ((e132 (or e127 e125)))
(let ((e133 (xor e132 e128)))
(let ((e134 (ite e133 e131 e130)))
e134
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)

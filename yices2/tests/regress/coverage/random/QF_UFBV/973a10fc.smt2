(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UFBV)
(declare-fun f0 ( (_ BitVec 85)) (_ BitVec 121))
(declare-fun p0 ( (_ BitVec 3)) Bool)
(declare-fun v0 () (_ BitVec 27))
(declare-fun v1 () (_ BitVec 1))
(declare-fun v2 () (_ BitVec 50))
(assert (let ((e3(_ bv80753775154701410948151 80)))
(let ((e4 (f0 ((_ zero_extend 35) v2))))
(let ((e5 (ite (p0 ((_ extract 83 81) e4)) (_ bv1 1) (_ bv0 1))))
(let ((e6 ((_ rotate_left 74) e4)))
(let ((e7 (bvneg e5)))
(let ((e8 (ite (bvult ((_ sign_extend 49) e7) v2) (_ bv1 1) (_ bv0 1))))
(let ((e9 ((_ repeat 100) e7)))
(let ((e10 ((_ repeat 1) e3)))
(let ((e11 (bvsub ((_ zero_extend 50) v2) e9)))
(let ((e12 (bvmul e3 ((_ zero_extend 79) e8))))
(let ((e13 (ite (p0 ((_ extract 31 29) e11)) (_ bv1 1) (_ bv0 1))))
(let ((e14 (bvshl e12 ((_ zero_extend 79) e8))))
(let ((e15 (ite (bvult ((_ sign_extend 21) e9) e4) (_ bv1 1) (_ bv0 1))))
(let ((e16 (bvnor ((_ sign_extend 49) e15) v2)))
(let ((e17 (ite (bvsle e11 ((_ zero_extend 99) e5)) (_ bv1 1) (_ bv0 1))))
(let ((e18 (bvsub ((_ zero_extend 120) e7) e6)))
(let ((e19 (bvcomp e18 ((_ zero_extend 21) e11))))
(let ((e20 ((_ repeat 85) e7)))
(let ((e21 ((_ rotate_right 42) e6)))
(let ((e22 (ite (bvsle e19 e17) (_ bv1 1) (_ bv0 1))))
(let ((e23 (f0 ((_ zero_extend 84) v1))))
(let ((e24 (bvsrem ((_ sign_extend 79) e8) e14)))
(let ((e25 (bvsdiv ((_ sign_extend 120) e22) e6)))
(let ((e26 (ite (bvuge ((_ zero_extend 79) e19) e10) (_ bv1 1) (_ bv0 1))))
(let ((e27 (bvcomp ((_ sign_extend 79) v1) e24)))
(let ((e28 (bvudiv e5 e8)))
(let ((e29 (f0 ((_ sign_extend 5) e10))))
(let ((e30 ((_ zero_extend 8) e18)))
(let ((e31 (bvxnor e28 e15)))
(let ((e32 (bvmul ((_ sign_extend 120) e7) e21)))
(let ((e33 (ite (bvuge e12 ((_ zero_extend 79) e15)) (_ bv1 1) (_ bv0 1))))
(let ((e34 (bvnand e4 e21)))
(let ((e35 (bvnor ((_ zero_extend 120) v1) e32)))
(let ((e36 (ite (bvule e13 e7) (_ bv1 1) (_ bv0 1))))
(let ((e37 ((_ rotate_left 0) e28)))
(let ((e38 (bvnot e24)))
(let ((e39 (ite (bvslt e22 e27) (_ bv1 1) (_ bv0 1))))
(let ((e40 (bvmul ((_ sign_extend 30) v2) e14)))
(let ((e41 (bvnot e22)))
(let ((e42 (ite (bvslt ((_ sign_extend 26) e39) v0) (_ bv1 1) (_ bv0 1))))
(let ((e43 (bvsle e18 e35)))
(let ((e44 (p0 ((_ sign_extend 2) e22))))
(let ((e45 (p0 ((_ sign_extend 2) e39))))
(let ((e46 (bvult e19 e15)))
(let ((e47 (bvule e41 e28)))
(let ((e48 (= e35 ((_ zero_extend 120) e28))))
(let ((e49 (bvslt e32 ((_ zero_extend 21) e9))))
(let ((e50 (p0 ((_ sign_extend 2) e27))))
(let ((e51 (p0 ((_ extract 11 9) e4))))
(let ((e52 (bvsle ((_ zero_extend 79) e26) e14)))
(let ((e53 (bvule e22 e42)))
(let ((e54 (= e30 ((_ sign_extend 128) e5))))
(let ((e55 (bvsge e14 ((_ sign_extend 79) e37))))
(let ((e56 (= ((_ zero_extend 99) e7) e9)))
(let ((e57 (bvuge e14 ((_ sign_extend 30) e16))))
(let ((e58 (p0 ((_ extract 17 15) e35))))
(let ((e59 (bvult e42 e13)))
(let ((e60 (bvslt v1 e22)))
(let ((e61 (bvule e24 e10)))
(let ((e62 (= e35 e35)))
(let ((e63 (bvslt e26 e39)))
(let ((e64 (bvule ((_ sign_extend 120) e36) e32)))
(let ((e65 (bvuge e9 ((_ zero_extend 99) e42))))
(let ((e66 (bvsgt e11 ((_ sign_extend 99) e8))))
(let ((e67 (p0 ((_ extract 44 42) e4))))
(let ((e68 (bvugt e9 ((_ zero_extend 99) e33))))
(let ((e69 (bvsle e32 ((_ zero_extend 120) e19))))
(let ((e70 (p0 ((_ extract 47 45) e20))))
(let ((e71 (bvule e33 e26)))
(let ((e72 (bvsgt e27 e5)))
(let ((e73 (bvugt e8 e8)))
(let ((e74 (distinct e39 v1)))
(let ((e75 (bvult ((_ sign_extend 41) e24) e25)))
(let ((e76 (bvsge ((_ sign_extend 41) e12) e34)))
(let ((e77 (p0 ((_ sign_extend 2) e26))))
(let ((e78 (bvsgt e25 ((_ sign_extend 120) e15))))
(let ((e79 (bvsle e25 ((_ zero_extend 41) e38))))
(let ((e80 (p0 ((_ extract 92 90) e9))))
(let ((e81 (bvsge e18 ((_ sign_extend 41) e12))))
(let ((e82 (distinct ((_ sign_extend 120) e41) e29)))
(let ((e83 (bvuge e10 e10)))
(let ((e84 (bvsge e21 e21)))
(let ((e85 (= e21 ((_ zero_extend 21) e9))))
(let ((e86 (p0 ((_ zero_extend 2) e7))))
(let ((e87 (bvugt e29 ((_ sign_extend 120) e42))))
(let ((e88 (p0 ((_ extract 5 3) e21))))
(let ((e89 (= ((_ sign_extend 120) e41) e29)))
(let ((e90 (bvslt e29 ((_ sign_extend 120) e41))))
(let ((e91 (bvsle ((_ zero_extend 84) e17) e20)))
(let ((e92 (bvslt e21 e34)))
(let ((e93 (bvule ((_ sign_extend 99) e7) e11)))
(let ((e94 (bvule ((_ sign_extend 41) e38) e21)))
(let ((e95 (bvuge e9 ((_ zero_extend 99) e22))))
(let ((e96 (= e6 ((_ sign_extend 120) e36))))
(let ((e97 (bvult e39 e28)))
(let ((e98 (bvult ((_ sign_extend 128) e19) e30)))
(let ((e99 (p0 ((_ extract 91 89) e25))))
(let ((e100 (bvule ((_ zero_extend 120) e28) e25)))
(let ((e101 (bvsgt v2 ((_ zero_extend 49) e26))))
(let ((e102 (bvsle e18 ((_ sign_extend 120) e17))))
(let ((e103 (bvsle e8 e19)))
(let ((e104 (bvule e6 ((_ zero_extend 120) e26))))
(let ((e105 (bvult ((_ zero_extend 71) e16) e23)))
(let ((e106 (p0 ((_ extract 26 24) v0))))
(let ((e107 (bvsgt e22 e13)))
(let ((e108 (bvule ((_ zero_extend 79) e33) e12)))
(let ((e109 (bvslt v0 ((_ zero_extend 26) e36))))
(let ((e110 (bvsgt ((_ zero_extend 79) e27) e12)))
(let ((e111 (bvslt e42 e36)))
(let ((e112 (bvslt ((_ zero_extend 120) e13) e34)))
(let ((e113 (= ((_ sign_extend 120) e42) e4)))
(let ((e114 (bvuge e7 e7)))
(let ((e115 (bvslt e31 e37)))
(let ((e116 (bvsge e25 ((_ sign_extend 21) e11))))
(let ((e117 (distinct e10 ((_ sign_extend 79) e13))))
(let ((e118 (p0 ((_ extract 35 33) e21))))
(let ((e119 (bvult ((_ zero_extend 79) e42) e38)))
(let ((e120 (bvult e8 e7)))
(let ((e121 (bvult e17 e28)))
(let ((e122 (bvule ((_ zero_extend 26) e36) v0)))
(let ((e123 (distinct e34 e6)))
(let ((e124 (bvsle e33 e41)))
(let ((e125 (bvule ((_ zero_extend 79) e39) e14)))
(let ((e126 (bvsle e21 ((_ zero_extend 41) e14))))
(let ((e127 (bvsge ((_ sign_extend 128) e22) e30)))
(let ((e128 (bvsle ((_ zero_extend 120) e31) e18)))
(let ((e129 (bvsge ((_ sign_extend 120) e8) e25)))
(let ((e130 (= e7 e41)))
(let ((e131 (bvule ((_ zero_extend 20) e10) e11)))
(let ((e132 (bvsge e33 e33)))
(let ((e133 (bvslt e26 e5)))
(let ((e134 (bvsge e16 ((_ sign_extend 49) e26))))
(let ((e135 (bvsge e35 ((_ sign_extend 120) e28))))
(let ((e136 (bvsge e32 ((_ zero_extend 41) e14))))
(let ((e137 (bvule e12 e24)))
(let ((e138 (bvsle e8 e33)))
(let ((e139 (bvslt e29 e23)))
(let ((e140 (distinct ((_ zero_extend 79) e31) e12)))
(let ((e141 (bvuge e12 e24)))
(let ((e142 (bvslt ((_ zero_extend 79) e37) e14)))
(let ((e143 (bvugt e28 e39)))
(let ((e144 (bvslt e3 e3)))
(let ((e145 (bvsgt e28 e19)))
(let ((e146 (= ((_ zero_extend 120) e26) e23)))
(let ((e147 (bvule ((_ sign_extend 79) e33) e40)))
(let ((e148 (xor e91 e108)))
(let ((e149 (ite e66 e71 e82)))
(let ((e150 (and e49 e67)))
(let ((e151 (not e45)))
(let ((e152 (and e118 e89)))
(let ((e153 (xor e106 e87)))
(let ((e154 (=> e80 e135)))
(let ((e155 (not e110)))
(let ((e156 (= e93 e153)))
(let ((e157 (ite e57 e73 e150)))
(let ((e158 (xor e52 e79)))
(let ((e159 (= e149 e128)))
(let ((e160 (or e138 e61)))
(let ((e161 (or e114 e43)))
(let ((e162 (and e85 e124)))
(let ((e163 (= e103 e88)))
(let ((e164 (not e134)))
(let ((e165 (= e148 e131)))
(let ((e166 (ite e136 e121 e154)))
(let ((e167 (xor e127 e65)))
(let ((e168 (=> e48 e50)))
(let ((e169 (ite e54 e160 e102)))
(let ((e170 (and e144 e56)))
(let ((e171 (xor e115 e76)))
(let ((e172 (or e95 e139)))
(let ((e173 (ite e166 e158 e96)))
(let ((e174 (not e111)))
(let ((e175 (not e147)))
(let ((e176 (and e44 e75)))
(let ((e177 (and e126 e151)))
(let ((e178 (xor e156 e177)))
(let ((e179 (= e178 e90)))
(let ((e180 (not e74)))
(let ((e181 (xor e137 e68)))
(let ((e182 (= e167 e161)))
(let ((e183 (ite e92 e163 e99)))
(let ((e184 (or e60 e107)))
(let ((e185 (and e47 e51)))
(let ((e186 (not e105)))
(let ((e187 (= e142 e59)))
(let ((e188 (not e116)))
(let ((e189 (= e145 e182)))
(let ((e190 (= e122 e162)))
(let ((e191 (and e175 e186)))
(let ((e192 (or e112 e70)))
(let ((e193 (xor e130 e83)))
(let ((e194 (ite e176 e55 e86)))
(let ((e195 (=> e188 e155)))
(let ((e196 (not e109)))
(let ((e197 (and e141 e123)))
(let ((e198 (not e58)))
(let ((e199 (not e117)))
(let ((e200 (and e174 e72)))
(let ((e201 (xor e191 e132)))
(let ((e202 (not e185)))
(let ((e203 (= e165 e98)))
(let ((e204 (ite e64 e104 e159)))
(let ((e205 (and e171 e179)))
(let ((e206 (= e120 e62)))
(let ((e207 (and e197 e199)))
(let ((e208 (=> e190 e81)))
(let ((e209 (not e63)))
(let ((e210 (xor e180 e129)))
(let ((e211 (= e125 e209)))
(let ((e212 (not e152)))
(let ((e213 (ite e210 e97 e113)))
(let ((e214 (=> e157 e84)))
(let ((e215 (or e53 e213)))
(let ((e216 (xor e198 e78)))
(let ((e217 (ite e189 e216 e195)))
(let ((e218 (or e140 e170)))
(let ((e219 (=> e207 e46)))
(let ((e220 (not e168)))
(let ((e221 (or e143 e94)))
(let ((e222 (or e183 e192)))
(let ((e223 (and e196 e184)))
(let ((e224 (ite e172 e119 e69)))
(let ((e225 (=> e223 e218)))
(let ((e226 (ite e187 e212 e164)))
(let ((e227 (xor e201 e206)))
(let ((e228 (or e227 e146)))
(let ((e229 (not e221)))
(let ((e230 (xor e204 e219)))
(let ((e231 (xor e133 e211)))
(let ((e232 (= e225 e100)))
(let ((e233 (= e230 e230)))
(let ((e234 (and e217 e101)))
(let ((e235 (or e215 e173)))
(let ((e236 (ite e205 e200 e233)))
(let ((e237 (xor e235 e203)))
(let ((e238 (not e236)))
(let ((e239 (=> e226 e222)))
(let ((e240 (ite e239 e208 e224)))
(let ((e241 (=> e229 e220)))
(let ((e242 (not e193)))
(let ((e243 (xor e77 e237)))
(let ((e244 (ite e228 e228 e231)))
(let ((e245 (xor e169 e241)))
(let ((e246 (not e214)))
(let ((e247 (not e245)))
(let ((e248 (xor e242 e232)))
(let ((e249 (not e238)))
(let ((e250 (not e202)))
(let ((e251 (ite e247 e249 e181)))
(let ((e252 (xor e234 e246)))
(let ((e253 (= e250 e243)))
(let ((e254 (not e240)))
(let ((e255 (=> e253 e252)))
(let ((e256 (xor e254 e254)))
(let ((e257 (= e194 e256)))
(let ((e258 (and e251 e244)))
(let ((e259 (and e258 e248)))
(let ((e260 (ite e255 e257 e259)))
(let ((e261 (and e260 (not (= e14 (_ bv0 80))))))
(let ((e262 (and e261 (not (= e14 (bvnot (_ bv0 80)))))))
(let ((e263 (and e262 (not (= e6 (_ bv0 121))))))
(let ((e264 (and e263 (not (= e6 (bvnot (_ bv0 121)))))))
(let ((e265 (and e264 (not (= e8 (_ bv0 1))))))
e265
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)

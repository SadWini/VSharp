(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UFBV)
(declare-fun f0 ( (_ BitVec 4) (_ BitVec 10) (_ BitVec 4)) (_ BitVec 2))
(declare-fun p0 ( (_ BitVec 8)) Bool)
(declare-fun p1 ( (_ BitVec 14)) Bool)
(declare-fun v0 () (_ BitVec 3))
(declare-fun v1 () (_ BitVec 8))
(declare-fun v2 () (_ BitVec 14))
(assert (let ((e3(_ bv3 5)))
(let ((e4(_ bv2 3)))
(let ((e5 (! (ite (p1 ((_ zero_extend 6) v1)) (_ bv1 1) (_ bv0 1)) :named term5)))
(let ((e6 (! (bvxor v1 ((_ zero_extend 7) e5)) :named term6)))
(let ((e7 (! (bvurem v0 v0) :named term7)))
(let ((e8 (! (bvor e6 ((_ zero_extend 3) e3)) :named term8)))
(let ((e9 (! (f0 ((_ extract 3 0) e3) ((_ sign_extend 7) v0) ((_ extract 4 1) e3)) :named term9)))
(let ((e10 (! (ite (p0 ((_ zero_extend 7) e5)) (_ bv1 1) (_ bv0 1)) :named term10)))
(let ((e11 (! (ite (distinct ((_ zero_extend 6) v1) v2) (_ bv1 1) (_ bv0 1)) :named term11)))
(let ((e12 (! (bvneg e10) :named term12)))
(let ((e13 (! (bvnot v2) :named term13)))
(let ((e14 (! (bvashr e12 e11) :named term14)))
(let ((e15 (! ((_ rotate_right 5) v1) :named term15)))
(let ((e16 (! (bvmul ((_ zero_extend 5) v0) v1) :named term16)))
(let ((e17 (! (ite (= v1 ((_ sign_extend 7) e11)) (_ bv1 1) (_ bv0 1)) :named term17)))
(let ((e18 (! (concat e12 e15) :named term18)))
(let ((e19 (! (bvand e13 ((_ sign_extend 13) e11)) :named term19)))
(let ((e20 (! (ite (bvslt e13 ((_ sign_extend 6) e8)) (_ bv1 1) (_ bv0 1)) :named term20)))
(let ((e21 (! (bvudiv ((_ sign_extend 7) e14) v1) :named term21)))
(let ((e22 (! (ite (bvsge e16 ((_ zero_extend 7) e11)) (_ bv1 1) (_ bv0 1)) :named term22)))
(let ((e23 (! (bvshl ((_ sign_extend 11) e4) v2) :named term23)))
(let ((e24 (! (p1 ((_ zero_extend 6) e8)) :named term24)))
(let ((e25 (! (p1 ((_ sign_extend 13) e12)) :named term25)))
(let ((e26 (! (bvsge e13 ((_ sign_extend 13) e14)) :named term26)))
(let ((e27 (! (p0 e15) :named term27)))
(let ((e28 (! (bvslt ((_ zero_extend 13) e11) e13) :named term28)))
(let ((e29 (! (bvule v2 ((_ sign_extend 13) e12)) :named term29)))
(let ((e30 (! (bvult ((_ sign_extend 13) e17) e19) :named term30)))
(let ((e31 (! (bvslt v0 e4) :named term31)))
(let ((e32 (! (bvule ((_ zero_extend 7) e10) e15) :named term32)))
(let ((e33 (! (bvuge e17 e11) :named term33)))
(let ((e34 (! (distinct e10 e5) :named term34)))
(let ((e35 (! (bvsle e21 ((_ zero_extend 3) e3)) :named term35)))
(let ((e36 (! (distinct ((_ sign_extend 1) v1) e18) :named term36)))
(let ((e37 (! (bvule e8 ((_ zero_extend 7) e12)) :named term37)))
(let ((e38 (! (bvule e23 ((_ sign_extend 13) e11)) :named term38)))
(let ((e39 (! (bvsle ((_ sign_extend 7) e14) e16) :named term39)))
(let ((e40 (! (bvule e6 ((_ sign_extend 5) e7)) :named term40)))
(let ((e41 (! (bvsgt ((_ sign_extend 13) e17) e19) :named term41)))
(let ((e42 (! (bvuge ((_ sign_extend 7) e10) e8) :named term42)))
(let ((e43 (! (bvslt ((_ zero_extend 2) e10) e7) :named term43)))
(let ((e44 (! (bvule e4 ((_ zero_extend 2) e12)) :named term44)))
(let ((e45 (! (bvule ((_ sign_extend 6) e6) e19) :named term45)))
(let ((e46 (! (bvslt ((_ sign_extend 5) e4) v1) :named term46)))
(let ((e47 (! (distinct ((_ sign_extend 2) e11) e7) :named term47)))
(let ((e48 (! (bvuge e6 ((_ sign_extend 7) e17)) :named term48)))
(let ((e49 (! (p0 e21) :named term49)))
(let ((e50 (! (distinct v1 ((_ zero_extend 5) v0)) :named term50)))
(let ((e51 (! (bvugt e21 ((_ sign_extend 7) e10)) :named term51)))
(let ((e52 (! (bvslt ((_ sign_extend 2) e14) v0) :named term52)))
(let ((e53 (! (bvult e17 e12) :named term53)))
(let ((e54 (! (= ((_ sign_extend 2) v0) e3) :named term54)))
(let ((e55 (! (bvsgt ((_ sign_extend 4) e10) e3) :named term55)))
(let ((e56 (! (bvugt ((_ sign_extend 5) e7) e6) :named term56)))
(let ((e57 (! (bvuge e19 ((_ zero_extend 13) e20)) :named term57)))
(let ((e58 (! (bvsle ((_ zero_extend 7) e5) e8) :named term58)))
(let ((e59 (! (bvsge ((_ zero_extend 3) e3) e6) :named term59)))
(let ((e60 (! (bvsgt e20 e12) :named term60)))
(let ((e61 (! (bvslt ((_ sign_extend 1) e11) e9) :named term61)))
(let ((e62 (! (bvuge e12 e17) :named term62)))
(let ((e63 (! (bvsgt ((_ zero_extend 2) e20) e4) :named term63)))
(let ((e64 (! (= e12 e10) :named term64)))
(let ((e65 (! (distinct e6 ((_ sign_extend 5) e4)) :named term65)))
(let ((e66 (! (= e8 ((_ zero_extend 5) v0)) :named term66)))
(let ((e67 (! (bvule ((_ zero_extend 7) e10) e6) :named term67)))
(let ((e68 (! (bvugt ((_ zero_extend 6) e9) v1) :named term68)))
(let ((e69 (! (distinct e14 e17) :named term69)))
(let ((e70 (! (bvugt v1 v1) :named term70)))
(let ((e71 (! (= ((_ sign_extend 2) e5) e4) :named term71)))
(let ((e72 (! (bvsle e18 ((_ sign_extend 7) e9)) :named term72)))
(let ((e73 (! (p1 ((_ sign_extend 9) e3)) :named term73)))
(let ((e74 (! (p1 ((_ sign_extend 6) e8)) :named term74)))
(let ((e75 (! (bvule e4 v0) :named term75)))
(let ((e76 (! (bvule e8 ((_ sign_extend 5) v0)) :named term76)))
(let ((e77 (! (bvsgt e8 e6) :named term77)))
(let ((e78 (! (distinct ((_ sign_extend 5) v0) e16) :named term78)))
(let ((e79 (! (bvugt e6 v1) :named term79)))
(let ((e80 (! (bvuge ((_ zero_extend 7) e20) e8) :named term80)))
(let ((e81 (! (bvsge e19 e23) :named term81)))
(let ((e82 (! (bvule ((_ zero_extend 7) e5) e15) :named term82)))
(let ((e83 (! (p0 ((_ sign_extend 7) e12)) :named term83)))
(let ((e84 (! (bvult e20 e22) :named term84)))
(let ((e85 (! (or e49 e27) :named term85)))
(let ((e86 (! (xor e75 e26) :named term86)))
(let ((e87 (! (or e56 e85) :named term87)))
(let ((e88 (! (or e73 e28) :named term88)))
(let ((e89 (! (and e86 e86) :named term89)))
(let ((e90 (! (not e51) :named term90)))
(let ((e91 (! (not e64) :named term91)))
(let ((e92 (! (not e87) :named term92)))
(let ((e93 (! (and e35 e55) :named term93)))
(let ((e94 (! (and e92 e33) :named term94)))
(let ((e95 (! (xor e82 e68) :named term95)))
(let ((e96 (! (and e93 e84) :named term96)))
(let ((e97 (! (= e58 e54) :named term97)))
(let ((e98 (! (and e66 e50) :named term98)))
(let ((e99 (! (not e65) :named term99)))
(let ((e100 (! (ite e52 e44 e71) :named term100)))
(let ((e101 (! (not e46) :named term101)))
(let ((e102 (! (xor e70 e95) :named term102)))
(let ((e103 (! (= e94 e96) :named term103)))
(let ((e104 (! (not e40) :named term104)))
(let ((e105 (! (ite e63 e81 e61) :named term105)))
(let ((e106 (! (xor e48 e32) :named term106)))
(let ((e107 (! (=> e37 e101) :named term107)))
(let ((e108 (! (xor e78 e104) :named term108)))
(let ((e109 (! (and e107 e42) :named term109)))
(let ((e110 (! (not e100) :named term110)))
(let ((e111 (! (and e91 e25) :named term111)))
(let ((e112 (! (or e24 e105) :named term112)))
(let ((e113 (! (= e31 e89) :named term113)))
(let ((e114 (! (=> e102 e62) :named term114)))
(let ((e115 (! (ite e36 e39 e111) :named term115)))
(let ((e116 (! (= e47 e72) :named term116)))
(let ((e117 (! (=> e59 e29) :named term117)))
(let ((e118 (! (= e74 e83) :named term118)))
(let ((e119 (! (=> e109 e109) :named term119)))
(let ((e120 (! (xor e118 e97) :named term120)))
(let ((e121 (! (and e112 e103) :named term121)))
(let ((e122 (! (and e41 e115) :named term122)))
(let ((e123 (! (ite e98 e106 e69) :named term123)))
(let ((e124 (! (xor e53 e110) :named term124)))
(let ((e125 (! (=> e77 e57) :named term125)))
(let ((e126 (! (not e125) :named term126)))
(let ((e127 (! (not e60) :named term127)))
(let ((e128 (! (xor e123 e116) :named term128)))
(let ((e129 (! (and e127 e80) :named term129)))
(let ((e130 (! (or e114 e76) :named term130)))
(let ((e131 (! (= e108 e108) :named term131)))
(let ((e132 (! (and e119 e124) :named term132)))
(let ((e133 (! (and e130 e99) :named term133)))
(let ((e134 (! (or e121 e67) :named term134)))
(let ((e135 (! (or e34 e132) :named term135)))
(let ((e136 (! (ite e90 e88 e88) :named term136)))
(let ((e137 (! (not e122) :named term137)))
(let ((e138 (! (and e136 e113) :named term138)))
(let ((e139 (! (and e79 e30) :named term139)))
(let ((e140 (! (xor e131 e129) :named term140)))
(let ((e141 (! (ite e139 e43 e134) :named term141)))
(let ((e142 (! (=> e133 e138) :named term142)))
(let ((e143 (! (ite e117 e142 e38) :named term143)))
(let ((e144 (! (ite e120 e135 e45) :named term144)))
(let ((e145 (! (and e137 e137) :named term145)))
(let ((e146 (! (xor e144 e126) :named term146)))
(let ((e147 (! (xor e145 e141) :named term147)))
(let ((e148 (! (xor e128 e140) :named term148)))
(let ((e149 (! (= e146 e148) :named term149)))
(let ((e150 (! (and e147 e149) :named term150)))
(let ((e151 (! (and e143 e143) :named term151)))
(let ((e152 (! (= e151 e150) :named term152)))
(let ((e153 (! (and e152 (not (= v1 (_ bv0 8)))) :named term153)))
(let ((e154 (! (and e153 (not (= v0 (_ bv0 3)))) :named term154)))
e154
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "/dev/null")
(get-model)
(get-value (term5))
(get-value (term6))
(get-value (term7))
(get-value (term8))
(get-value (term9))
(get-value (term10))
(get-value (term11))
(get-value (term12))
(get-value (term13))
(get-value (term14))
(get-value (term15))
(get-value (term16))
(get-value (term17))
(get-value (term18))
(get-value (term19))
(get-value (term20))
(get-value (term21))
(get-value (term22))
(get-value (term23))
(get-value (term24))
(get-value (term25))
(get-value (term26))
(get-value (term27))
(get-value (term28))
(get-value (term29))
(get-value (term30))
(get-value (term31))
(get-value (term32))
(get-value (term33))
(get-value (term34))
(get-value (term35))
(get-value (term36))
(get-value (term37))
(get-value (term38))
(get-value (term39))
(get-value (term40))
(get-value (term41))
(get-value (term42))
(get-value (term43))
(get-value (term44))
(get-value (term45))
(get-value (term46))
(get-value (term47))
(get-value (term48))
(get-value (term49))
(get-value (term50))
(get-value (term51))
(get-value (term52))
(get-value (term53))
(get-value (term54))
(get-value (term55))
(get-value (term56))
(get-value (term57))
(get-value (term58))
(get-value (term59))
(get-value (term60))
(get-value (term61))
(get-value (term62))
(get-value (term63))
(get-value (term64))
(get-value (term65))
(get-value (term66))
(get-value (term67))
(get-value (term68))
(get-value (term69))
(get-value (term70))
(get-value (term71))
(get-value (term72))
(get-value (term73))
(get-value (term74))
(get-value (term75))
(get-value (term76))
(get-value (term77))
(get-value (term78))
(get-value (term79))
(get-value (term80))
(get-value (term81))
(get-value (term82))
(get-value (term83))
(get-value (term84))
(get-value (term85))
(get-value (term86))
(get-value (term87))
(get-value (term88))
(get-value (term89))
(get-value (term90))
(get-value (term91))
(get-value (term92))
(get-value (term93))
(get-value (term94))
(get-value (term95))
(get-value (term96))
(get-value (term97))
(get-value (term98))
(get-value (term99))
(get-value (term100))
(get-value (term101))
(get-value (term102))
(get-value (term103))
(get-value (term104))
(get-value (term105))
(get-value (term106))
(get-value (term107))
(get-value (term108))
(get-value (term109))
(get-value (term110))
(get-value (term111))
(get-value (term112))
(get-value (term113))
(get-value (term114))
(get-value (term115))
(get-value (term116))
(get-value (term117))
(get-value (term118))
(get-value (term119))
(get-value (term120))
(get-value (term121))
(get-value (term122))
(get-value (term123))
(get-value (term124))
(get-value (term125))
(get-value (term126))
(get-value (term127))
(get-value (term128))
(get-value (term129))
(get-value (term130))
(get-value (term131))
(get-value (term132))
(get-value (term133))
(get-value (term134))
(get-value (term135))
(get-value (term136))
(get-value (term137))
(get-value (term138))
(get-value (term139))
(get-value (term140))
(get-value (term141))
(get-value (term142))
(get-value (term143))
(get-value (term144))
(get-value (term145))
(get-value (term146))
(get-value (term147))
(get-value (term148))
(get-value (term149))
(get-value (term150))
(get-value (term151))
(get-value (term152))
(get-value (term153))
(get-value (term154))
(get-info :all-statistics)

(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UF)
(declare-sort S0 0)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-fun v0 () S0)
(declare-fun v1 () S0)
(declare-fun v2 () S0)
(declare-fun v3 () S1)
(declare-fun v4 () S1)
(declare-fun v5 () S1)
(declare-fun v6 () S2)
(declare-fun v7 () S2)
(declare-fun v8 () S2)
(declare-fun f0 ( S1 S1) S2)
(declare-fun f1 ( S0 S1) S0)
(declare-fun f2 ( S2 S2) S0)
(declare-fun f3 ( S0) S0)
(declare-fun f4 ( S1 S2) S0)
(declare-fun f5 ( S0) S2)
(declare-fun f6 ( S2 S1 S0) S0)
(declare-fun f7 ( S0 S0 S2) S2)
(declare-fun f8 ( S2 S0) S2)
(declare-fun f9 ( S2) S1)
(declare-fun p0 ( S1 S0) Bool)
(declare-fun p1 ( S1) Bool)
(declare-fun p2 ( S2 S2 S2) Bool)
(declare-fun p3 ( S2 S2 S0) Bool)
(declare-fun p4 ( S2 S2 S1) Bool)
(assert (let ((e9 (f0 v5 v3)))
(let ((e10 (! (f2 e9 v7) :named term10)))
(let ((e11 (! (f3 e10) :named term11)))
(let ((e12 (! (f2 v7 e9) :named term12)))
(let ((e13 (! (f2 v6 v6) :named term13)))
(let ((e14 (! (f9 v6) :named term14)))
(let ((e15 (! (f4 v5 e9) :named term15)))
(let ((e16 (! (f4 v3 v8) :named term16)))
(let ((e17 (! (f2 e9 v8) :named term17)))
(let ((e18 (! (f0 v3 v5) :named term18)))
(let ((e19 (! (f3 e10) :named term19)))
(let ((e20 (! (f6 v6 v5 v2) :named term20)))
(let ((e21 (! (f2 v6 v7) :named term21)))
(let ((e22 (! (f6 v8 v3 e19) :named term22)))
(let ((e23 (! (f7 v0 e16 v8) :named term23)))
(let ((e24 (! (f0 v4 v4) :named term24)))
(let ((e25 (! (f6 e18 v5 v1) :named term25)))
(let ((e26 (! (f7 e22 e17 e18) :named term26)))
(let ((e27 (! (f8 v7 e13) :named term27)))
(let ((e28 (! (f3 e25) :named term28)))
(let ((e29 (! (f5 e12) :named term29)))
(let ((e30 (! (f1 e19 e14) :named term30)))
(let ((e31 (! (distinct e13 e22) :named term31)))
(let ((e32 (! (p3 v8 v7 e30) :named term32)))
(let ((e33 (! (distinct e15 e25) :named term33)))
(let ((e34 (! (p0 e14 e12) :named term34)))
(let ((e35 (! (distinct e21 e12) :named term35)))
(let ((e36 (! (= e23 e24) :named term36)))
(let ((e37 (! (= v3 v4) :named term37)))
(let ((e38 (! (p1 v3) :named term38)))
(let ((e39 (! (distinct e18 e18) :named term39)))
(let ((e40 (! (= e27 e9) :named term40)))
(let ((e41 (! (p0 v5 e21) :named term41)))
(let ((e42 (! (= e29 v8) :named term42)))
(let ((e43 (! (distinct e19 v0) :named term43)))
(let ((e44 (! (distinct e20 v0) :named term44)))
(let ((e45 (! (distinct v6 e24) :named term45)))
(let ((e46 (! (= v1 e17) :named term46)))
(let ((e47 (! (distinct e11 e10) :named term47)))
(let ((e48 (! (p1 v4) :named term48)))
(let ((e49 (! (p2 e18 e26 e27) :named term49)))
(let ((e50 (! (= e28 e30) :named term50)))
(let ((e51 (! (p0 v5 e30) :named term51)))
(let ((e52 (! (p0 v3 e15) :named term52)))
(let ((e53 (! (p0 v3 e12) :named term53)))
(let ((e54 (! (= e16 e21) :named term54)))
(let ((e55 (! (= v2 e10) :named term55)))
(let ((e56 (! (p4 e27 e23 v4) :named term56)))
(let ((e57 (! (ite e40 v5 e14) :named term57)))
(let ((e58 (! (ite e51 e13 e22) :named term58)))
(let ((e59 (! (ite e47 e20 v1) :named term59)))
(let ((e60 (! (ite e39 e27 e27) :named term60)))
(let ((e61 (! (ite e37 e23 v7) :named term61)))
(let ((e62 (! (ite e52 e27 e9) :named term62)))
(let ((e63 (! (ite e41 e11 v2) :named term63)))
(let ((e64 (! (ite e56 e18 e60) :named term64)))
(let ((e65 (! (ite e32 e63 e20) :named term65)))
(let ((e66 (! (ite e50 e59 e65) :named term66)))
(let ((e67 (! (ite e56 e21 e17) :named term67)))
(let ((e68 (! (ite e50 e28 v0) :named term68)))
(let ((e69 (! (ite e36 v8 e9) :named term69)))
(let ((e70 (! (ite e48 e10 v1) :named term70)))
(let ((e71 (! (ite e36 v7 v6) :named term71)))
(let ((e72 (! (ite e49 e25 e11) :named term72)))
(let ((e73 (! (ite e34 e24 e60) :named term73)))
(let ((e74 (! (ite e52 e12 e21) :named term74)))
(let ((e75 (! (ite e45 e29 e23) :named term75)))
(let ((e76 (! (ite e40 e26 e29) :named term76)))
(let ((e77 (! (ite e38 e16 e65) :named term77)))
(let ((e78 (! (ite e55 e15 e72) :named term78)))
(let ((e79 (! (ite e54 e66 e11) :named term79)))
(let ((e80 (! (ite e42 v3 e14) :named term80)))
(let ((e81 (! (ite e53 e19 e78) :named term81)))
(let ((e82 (! (ite e56 v4 v3) :named term82)))
(let ((e83 (! (ite e35 e66 e66) :named term83)))
(let ((e84 (! (ite e33 e30 e21) :named term84)))
(let ((e85 (! (ite e49 v5 e80) :named term85)))
(let ((e86 (! (ite e31 e20 e74) :named term86)))
(let ((e87 (! (ite e44 e22 e59) :named term87)))
(let ((e88 (! (ite e56 e72 e84) :named term88)))
(let ((e89 (! (ite e46 v3 v4) :named term89)))
(let ((e90 (! (ite e56 e85 v3) :named term90)))
(let ((e91 (! (ite e42 e77 e12) :named term91)))
(let ((e92 (! (ite e55 e10 v2) :named term92)))
(let ((e93 (! (ite e43 e89 e90) :named term93)))
(let ((e94 (! (p2 e24 v8 e69) :named term94)))
(let ((e95 (! (distinct v2 e28) :named term95)))
(let ((e96 (! (distinct v5 v5) :named term96)))
(let ((e97 (! (= e22 e79) :named term97)))
(let ((e98 (! (= e80 v4) :named term98)))
(let ((e99 (! (distinct e63 e11) :named term99)))
(let ((e100 (! (p3 e27 e76 e87) :named term100)))
(let ((e101 (! (p4 e23 e62 e85) :named term101)))
(let ((e102 (! (p4 e24 e27 e89) :named term102)))
(let ((e103 (! (p0 e57 e19) :named term103)))
(let ((e104 (! (= e60 e71) :named term104)))
(let ((e105 (! (p0 e82 e21) :named term105)))
(let ((e106 (! (= e13 e10) :named term106)))
(let ((e107 (! (= e91 e74) :named term107)))
(let ((e108 (! (p4 e27 v8 e14) :named term108)))
(let ((e109 (! (p1 v3) :named term109)))
(let ((e110 (! (= e58 e13) :named term110)))
(let ((e111 (! (distinct e67 v2) :named term111)))
(let ((e112 (! (distinct e84 e15) :named term112)))
(let ((e113 (! (distinct e20 e66) :named term113)))
(let ((e114 (! (= e59 e16) :named term114)))
(let ((e115 (! (= e93 e93) :named term115)))
(let ((e116 (! (distinct e70 e13) :named term116)))
(let ((e117 (! (p4 e64 v6 e89) :named term117)))
(let ((e118 (! (distinct e90 e14) :named term118)))
(let ((e119 (! (= e65 e83) :named term119)))
(let ((e120 (! (distinct e17 e22) :named term120)))
(let ((e121 (! (= e18 e62) :named term121)))
(let ((e122 (! (p4 e26 e23 v4) :named term122)))
(let ((e123 (! (p3 e62 e62 e58) :named term123)))
(let ((e124 (! (distinct e12 e74) :named term124)))
(let ((e125 (! (p4 e27 e24 v4) :named term125)))
(let ((e126 (! (p0 v3 e15) :named term126)))
(let ((e127 (! (distinct v0 v2) :named term127)))
(let ((e128 (! (= e86 e15) :named term128)))
(let ((e129 (! (distinct e77 e92) :named term129)))
(let ((e130 (! (p0 e93 e25) :named term130)))
(let ((e131 (! (p4 e71 v6 e82) :named term131)))
(let ((e132 (! (distinct e78 e67) :named term132)))
(let ((e133 (! (distinct e30 e16) :named term133)))
(let ((e134 (! (distinct e72 e79) :named term134)))
(let ((e135 (! (p0 e85 e12) :named term135)))
(let ((e136 (! (p3 e26 v6 e13) :named term136)))
(let ((e137 (! (p3 e29 e18 e78) :named term137)))
(let ((e138 (! (= e75 e23) :named term138)))
(let ((e139 (! (p4 e75 e24 e82) :named term139)))
(let ((e140 (! (= v1 e21) :named term140)))
(let ((e141 (! (p1 e80) :named term141)))
(let ((e142 (! (= e68 e92) :named term142)))
(let ((e143 (! (p3 e64 v6 e78) :named term143)))
(let ((e144 (! (p4 e18 e64 v3) :named term144)))
(let ((e145 (! (= e81 e77) :named term145)))
(let ((e146 (! (p1 e90) :named term146)))
(let ((e147 (! (distinct e9 e29) :named term147)))
(let ((e148 (! (p3 e60 e64 e72) :named term148)))
(let ((e149 (! (distinct v7 e61) :named term149)))
(let ((e150 (! (= e88 e86) :named term150)))
(let ((e151 (! (p1 e80) :named term151)))
(let ((e152 (! (distinct e73 e64) :named term152)))
(let ((e153 (! (xor e152 e47) :named term153)))
(let ((e154 (! (and e144 e112) :named term154)))
(let ((e155 (! (= e114 e102) :named term155)))
(let ((e156 (! (not e111) :named term156)))
(let ((e157 (! (or e98 e104) :named term157)))
(let ((e158 (! (and e110 e94) :named term158)))
(let ((e159 (! (=> e141 e96) :named term159)))
(let ((e160 (! (xor e148 e36) :named term160)))
(let ((e161 (! (ite e105 e101 e134) :named term161)))
(let ((e162 (! (or e55 e146) :named term162)))
(let ((e163 (! (= e109 e135) :named term163)))
(let ((e164 (! (not e126) :named term164)))
(let ((e165 (! (= e45 e35) :named term165)))
(let ((e166 (! (=> e34 e121) :named term166)))
(let ((e167 (! (not e50) :named term167)))
(let ((e168 (! (or e56 e125) :named term168)))
(let ((e169 (! (not e164) :named term169)))
(let ((e170 (! (not e116) :named term170)))
(let ((e171 (! (or e53 e44) :named term171)))
(let ((e172 (! (xor e157 e149) :named term172)))
(let ((e173 (! (not e153) :named term173)))
(let ((e174 (! (=> e99 e52) :named term174)))
(let ((e175 (! (= e108 e40) :named term175)))
(let ((e176 (! (and e142 e33) :named term176)))
(let ((e177 (! (and e145 e158) :named term177)))
(let ((e178 (! (ite e139 e174 e122) :named term178)))
(let ((e179 (! (or e51 e151) :named term179)))
(let ((e180 (! (ite e127 e163 e118) :named term180)))
(let ((e181 (! (xor e150 e38) :named term181)))
(let ((e182 (! (xor e133 e167) :named term182)))
(let ((e183 (! (and e119 e176) :named term183)))
(let ((e184 (! (xor e182 e179) :named term184)))
(let ((e185 (! (not e123) :named term185)))
(let ((e186 (! (ite e31 e171 e124) :named term186)))
(let ((e187 (! (not e54) :named term187)))
(let ((e188 (! (not e137) :named term188)))
(let ((e189 (! (ite e188 e43 e129) :named term189)))
(let ((e190 (! (ite e39 e115 e184) :named term190)))
(let ((e191 (! (ite e177 e173 e107) :named term191)))
(let ((e192 (! (ite e147 e97 e180) :named term192)))
(let ((e193 (! (= e103 e181) :named term193)))
(let ((e194 (! (= e172 e138) :named term194)))
(let ((e195 (! (ite e159 e168 e175) :named term195)))
(let ((e196 (! (or e161 e49) :named term196)))
(let ((e197 (! (ite e162 e185 e178) :named term197)))
(let ((e198 (! (=> e186 e166) :named term198)))
(let ((e199 (! (=> e169 e37) :named term199)))
(let ((e200 (! (and e42 e194) :named term200)))
(let ((e201 (! (or e46 e195) :named term201)))
(let ((e202 (! (and e198 e201) :named term202)))
(let ((e203 (! (ite e140 e136 e140) :named term203)))
(let ((e204 (! (=> e170 e41) :named term204)))
(let ((e205 (! (=> e48 e192) :named term205)))
(let ((e206 (! (ite e193 e160 e155) :named term206)))
(let ((e207 (! (ite e100 e95 e143) :named term207)))
(let ((e208 (! (ite e205 e196 e120) :named term208)))
(let ((e209 (! (=> e197 e189) :named term209)))
(let ((e210 (! (= e190 e117) :named term210)))
(let ((e211 (! (xor e191 e204) :named term211)))
(let ((e212 (! (and e187 e207) :named term212)))
(let ((e213 (! (= e130 e211) :named term213)))
(let ((e214 (! (= e203 e210) :named term214)))
(let ((e215 (! (not e113) :named term215)))
(let ((e216 (! (ite e165 e202 e128) :named term216)))
(let ((e217 (! (= e216 e200) :named term217)))
(let ((e218 (! (and e206 e131) :named term218)))
(let ((e219 (! (=> e209 e106) :named term219)))
(let ((e220 (! (or e132 e213) :named term220)))
(let ((e221 (! (and e219 e214) :named term221)))
(let ((e222 (! (xor e217 e220) :named term222)))
(let ((e223 (! (=> e156 e221) :named term223)))
(let ((e224 (! (or e218 e212) :named term224)))
(let ((e225 (! (and e208 e199) :named term225)))
(let ((e226 (! (ite e222 e222 e225) :named term226)))
(let ((e227 (! (xor e32 e223) :named term227)))
(let ((e228 (! (xor e224 e154) :named term228)))
(let ((e229 (! (= e227 e226) :named term229)))
(let ((e230 (! (not e215) :named term230)))
(let ((e231 (! (and e183 e228) :named term231)))
(let ((e232 (! (= e229 e229) :named term232)))
(let ((e233 (! (and e232 e230) :named term233)))
(let ((e234 (! (not e233) :named term234)))
(let ((e235 (! (not e234) :named term235)))
(let ((e236 (! (and e231 e231) :named term236)))
(let ((e237 (! (and e236 e235) :named term237)))
e237
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "/dev/null")
(get-model)
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
(get-value (term155))
(get-value (term156))
(get-value (term157))
(get-value (term158))
(get-value (term159))
(get-value (term160))
(get-value (term161))
(get-value (term162))
(get-value (term163))
(get-value (term164))
(get-value (term165))
(get-value (term166))
(get-value (term167))
(get-value (term168))
(get-value (term169))
(get-value (term170))
(get-value (term171))
(get-value (term172))
(get-value (term173))
(get-value (term174))
(get-value (term175))
(get-value (term176))
(get-value (term177))
(get-value (term178))
(get-value (term179))
(get-value (term180))
(get-value (term181))
(get-value (term182))
(get-value (term183))
(get-value (term184))
(get-value (term185))
(get-value (term186))
(get-value (term187))
(get-value (term188))
(get-value (term189))
(get-value (term190))
(get-value (term191))
(get-value (term192))
(get-value (term193))
(get-value (term194))
(get-value (term195))
(get-value (term196))
(get-value (term197))
(get-value (term198))
(get-value (term199))
(get-value (term200))
(get-value (term201))
(get-value (term202))
(get-value (term203))
(get-value (term204))
(get-value (term205))
(get-value (term206))
(get-value (term207))
(get-value (term208))
(get-value (term209))
(get-value (term210))
(get-value (term211))
(get-value (term212))
(get-value (term213))
(get-value (term214))
(get-value (term215))
(get-value (term216))
(get-value (term217))
(get-value (term218))
(get-value (term219))
(get-value (term220))
(get-value (term221))
(get-value (term222))
(get-value (term223))
(get-value (term224))
(get-value (term225))
(get-value (term226))
(get-value (term227))
(get-value (term228))
(get-value (term229))
(get-value (term230))
(get-value (term231))
(get-value (term232))
(get-value (term233))
(get-value (term234))
(get-value (term235))
(get-value (term236))
(get-value (term237))
(get-info :all-statistics)

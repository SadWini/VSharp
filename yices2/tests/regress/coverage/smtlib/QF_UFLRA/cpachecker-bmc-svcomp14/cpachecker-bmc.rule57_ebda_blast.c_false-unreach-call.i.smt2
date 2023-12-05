(set-logic QF_UFLRA)
(set-info :source |CPAchecker with bounded model checking on SV-COMP14 program using MathSAT5, submitted by Philipp Wendler, http://cpachecker.sosy-lab.org|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")


(declare-fun |ebda_rsrc_controller::hp_slot_ptr@3| () Real)
(declare-fun kzalloc@3 () Real)
(declare-fun |ibmphp_init_devno::__retval__@2| () Real)
(declare-fun |__ADDRESS_OF_ibmphp_find_same_bus_num::__CPAchecker_TMP_0| () Real)
(declare-fun |__ADDRESS_OF_fillslotinfo::__CPAchecker_TMP_0| () Real)
(declare-fun __BASE_ADDRESS_OF__ (Real) Real)
(declare-fun __ADDRESS_OF_used_tmp_slot () Real)
(declare-fun |__ADDRESS_OF___VERIFIER_successful_zalloc_*void#1| () Real)
(declare-fun |ibmphp_init_devno::__CPAchecker_TMP_0@1| () Real)
(declare-fun |kzalloc#2| () Real)
(declare-fun |ebda_rsrc_controller::__retval__@2| () Real)
(declare-fun |ibmphp_find_same_bus_num::__CPAchecker_TMP_0@3| () Real)
(declare-fun |fillslotinfo::__CPAchecker_TMP_0@3| () Real)
(declare-fun |__ADDRESS_OF___VERIFIER_fake_alloc*(void)[0]#2| () Real)
(declare-fun |__ADDRESS_OF_ebda_rsrc_controller::bus_info_ptr1| () Real)
(declare-fun |__ADDRESS_OF_ebda_rsrc_controller::hp_slot_ptr| () Real)
(declare-fun |*(struct_slot)*@1| (Real) Real)
(declare-fun __ADDRESS_OF_freed_tmp_slot () Real)
(declare-fun |ibmphp_find_same_bus_num::__retval__@1| () Real)
(declare-fun |fillslotinfo::__retval__@2| () Real)
(declare-fun |ebda_rsrc_controller::rc@4| () Real)
(declare-fun kzalloc@2 () Real)
(declare-fun used_tmp_slot@3 () Real)
(declare-fun |ebda_rsrc_controller::bus_info_ptr1@4| () Real)
(declare-fun |kfree::p@1| () Real)
(declare-fun |ibmphp_init_devno::__retval__@1| () Real)
(declare-fun |ebda_rsrc_controller::bus_info_ptr1@2| () Real)
(declare-fun |__ADDRESS_OF___VERIFIER_successful_zalloc_*void#0| () Real)
(declare-fun |ebda_rsrc_controller::bus_info_ptr1@3| () Real)
(declare-fun |__ADDRESS_OF_ebda_rsrc_controller::rc| () Real)
(declare-fun |__ADDRESS_OF_ibmphp_init_devno::__CPAchecker_TMP_0| () Real)
(declare-fun |__ADDRESS_OF___VERIFIER_fake_alloc*(void)[0]#3| () Real)
(declare-fun |kfree::p@2| () Real)
(declare-fun freed_tmp_slot@3 () Real)
(declare-fun |fillslotinfo::__CPAchecker_TMP_0@1| () Real)
(declare-fun tmp_slot@2 () Real)
(declare-fun __ADDRESS_OF_tmp_slot () Real)
(declare-fun |ebda_rsrc_controller::rc@3| () Real)
(declare-fun |*(struct_slot)*@2| (Real) Real)
(declare-fun freed_tmp_slot@4 () Real)
(declare-fun |ibmphp_find_same_bus_num::__CPAchecker_TMP_0@1| () Real)
(declare-fun freed_tmp_slot@2 () Real)
(declare-fun used_tmp_slot@4 () Real)
(declare-fun used_tmp_slot@2 () Real)
(declare-fun |ibmphp_find_same_bus_num::__retval__@2| () Real)
(declare-fun |ibmphp_init_devno::__CPAchecker_TMP_0@3| () Real)
(declare-fun |kzalloc#3| () Real)
(declare-fun tmp_slot@3 () Real)
(declare-fun |fillslotinfo::__retval__@1| () Real)
(define-fun _7 () Real 0)
(define-fun _8 () Real __ADDRESS_OF_tmp_slot)
(define-fun _9 () Real (__BASE_ADDRESS_OF__ _8))
(define-fun _10 () Bool (= _8 _9))
(define-fun _11 () Real tmp_slot@2)
(define-fun _12 () Bool (= _11 _7))
(define-fun _13 () Bool (and _10 _12))
(define-fun _14 () Real __ADDRESS_OF_used_tmp_slot)
(define-fun _15 () Real (__BASE_ADDRESS_OF__ _14))
(define-fun _16 () Bool (= _14 _15))
(define-fun _17 () Real used_tmp_slot@2)
(define-fun _18 () Bool (= _17 _7))
(define-fun _19 () Bool (and _16 _18))
(define-fun _20 () Bool (and _13 _19))
(define-fun _21 () Real __ADDRESS_OF_freed_tmp_slot)
(define-fun _22 () Real (__BASE_ADDRESS_OF__ _21))
(define-fun _23 () Bool (= _21 _22))
(define-fun _24 () Real 1)
(define-fun _25 () Real freed_tmp_slot@2)
(define-fun _26 () Bool (= _25 _24))
(define-fun _27 () Bool (and _23 _26))
(define-fun _28 () Bool (and _20 _27))
(define-fun _29 () Real |__ADDRESS_OF_ebda_rsrc_controller::hp_slot_ptr|)
(define-fun _30 () Real (__BASE_ADDRESS_OF__ _29))
(define-fun _31 () Bool (= _29 _30))
(define-fun _32 () Bool (<= _29 _7))
(define-fun _33 () Bool (not _32))
(define-fun _34 () Bool (and _31 _33))
(define-fun _35 () Bool (and _28 _34))
(define-fun _36 () Real |__ADDRESS_OF_ebda_rsrc_controller::bus_info_ptr1|)
(define-fun _37 () Real (__BASE_ADDRESS_OF__ _36))
(define-fun _38 () Bool (= _36 _37))
(define-fun _39 () Bool (and _35 _38))
(define-fun _40 () Real |__ADDRESS_OF_ebda_rsrc_controller::rc|)
(define-fun _41 () Real (__BASE_ADDRESS_OF__ _40))
(define-fun _42 () Bool (= _40 _41))
(define-fun _43 () Bool (and _39 _42))
(define-fun _44 () Real |kzalloc#2|)
(define-fun _45 () Bool (= _44 _7))
(define-fun _46 () Bool (not _45))
(define-fun _47 () Real |__ADDRESS_OF___VERIFIER_successful_zalloc_*void#0|)
(define-fun _48 () Real (ite _46 _47 _7))
(define-fun _49 () Real (|*(struct_slot)*@1| _47))
(define-fun _50 () Bool (= _49 _7))
(define-fun _53 () Real (- 4))
(define-fun _54 () Bool (<= _29 _53))
(define-fun _55 () Bool (not _54))
(define-fun _56 () Real (- 1))
(define-fun _57 () Real (* (- 1) _47))
(define-fun _58 () Real (+ _29 _57))
(define-fun _59 () Bool (<= _58 _53))
(define-fun _60 () Bool (and _55 _59))
(define-fun _61 () Real |ebda_rsrc_controller::hp_slot_ptr@3|)
(define-fun _62 () Bool (= _48 _61))
(define-fun _63 () Bool (and _50 _60))
(define-fun _64 () Bool (and _62 _63))
(define-fun _65 () Bool (and _43 _64))
(define-fun _66 () Bool (= _61 _7))
(define-fun _68 () Bool (and _65 _66))
(define-fun _69 () Bool (not _66))
(define-fun _70 () Bool (and _65 _69))
(define-fun _71 () Real |kzalloc#3|)
(define-fun _72 () Bool (= _71 _7))
(define-fun _73 () Bool (not _72))
(define-fun _74 () Real |__ADDRESS_OF___VERIFIER_successful_zalloc_*void#1|)
(define-fun _75 () Real (ite _73 _74 _7))
(define-fun _78 () Real (- 8))
(define-fun _79 () Bool (<= _47 _78))
(define-fun _80 () Bool (not _79))
(define-fun _81 () Real (* (- 1) _74))
(define-fun _82 () Real (+ _47 _81))
(define-fun _83 () Bool (<= _82 _78))
(define-fun _84 () Bool (and _80 _83))
(define-fun _85 () Real tmp_slot@3)
(define-fun _86 () Bool (= _75 _85))
(define-fun _87 () Bool (and _84 _86))
(define-fun _88 () Bool (and _70 _87))
(define-fun _89 () Bool (= _85 _7))
(define-fun _91 () Bool (and _88 _89))
(define-fun _92 () Bool (not _89))
(define-fun _93 () Bool (and _88 _92))
(define-fun _94 () Real used_tmp_slot@3)
(define-fun _95 () Bool (= _94 _7))
(define-fun _96 () Bool (and _93 _95))
(define-fun _97 () Real freed_tmp_slot@3)
(define-fun _98 () Bool (= _97 _7))
(define-fun _99 () Bool (and _96 _98))
(define-fun _100 () Real |__ADDRESS_OF_ibmphp_find_same_bus_num::__CPAchecker_TMP_0|)
(define-fun _101 () Real (__BASE_ADDRESS_OF__ _100))
(define-fun _102 () Bool (= _100 _101))
(define-fun _103 () Bool (and _99 _102))
(define-fun _104 () Real |ibmphp_find_same_bus_num::__CPAchecker_TMP_0@3|)
(define-fun _105 () Real |ibmphp_find_same_bus_num::__retval__@2|)
(define-fun _106 () Bool (= _104 _105))
(define-fun _107 () Bool (and _103 _106))
(define-fun _108 () Real |ebda_rsrc_controller::bus_info_ptr1@3|)
(define-fun _109 () Bool (= _105 _108))
(define-fun _110 () Bool (and _107 _109))
(define-fun _111 () Bool (= _108 _7))
(define-fun _113 () Bool (and _110 _111))
(define-fun _114 () Bool (not _111))
(define-fun _115 () Bool (and _110 _114))
(define-fun _116 () Real |ebda_rsrc_controller::bus_info_ptr1@4|)
(define-fun _117 () Bool (= _116 _7))
(define-fun _118 () Bool (and _115 _117))
(define-fun _119 () Real (|*(struct_slot)*@2| _61))
(define-fun _120 () Bool (= _85 _119))
(define-fun _121 () Bool (= _47 _61))
(define-fun _122 () Real (|*(struct_slot)*@2| _47))
(define-fun _123 () Bool (= _49 _122))
(define-fun _124 () Bool (or _121 _123))
(define-fun _125 () Bool (and _120 _124))
(define-fun _126 () Bool (and _118 _125))
(define-fun _127 () Real used_tmp_slot@4)
(define-fun _128 () Bool (= _127 _24))
(define-fun _129 () Bool (and _126 _128))
(define-fun _130 () Real |__ADDRESS_OF_fillslotinfo::__CPAchecker_TMP_0|)
(define-fun _131 () Real (__BASE_ADDRESS_OF__ _130))
(define-fun _132 () Bool (= _130 _131))
(define-fun _133 () Bool (and _129 _132))
(define-fun _134 () Real |fillslotinfo::__CPAchecker_TMP_0@3|)
(define-fun _135 () Real |fillslotinfo::__retval__@2|)
(define-fun _136 () Bool (= _134 _135))
(define-fun _137 () Bool (and _133 _136))
(define-fun _138 () Real |ebda_rsrc_controller::rc@3|)
(define-fun _139 () Bool (= _135 _138))
(define-fun _140 () Bool (and _137 _139))
(define-fun _141 () Bool (= _138 _7))
(define-fun _143 () Bool (and _140 _141))
(define-fun _144 () Bool (not _141))
(define-fun _145 () Bool (and _140 _144))
(define-fun _146 () Real |__ADDRESS_OF_ibmphp_init_devno::__CPAchecker_TMP_0|)
(define-fun _147 () Real (__BASE_ADDRESS_OF__ _146))
(define-fun _148 () Bool (= _146 _147))
(define-fun _149 () Bool (and _143 _148))
(define-fun _150 () Real |ibmphp_init_devno::__CPAchecker_TMP_0@3|)
(define-fun _151 () Real |ibmphp_init_devno::__retval__@2|)
(define-fun _152 () Bool (= _150 _151))
(define-fun _153 () Bool (and _149 _152))
(define-fun _154 () Real |ebda_rsrc_controller::rc@4|)
(define-fun _155 () Bool (= _151 _154))
(define-fun _156 () Bool (and _153 _155))
(define-fun _157 () Bool (= _154 _7))
(define-fun _159 () Bool (and _156 _157))
(define-fun _160 () Bool (not _157))
(define-fun _161 () Bool (and _156 _160))
(define-fun _162 () Bool (= _138 _154))
(define-fun _163 () Real |ibmphp_init_devno::__CPAchecker_TMP_0@1|)
(define-fun _164 () Bool (= _150 _163))
(define-fun _165 () Bool (and _162 _164))
(define-fun _166 () Real |ibmphp_init_devno::__retval__@1|)
(define-fun _167 () Bool (= _151 _166))
(define-fun _168 () Bool (and _165 _167))
(define-fun _169 () Bool (and _145 _168))
(define-fun _170 () Bool (or _161 _169))
(define-fun _171 () Real |ebda_rsrc_controller::__retval__@2|)
(define-fun _172 () Bool (= _171 _7))
(define-fun _173 () Bool (and _159 _172))
(define-fun _174 () Real (- 3))
(define-fun _175 () Bool (= _138 _174))
(define-fun _176 () Bool (and _113 _175))
(define-fun _177 () Bool (= _108 _116))
(define-fun _178 () Bool (and _123 _177))
(define-fun _179 () Bool (and _162 _178))
(define-fun _180 () Real |fillslotinfo::__CPAchecker_TMP_0@1|)
(define-fun _181 () Bool (= _134 _180))
(define-fun _182 () Bool (and _179 _181))
(define-fun _183 () Real |fillslotinfo::__retval__@1|)
(define-fun _184 () Bool (= _135 _183))
(define-fun _185 () Bool (and _182 _184))
(define-fun _186 () Bool (and _164 _185))
(define-fun _187 () Bool (and _167 _186))
(define-fun _188 () Bool (= _94 _127))
(define-fun _189 () Bool (and _187 _188))
(define-fun _190 () Bool (and _176 _189))
(define-fun _191 () Bool (or _170 _190))
(define-fun _192 () Real |kfree::p@2|)
(define-fun _193 () Bool (= _119 _192))
(define-fun _194 () Bool (and _191 _193))
(define-fun _195 () Bool (= _192 _7))
(define-fun _196 () Bool (not _195))
(define-fun _198 () Bool (and _194 _196))
(define-fun _199 () Bool (and _194 _195))
(define-fun _200 () Bool (= _85 _192))
(define-fun _202 () Bool (and _198 _200))
(define-fun _203 () Bool (not _200))
(define-fun _204 () Bool (and _198 _203))
(define-fun _205 () Bool (or _199 _204))
(define-fun _206 () Real freed_tmp_slot@4)
(define-fun _207 () Bool (= _206 _24))
(define-fun _208 () Bool (and _202 _207))
(define-fun _209 () Bool (= _97 _206))
(define-fun _210 () Bool (and _205 _209))
(define-fun _211 () Bool (or _208 _210))
(define-fun _212 () Real (- 2))
(define-fun _213 () Bool (= _138 _212))
(define-fun _214 () Bool (and _91 _213))
(define-fun _215 () Real |ebda_rsrc_controller::bus_info_ptr1@2|)
(define-fun _216 () Bool (= _116 _215))
(define-fun _217 () Bool (and _123 _216))
(define-fun _218 () Bool (and _162 _217))
(define-fun _219 () Bool (and _181 _218))
(define-fun _220 () Bool (and _184 _219))
(define-fun _221 () Bool (= _25 _206))
(define-fun _222 () Bool (and _220 _221))
(define-fun _223 () Real |ibmphp_find_same_bus_num::__CPAchecker_TMP_0@1|)
(define-fun _224 () Bool (= _104 _223))
(define-fun _225 () Bool (and _222 _224))
(define-fun _226 () Real |ibmphp_find_same_bus_num::__retval__@1|)
(define-fun _227 () Bool (= _105 _226))
(define-fun _228 () Bool (and _225 _227))
(define-fun _229 () Bool (and _164 _228))
(define-fun _230 () Bool (and _167 _229))
(define-fun _231 () Real |kfree::p@1|)
(define-fun _232 () Bool (= _192 _231))
(define-fun _233 () Bool (and _230 _232))
(define-fun _234 () Bool (= _17 _127))
(define-fun _235 () Bool (and _233 _234))
(define-fun _236 () Bool (and _214 _235))
(define-fun _237 () Bool (or _211 _236))
(define-fun _238 () Bool (and _68 _213))
(define-fun _239 () Real kzalloc@2)
(define-fun _240 () Real kzalloc@3)
(define-fun _241 () Bool (= _239 _240))
(define-fun _242 () Bool (and _233 _241))
(define-fun _243 () Bool (= _11 _85))
(define-fun _244 () Bool (and _242 _243))
(define-fun _245 () Bool (and _234 _244))
(define-fun _246 () Real |__ADDRESS_OF___VERIFIER_fake_alloc*(void)[0]#2|)
(define-fun _247 () Real (* (- 1) _246))
(define-fun _248 () Real (+ _47 _247))
(define-fun _249 () Bool (<= _248 _78))
(define-fun _250 () Bool (and _80 _249))
(define-fun _253 () Real (- 16))
(define-fun _254 () Bool (<= _74 _253))
(define-fun _255 () Bool (not _254))
(define-fun _256 () Real (+ _74 _247))
(define-fun _257 () Bool (<= _256 _253))
(define-fun _258 () Bool (and _255 _257))
(define-fun _259 () Bool (and _250 _258))
(define-fun _260 () Bool (and _238 _245))
(define-fun _261 () Bool (or _237 _260))
(define-fun _262 () Bool (and _259 _261))
(define-fun _263 () Bool (= _154 _171))
(define-fun _264 () Bool (and _262 _263))
(define-fun _265 () Bool (and _209 _232))
(define-fun _266 () Real |__ADDRESS_OF___VERIFIER_fake_alloc*(void)[0]#3|)
(define-fun _267 () Bool (<= _246 _7))
(define-fun _268 () Bool (not _267))
(define-fun _269 () Bool (<= _246 _266))
(define-fun _270 () Bool (and _268 _269))
(define-fun _271 () Real (* (- 1) _266))
(define-fun _272 () Real (+ _74 _271))
(define-fun _273 () Bool (<= _272 _253))
(define-fun _274 () Bool (and _255 _273))
(define-fun _275 () Bool (and _270 _274))
(define-fun _276 () Bool (and _173 _265))
(define-fun _277 () Bool (or _264 _276))
(define-fun _278 () Bool (and _275 _277))
(define-fun _279 () Bool (= _127 _7))
(define-fun _281 () Bool (and _278 _279))
(define-fun _284 () Bool (= _206 _7))
(define-fun _286 () Bool (and _281 _284))
(declare-fun __ART__57@0 () Bool)
(declare-fun __ART__78@0 () Bool)
(declare-fun __ART__79@0 () Bool)
(declare-fun __ART__99@0 () Bool)
(declare-fun __ART__100@0 () Bool)
(declare-fun __ART__27@0 () Bool)
(declare-fun __ART__31@0 () Bool)
(declare-fun __ART__43@0 () Bool)
(declare-fun __ART__67@0 () Bool)
(define-fun _365 () Bool __ART__27@0)
(define-fun _366 () Bool (= _66 _365))
(define-fun _367 () Bool __ART__31@0)
(define-fun _368 () Bool (= _89 _367))
(define-fun _369 () Bool (and _366 _368))
(define-fun _370 () Bool __ART__43@0)
(define-fun _371 () Bool (= _111 _370))
(define-fun _372 () Bool (and _369 _371))
(define-fun _373 () Bool __ART__57@0)
(define-fun _374 () Bool (= _141 _373))
(define-fun _375 () Bool (and _372 _374))
(define-fun _376 () Bool __ART__67@0)
(define-fun _377 () Bool (= _157 _376))
(define-fun _378 () Bool (and _375 _377))
(define-fun _379 () Bool __ART__78@0)
(define-fun _380 () Bool (= _196 _379))
(define-fun _381 () Bool (and _378 _380))
(define-fun _382 () Bool __ART__79@0)
(define-fun _383 () Bool (= _200 _382))
(define-fun _384 () Bool (and _381 _383))
(define-fun _385 () Bool __ART__99@0)
(define-fun _386 () Bool (= _279 _385))
(define-fun _387 () Bool (and _384 _386))
(define-fun _388 () Bool __ART__100@0)
(define-fun _389 () Bool (= _284 _388))
(define-fun _390 () Bool (and _387 _389))


(push 1)
(assert _286)
(set-info :status sat)
(check-sat)
(push 1)
(assert _390)
(set-info :status sat)
(check-sat)
(pop 1)
(pop 1)
(exit)

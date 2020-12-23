%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:30 EST 2020

% Result     : Theorem 55.97s
% Output     : CNFRefutation 55.97s
% Verified   : 
% Statistics : Number of formulae       :  818 ( 819 expanded)
%              Number of leaves         :  811 ( 812 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_funct_2 > r1_relset_1 > v3_funct_2 > v1_funct_2 > r3_wellord1 > m2_subset_1 > m1_funct_2 > v5_relat_1 > v5_funct_1 > v4_relat_1 > v3_setfam_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > r8_relat_2 > r6_relat_2 > r4_wellord1 > r4_relat_2 > r3_xboole_0 > r2_xboole_0 > r2_wellord2 > r2_wellord1 > r2_tarski > r2_setfam_1 > r2_hidden > r1_xboole_0 > r1_wellord1 > r1_tarski > r1_subset_1 > r1_setfam_1 > r1_relat_2 > r1_partfun1 > r1_ordinal1 > m1_subset_1 > m1_setfam_1 > v8_relat_2 > v7_ordinal1 > v6_relat_2 > v6_ordinal1 > v5_ordinal1 > v4_relat_2 > v4_ordinal1 > v4_funct_1 > v3_relat_2 > v3_relat_1 > v3_ordinal1 > v3_funct_1 > v2_wellord1 > v2_setfam_1 > v2_relat_1 > v2_ordinal1 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_wellord1 > v1_setfam_1 > v1_relat_2 > v1_relat_1 > v1_ordinal1 > v1_funct_1 > v1_finset_1 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_relset_1 > k4_enumset1 > k1_partfun1 > k9_mcart_1 > k8_mcart_1 > k8_funct_2 > k3_enumset1 > k11_mcart_1 > k10_mcart_1 > k8_relset_1 > k7_relset_1 > k7_mcart_1 > k7_funct_2 > k6_relset_1 > k6_mcart_1 > k6_funct_2 > k5_relset_1 > k5_mcart_1 > k5_funct_2 > k4_zfmisc_1 > k4_mcart_1 > k4_funct_2 > k3_funct_2 > k2_partfun1 > k2_enumset1 > o_3_1_funct_2 > o_3_0_wellord2 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k7_partfun1 > k5_subset_1 > k5_partfun1 > k4_subset_1 > k3_zfmisc_1 > k3_relset_1 > k3_partfun1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > o_2_4_funct_2 > o_2_1_setfam_1 > o_2_1_relat_1 > o_2_0_wellord1 > o_2_0_setfam_1 > o_2_0_relat_1 > o_2_0_ordinal1 > k9_relat_1 > k8_setfam_1 > k8_relat_1 > k7_setfam_1 > k7_relat_1 > k6_subset_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k4_setfam_1 > k4_partfun1 > k3_xboole_0 > k3_wellord1 > k3_subset_1 > k3_setfam_1 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > k2_setfam_1 > k2_funct_2 > k1_wellord1 > k1_funct_2 > k1_funct_1 > k11_relat_1 > k10_relat_1 > a_2_1_mcart_1 > a_2_0_mcart_1 > #nlpp > o_1_6_relat_1 > o_1_5_relat_1 > o_1_4_relat_1 > o_1_3_relat_1 > o_1_2_relat_1 > o_1_1_relat_1 > o_1_1_funct_2 > o_1_0_wellord2 > o_1_0_setfam_1 > o_1_0_ordinal1 > o_1_0_mcart_1 > o_1_0_funct_1 > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k4_relat_1 > k3_tarski > k3_relat_1 > k2_wellord2 > k2_subset_1 > k2_relat_1 > k2_ordinal1 > k2_mcart_1 > k2_funct_1 > k20_mcart_1 > k1_zfmisc_1 > k1_wellord2 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_ordinal1 > k1_mcart_1 > k19_mcart_1 > k18_mcart_1 > k17_mcart_1 > k16_mcart_1 > k15_mcart_1 > o_0_0_xboole_0 > np__1 > k1_xboole_0 > #skF_385 > #skF_13 > #skF_464 > #skF_330 > #skF_287 > #skF_142 > #skF_550 > #skF_384 > #skF_615 > #skF_238 > #skF_338 > #skF_596 > #skF_91 > #skF_289 > #skF_598 > #skF_76 > #skF_527 > #skF_114 > #skF_298 > #skF_519 > #skF_199 > #skF_586 > #skF_47 > #skF_118 > #skF_531 > #skF_168 > #skF_326 > #skF_343 > #skF_456 > #skF_26 > #skF_564 > #skF_337 > #skF_410 > #skF_606 > #skF_557 > #skF_106 > #skF_577 > #skF_248 > #skF_11 > #skF_225 > #skF_406 > #skF_75 > #skF_254 > #skF_488 > #skF_500 > #skF_133 > #skF_559 > #skF_311 > #skF_499 > #skF_436 > #skF_41 > #skF_73 > #skF_484 > #skF_357 > #skF_281 > #skF_219 > #skF_228 > #skF_491 > #skF_316 > #skF_190 > #skF_175 > #skF_427 > #skF_65 > #skF_404 > #skF_540 > #skF_538 > #skF_183 > #skF_355 > #skF_416 > #skF_93 > #skF_33 > #skF_395 > #skF_57 > #skF_452 > #skF_278 > #skF_535 > #skF_148 > #skF_198 > #skF_422 > #skF_86 > #skF_18 > #skF_437 > #skF_421 > #skF_418 > #skF_386 > #skF_392 > #skF_523 > #skF_144 > #skF_146 > #skF_266 > #skF_121 > #skF_435 > #skF_582 > #skF_393 > #skF_113 > #skF_45 > #skF_515 > #skF_200 > #skF_364 > #skF_268 > #skF_264 > #skF_61 > #skF_66 > #skF_380 > #skF_111 > #skF_180 > #skF_442 > #skF_265 > #skF_558 > #skF_449 > #skF_6 > #skF_297 > #skF_455 > #skF_296 > #skF_378 > #skF_300 > #skF_131 > #skF_349 > #skF_327 > #skF_218 > #skF_518 > #skF_320 > #skF_87 > #skF_127 > #skF_371 > #skF_317 > #skF_490 > #skF_272 > #skF_1 > #skF_489 > #skF_396 > #skF_510 > #skF_68 > #skF_17 > #skF_492 > #skF_269 > #skF_530 > #skF_162 > #skF_217 > #skF_376 > #skF_584 > #skF_520 > #skF_414 > #skF_188 > #skF_363 > #skF_589 > #skF_48 > #skF_208 > #skF_302 > #skF_573 > #skF_149 > #skF_112 > #skF_202 > #skF_115 > #skF_171 > #skF_423 > #skF_420 > #skF_255 > #skF_347 > #skF_257 > #skF_301 > #skF_605 > #skF_247 > #skF_352 > #skF_334 > #skF_324 > #skF_32 > #skF_116 > #skF_471 > #skF_356 > #skF_306 > #skF_286 > #skF_549 > #skF_94 > #skF_203 > #skF_308 > #skF_165 > #skF_292 > #skF_361 > #skF_72 > #skF_480 > #skF_578 > #skF_353 > #skF_567 > #skF_369 > #skF_280 > #skF_70 > #skF_314 > #skF_153 > #skF_275 > #skF_487 > #skF_390 > #skF_617 > #skF_417 > #skF_556 > #skF_299 > #skF_604 > #skF_511 > #skF_342 > #skF_430 > #skF_155 > #skF_474 > #skF_99 > #skF_453 > #skF_565 > #skF_501 > #skF_399 > #skF_60 > #skF_92 > #skF_31 > #skF_136 > #skF_432 > #skF_303 > #skF_568 > #skF_583 > #skF_209 > #skF_161 > #skF_4 > #skF_36 > #skF_319 > #skF_108 > #skF_387 > #skF_602 > #skF_412 > #skF_552 > #skF_235 > #skF_291 > #skF_138 > #skF_261 > #skF_555 > #skF_533 > #skF_419 > #skF_572 > #skF_526 > #skF_391 > #skF_79 > #skF_509 > #skF_332 > #skF_478 > #skF_69 > #skF_10 > #skF_498 > #skF_408 > #skF_370 > #skF_433 > #skF_377 > #skF_545 > #skF_81 > #skF_318 > #skF_372 > #skF_322 > #skF_117 > #skF_541 > #skF_539 > #skF_462 > #skF_497 > #skF_192 > #skF_95 > #skF_159 > #skF_84 > #skF_588 > #skF_325 > #skF_517 > #skF_253 > #skF_468 > #skF_100 > #skF_305 > #skF_571 > #skF_503 > #skF_616 > #skF_187 > #skF_176 > #skF_521 > #skF_313 > #skF_358 > #skF_37 > #skF_221 > #skF_522 > #skF_284 > #skF_82 > #skF_167 > #skF_469 > #skF_12 > #skF_123 > #skF_169 > #skF_96 > #skF_56 > #skF_143 > #skF_78 > #skF_172 > #skF_240 > #skF_173 > #skF_400 > #skF_88 > #skF_473 > #skF_425 > #skF_28 > #skF_156 > #skF_67 > #skF_197 > #skF_494 > #skF_446 > #skF_485 > #skF_46 > #skF_160 > #skF_563 > #skF_277 > #skF_472 > #skF_566 > #skF_290 > #skF_35 > #skF_74 > #skF_5 > #skF_196 > #skF_267 > #skF_534 > #skF_49 > #skF_608 > #skF_19 > #skF_466 > #skF_611 > #skF_44 > #skF_215 > #skF_477 > #skF_163 > #skF_507 > #skF_514 > #skF_30 > #skF_232 > #skF_618 > #skF_141 > #skF_585 > #skF_411 > #skF_321 > #skF_27 > #skF_592 > #skF_224 > #skF_110 > #skF_428 > #skF_97 > #skF_244 > #skF_154 > #skF_251 > #skF_379 > #skF_401 > #skF_448 > #skF_508 > #skF_184 > #skF_107 > #skF_504 > #skF_164 > #skF_85 > #skF_470 > #skF_80 > #skF_193 > #skF_51 > #skF_619 > #skF_9 > #skF_220 > #skF_383 > #skF_547 > #skF_231 > #skF_413 > #skF_365 > #skF_201 > #skF_554 > #skF_166 > #skF_212 > #skF_90 > #skF_206 > #skF_405 > #skF_457 > #skF_486 > #skF_461 > #skF_126 > #skF_513 > #skF_71 > #skF_234 > #skF_222 > #skF_195 > #skF_307 > #skF_7 > #skF_119 > #skF_328 > #skF_64 > #skF_576 > #skF_362 > #skF_276 > #skF_581 > #skF_223 > #skF_348 > #skF_600 > #skF_544 > #skF_612 > #skF_252 > #skF_170 > #skF_561 > #skF_493 > #skF_103 > #skF_216 > #skF_479 > #skF_229 > #skF_294 > #skF_20 > #skF_335 > #skF_279 > #skF_260 > #skF_434 > #skF_460 > #skF_443 > #skF_548 > #skF_467 > #skF_189 > #skF_211 > #skF_579 > #skF_236 > #skF_24 > #skF_495 > #skF_607 > #skF_340 > #skF_599 > #skF_329 > #skF_34 > #skF_595 > #skF_23 > #skF_476 > #skF_182 > #skF_185 > #skF_551 > #skF_580 > #skF_398 > #skF_389 > #skF_366 > #skF_610 > #skF_128 > #skF_459 > #skF_560 > #skF_151 > #skF_14 > #skF_465 > #skF_50 > #skF_367 > #skF_451 > #skF_89 > #skF_388 > #skF_140 > #skF_178 > #skF_205 > #skF_130 > #skF_397 > #skF_77 > #skF_593 > #skF_186 > #skF_263 > #skF_204 > #skF_152 > #skF_403 > #skF_145 > #skF_242 > #skF_174 > #skF_233 > #skF_249 > #skF_285 > #skF_63 > #skF_359 > #skF_368 > #skF_594 > #skF_59 > #skF_532 > #skF_315 > #skF_230 > #skF_481 > #skF_207 > #skF_104 > #skF_512 > #skF_525 > #skF_58 > #skF_373 > #skF_181 > #skF_336 > #skF_43 > #skF_537 > #skF_52 > #skF_137 > #skF_54 > #skF_614 > #skF_274 > #skF_482 > #skF_454 > #skF_431 > #skF_125 > #skF_191 > #skF_3 > #skF_458 > #skF_502 > #skF_309 > #skF_341 > #skF_424 > #skF_62 > #skF_288 > #skF_339 > #skF_55 > #skF_38 > #skF_496 > #skF_331 > #skF_2 > #skF_562 > #skF_157 > #skF_21 > #skF_354 > #skF_101 > #skF_333 > #skF_409 > #skF_179 > #skF_243 > #skF_241 > #skF_542 > #skF_226 > #skF_177 > #skF_426 > #skF_120 > #skF_102 > #skF_402 > #skF_105 > #skF_447 > #skF_40 > #skF_569 > #skF_214 > #skF_135 > #skF_613 > #skF_122 > #skF_444 > #skF_506 > #skF_570 > #skF_8 > #skF_270 > #skF_262 > #skF_381 > #skF_345 > #skF_574 > #skF_25 > #skF_304 > #skF_536 > #skF_273 > #skF_415 > #skF_375 > #skF_603 > #skF_591 > #skF_258 > #skF_227 > #skF_147 > #skF_293 > #skF_259 > #skF_463 > #skF_516 > #skF_575 > #skF_312 > #skF_601 > #skF_213 > #skF_132 > #skF_124 > #skF_295 > #skF_29 > #skF_529 > #skF_597 > #skF_237 > #skF_590 > #skF_483 > #skF_210 > #skF_250 > #skF_609 > #skF_360 > #skF_344 > #skF_439 > #skF_524 > #skF_394 > #skF_16 > #skF_543 > #skF_438 > #skF_283 > #skF_129 > #skF_374 > #skF_150 > #skF_553 > #skF_346 > #skF_445 > #skF_98 > #skF_441 > #skF_134 > #skF_83 > #skF_22 > #skF_587 > #skF_15 > #skF_440 > #skF_139 > #skF_351 > #skF_239 > #skF_282 > #skF_158 > #skF_42 > #skF_429 > #skF_450 > #skF_53 > #skF_194 > #skF_350 > #skF_245 > #skF_546 > #skF_256 > #skF_475 > #skF_407 > #skF_323 > #skF_39 > #skF_310 > #skF_528 > #skF_505 > #skF_271 > #skF_246 > #skF_109 > #skF_382

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_385',type,(
    '#skF_385': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(o_1_1_funct_2,type,(
    o_1_1_funct_2: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_464',type,(
    '#skF_464': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_330',type,(
    '#skF_330': ( $i * $i ) > $i )).

tff('#skF_287',type,(
    '#skF_287': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_142',type,(
    '#skF_142': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_550',type,(
    '#skF_550': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_384',type,(
    '#skF_384': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_615',type,(
    '#skF_615': ( $i * $i ) > $i )).

tff('#skF_238',type,(
    '#skF_238': ( $i * $i ) > $i )).

tff('#skF_338',type,(
    '#skF_338': ( $i * $i ) > $i )).

tff('#skF_596',type,(
    '#skF_596': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_91',type,(
    '#skF_91': $i > $i )).

tff('#skF_289',type,(
    '#skF_289': $i > $i )).

tff('#skF_598',type,(
    '#skF_598': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_76',type,(
    '#skF_76': ( $i * $i ) > $i )).

tff('#skF_527',type,(
    '#skF_527': $i > $i )).

tff('#skF_114',type,(
    '#skF_114': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_298',type,(
    '#skF_298': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_519',type,(
    '#skF_519': ( $i * $i ) > $i )).

tff('#skF_199',type,(
    '#skF_199': $i > $i )).

tff('#skF_586',type,(
    '#skF_586': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_118',type,(
    '#skF_118': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_531',type,(
    '#skF_531': $i > $i )).

tff('#skF_168',type,(
    '#skF_168': ( $i * $i ) > $i )).

tff('#skF_326',type,(
    '#skF_326': $i > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_343',type,(
    '#skF_343': ( $i * $i ) > $i )).

tff('#skF_456',type,(
    '#skF_456': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#skF_564',type,(
    '#skF_564': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_337',type,(
    '#skF_337': ( $i * $i ) > $i )).

tff('#skF_410',type,(
    '#skF_410': ( $i * $i ) > $i )).

tff(o_1_0_mcart_1,type,(
    o_1_0_mcart_1: $i > $i )).

tff('#skF_606',type,(
    '#skF_606': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_557',type,(
    '#skF_557': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_106',type,(
    '#skF_106': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_577',type,(
    '#skF_577': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_248',type,(
    '#skF_248': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff(k4_funct_2,type,(
    k4_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_225',type,(
    '#skF_225': ( $i * $i ) > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_406',type,(
    '#skF_406': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_75',type,(
    '#skF_75': ( $i * $i ) > $i )).

tff('#skF_254',type,(
    '#skF_254': ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_488',type,(
    '#skF_488': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_500',type,(
    '#skF_500': ( $i * $i ) > $i )).

tff('#skF_133',type,(
    '#skF_133': $i > $i )).

tff('#skF_559',type,(
    '#skF_559': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_311',type,(
    '#skF_311': ( $i * $i ) > $i )).

tff('#skF_499',type,(
    '#skF_499': ( $i * $i ) > $i )).

tff('#skF_436',type,(
    '#skF_436': $i > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff('#skF_73',type,(
    '#skF_73': ( $i * $i ) > $i )).

tff('#skF_484',type,(
    '#skF_484': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_357',type,(
    '#skF_357': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_281',type,(
    '#skF_281': $i )).

tff(k3_partfun1,type,(
    k3_partfun1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_219',type,(
    '#skF_219': $i )).

tff('#skF_228',type,(
    '#skF_228': ( $i * $i ) > $i )).

tff(o_2_1_relat_1,type,(
    o_2_1_relat_1: ( $i * $i ) > $i )).

tff('#skF_491',type,(
    '#skF_491': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff('#skF_316',type,(
    '#skF_316': ( $i * ( $i * $i ) ) > $i )).

tff(m1_funct_2,type,(
    m1_funct_2: ( $i * ( $i * $i ) ) > $o )).

tff('#skF_190',type,(
    '#skF_190': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_175',type,(
    '#skF_175': ( $i * $i ) > $i )).

tff('#skF_427',type,(
    '#skF_427': ( $i * $i ) > $i )).

tff('#skF_65',type,(
    '#skF_65': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r1_wellord1,type,(
    r1_wellord1: ( $i * $i ) > $o )).

tff('#skF_404',type,(
    '#skF_404': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_540',type,(
    '#skF_540': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_538',type,(
    '#skF_538': $i > $i )).

tff('#skF_183',type,(
    '#skF_183': ( $i * $i ) > $i )).

tff('#skF_355',type,(
    '#skF_355': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k5_funct_2,type,(
    k5_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_416',type,(
    '#skF_416': ( $i * $i ) > $i )).

tff('#skF_93',type,(
    '#skF_93': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_395',type,(
    '#skF_395': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(o_1_4_relat_1,type,(
    o_1_4_relat_1: $i > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff('#skF_452',type,(
    '#skF_452': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_278',type,(
    '#skF_278': $i > $i )).

tff('#skF_535',type,(
    '#skF_535': $i > $i )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#skF_148',type,(
    '#skF_148': ( $i * ( $i * $i ) ) > $i )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * ( $i * $i ) ) > $o )).

tff('#skF_198',type,(
    '#skF_198': ( $i * $i ) > $i )).

tff('#skF_422',type,(
    '#skF_422': ( $i * $i ) > $i )).

tff('#skF_86',type,(
    '#skF_86': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $o )).

tff('#skF_437',type,(
    '#skF_437': ( $i * $i ) > $i )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_421',type,(
    '#skF_421': ( $i * $i ) > $i )).

tff('#skF_418',type,(
    '#skF_418': $i > $i )).

tff('#skF_386',type,(
    '#skF_386': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_392',type,(
    '#skF_392': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_523',type,(
    '#skF_523': $i > $i )).

tff('#skF_144',type,(
    '#skF_144': ( $i * $i ) > $i )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_146',type,(
    '#skF_146': ( $i * $i ) > $i )).

tff('#skF_266',type,(
    '#skF_266': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_121',type,(
    '#skF_121': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_435',type,(
    '#skF_435': $i > $i )).

tff('#skF_582',type,(
    '#skF_582': ( $i * $i ) > $i )).

tff('#skF_393',type,(
    '#skF_393': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff('#skF_113',type,(
    '#skF_113': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_45',type,(
    '#skF_45': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_515',type,(
    '#skF_515': ( $i * $i ) > $i )).

tff('#skF_200',type,(
    '#skF_200': $i > $i )).

tff('#skF_364',type,(
    '#skF_364': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_268',type,(
    '#skF_268': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_264',type,(
    '#skF_264': ( $i * $i ) > $i )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_380',type,(
    '#skF_380': ( $i * $i ) > $i )).

tff('#skF_111',type,(
    '#skF_111': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_180',type,(
    '#skF_180': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_442',type,(
    '#skF_442': ( $i * $i ) > $i )).

tff('#skF_265',type,(
    '#skF_265': ( $i * ( $i * $i ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_558',type,(
    '#skF_558': ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(o_2_1_setfam_1,type,(
    o_2_1_setfam_1: ( $i * $i ) > $i )).

tff('#skF_449',type,(
    '#skF_449': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(r2_wellord2,type,(
    r2_wellord2: ( $i * $i ) > $o )).

tff('#skF_297',type,(
    '#skF_297': $i > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_455',type,(
    '#skF_455': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_296',type,(
    '#skF_296': $i > $i )).

tff('#skF_378',type,(
    '#skF_378': ( $i * $i ) > $i )).

tff('#skF_300',type,(
    '#skF_300': $i > $i )).

tff('#skF_131',type,(
    '#skF_131': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_349',type,(
    '#skF_349': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_327',type,(
    '#skF_327': $i > $i )).

tff('#skF_218',type,(
    '#skF_218': $i )).

tff('#skF_518',type,(
    '#skF_518': ( $i * $i ) > $i )).

tff('#skF_320',type,(
    '#skF_320': $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_87',type,(
    '#skF_87': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_127',type,(
    '#skF_127': ( $i * ( $i * $i ) ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_371',type,(
    '#skF_371': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_317',type,(
    '#skF_317': ( $i * ( $i * $i ) ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_490',type,(
    '#skF_490': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_272',type,(
    '#skF_272': $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_489',type,(
    '#skF_489': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_396',type,(
    '#skF_396': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_510',type,(
    '#skF_510': ( $i * $i ) > $i )).

tff('#skF_68',type,(
    '#skF_68': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff('#skF_492',type,(
    '#skF_492': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_269',type,(
    '#skF_269': ( $i * $i ) > $i )).

tff('#skF_530',type,(
    '#skF_530': $i > $i )).

tff('#skF_162',type,(
    '#skF_162': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_217',type,(
    '#skF_217': $i )).

tff('#skF_376',type,(
    '#skF_376': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_584',type,(
    '#skF_584': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_520',type,(
    '#skF_520': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_414',type,(
    '#skF_414': $i > $i )).

tff('#skF_188',type,(
    '#skF_188': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_363',type,(
    '#skF_363': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_589',type,(
    '#skF_589': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_208',type,(
    '#skF_208': $i > $i )).

tff('#skF_302',type,(
    '#skF_302': $i > $i )).

tff('#skF_573',type,(
    '#skF_573': ( $i * $i ) > $i )).

tff('#skF_149',type,(
    '#skF_149': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_112',type,(
    '#skF_112': ( $i * $i ) > $i )).

tff('#skF_202',type,(
    '#skF_202': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_115',type,(
    '#skF_115': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_171',type,(
    '#skF_171': ( $i * $i ) > $i )).

tff('#skF_423',type,(
    '#skF_423': $i > $i )).

tff('#skF_420',type,(
    '#skF_420': ( $i * $i ) > $i )).

tff('#skF_255',type,(
    '#skF_255': ( $i * $i ) > $i )).

tff('#skF_347',type,(
    '#skF_347': ( $i * $i ) > $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_257',type,(
    '#skF_257': $i > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_301',type,(
    '#skF_301': $i > $i )).

tff(k2_wellord2,type,(
    k2_wellord2: $i > $i )).

tff('#skF_605',type,(
    '#skF_605': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_247',type,(
    '#skF_247': $i > $i )).

tff('#skF_352',type,(
    '#skF_352': ( $i * $i ) > $i )).

tff('#skF_334',type,(
    '#skF_334': ( $i * $i ) > $i )).

tff('#skF_324',type,(
    '#skF_324': $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff(o_1_5_relat_1,type,(
    o_1_5_relat_1: $i > $i )).

tff('#skF_116',type,(
    '#skF_116': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_471',type,(
    '#skF_471': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_356',type,(
    '#skF_356': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_306',type,(
    '#skF_306': ( $i * $i ) > $i )).

tff('#skF_286',type,(
    '#skF_286': $i > $i )).

tff('#skF_549',type,(
    '#skF_549': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_94',type,(
    '#skF_94': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_203',type,(
    '#skF_203': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_308',type,(
    '#skF_308': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_165',type,(
    '#skF_165': ( $i * $i ) > $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_292',type,(
    '#skF_292': ( $i * $i ) > $i )).

tff('#skF_361',type,(
    '#skF_361': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_480',type,(
    '#skF_480': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_578',type,(
    '#skF_578': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_353',type,(
    '#skF_353': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_567',type,(
    '#skF_567': ( $i * $i ) > $i )).

tff('#skF_369',type,(
    '#skF_369': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_280',type,(
    '#skF_280': $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff('#skF_314',type,(
    '#skF_314': ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff('#skF_153',type,(
    '#skF_153': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_275',type,(
    '#skF_275': $i > $i )).

tff('#skF_487',type,(
    '#skF_487': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff('#skF_390',type,(
    '#skF_390': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_617',type,(
    '#skF_617': $i )).

tff('#skF_417',type,(
    '#skF_417': ( $i * $i ) > $i )).

tff('#skF_556',type,(
    '#skF_556': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_299',type,(
    '#skF_299': $i > $i )).

tff('#skF_604',type,(
    '#skF_604': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_511',type,(
    '#skF_511': ( $i * $i ) > $i )).

tff('#skF_342',type,(
    '#skF_342': ( $i * $i ) > $i )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $o )).

tff('#skF_430',type,(
    '#skF_430': ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff('#skF_155',type,(
    '#skF_155': ( $i * ( $i * $i ) ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_474',type,(
    '#skF_474': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_99',type,(
    '#skF_99': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_453',type,(
    '#skF_453': $i > $i )).

tff('#skF_565',type,(
    '#skF_565': ( $i * $i ) > $i )).

tff('#skF_501',type,(
    '#skF_501': ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_399',type,(
    '#skF_399': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * $i ) > $i )).

tff('#skF_92',type,(
    '#skF_92': ( $i * $i ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff('#skF_136',type,(
    '#skF_136': $i > $i )).

tff('#skF_432',type,(
    '#skF_432': ( $i * $i ) > $i )).

tff('#skF_303',type,(
    '#skF_303': $i > $i )).

tff('#skF_568',type,(
    '#skF_568': ( $i * $i ) > $i )).

tff('#skF_583',type,(
    '#skF_583': ( $i * ( $i * $i ) ) > $i )).

tff(k17_mcart_1,type,(
    k17_mcart_1: $i > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_209',type,(
    '#skF_209': ( $i * $i ) > $i )).

tff('#skF_161',type,(
    '#skF_161': ( $i * ( $i * $i ) ) > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_319',type,(
    '#skF_319': ( $i * $i ) > $i )).

tff('#skF_108',type,(
    '#skF_108': ( $i * $i ) > $i )).

tff('#skF_387',type,(
    '#skF_387': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_602',type,(
    '#skF_602': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_412',type,(
    '#skF_412': ( $i * $i ) > $i )).

tff(v7_ordinal1,type,(
    v7_ordinal1: $i > $o )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff('#skF_552',type,(
    '#skF_552': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_235',type,(
    '#skF_235': $i > $i )).

tff('#skF_291',type,(
    '#skF_291': $i > $i )).

tff('#skF_138',type,(
    '#skF_138': $i > $i )).

tff('#skF_261',type,(
    '#skF_261': ( $i * $i ) > $i )).

tff('#skF_555',type,(
    '#skF_555': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_533',type,(
    '#skF_533': $i > $i )).

tff('#skF_419',type,(
    '#skF_419': ( $i * $i ) > $i )).

tff('#skF_572',type,(
    '#skF_572': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_526',type,(
    '#skF_526': ( $i * $i ) > $i )).

tff('#skF_391',type,(
    '#skF_391': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_79',type,(
    '#skF_79': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_509',type,(
    '#skF_509': $i > $i )).

tff('#skF_332',type,(
    '#skF_332': ( $i * $i ) > $i )).

tff('#skF_478',type,(
    '#skF_478': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_69',type,(
    '#skF_69': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_498',type,(
    '#skF_498': ( $i * $i ) > $i )).

tff('#skF_408',type,(
    '#skF_408': $i > $i )).

tff('#skF_370',type,(
    '#skF_370': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_433',type,(
    '#skF_433': $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_377',type,(
    '#skF_377': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_545',type,(
    '#skF_545': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_81',type,(
    '#skF_81': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_318',type,(
    '#skF_318': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_372',type,(
    '#skF_372': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_322',type,(
    '#skF_322': $i > $i )).

tff('#skF_117',type,(
    '#skF_117': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_541',type,(
    '#skF_541': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_539',type,(
    '#skF_539': $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_462',type,(
    '#skF_462': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_497',type,(
    '#skF_497': ( $i * $i ) > $i )).

tff('#skF_192',type,(
    '#skF_192': $i )).

tff('#skF_95',type,(
    '#skF_95': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_159',type,(
    '#skF_159': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_588',type,(
    '#skF_588': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_325',type,(
    '#skF_325': $i > $i )).

tff('#skF_517',type,(
    '#skF_517': ( $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_253',type,(
    '#skF_253': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_468',type,(
    '#skF_468': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_100',type,(
    '#skF_100': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_305',type,(
    '#skF_305': $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_571',type,(
    '#skF_571': $i > $i )).

tff('#skF_503',type,(
    '#skF_503': ( $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_616',type,(
    '#skF_616': ( $i * $i ) > $i )).

tff('#skF_187',type,(
    '#skF_187': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_176',type,(
    '#skF_176': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_521',type,(
    '#skF_521': ( $i * $i ) > $i )).

tff('#skF_313',type,(
    '#skF_313': ( $i * $i ) > $i )).

tff('#skF_358',type,(
    '#skF_358': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_221',type,(
    '#skF_221': $i )).

tff('#skF_522',type,(
    '#skF_522': $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_284',type,(
    '#skF_284': $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_82',type,(
    '#skF_82': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_167',type,(
    '#skF_167': ( $i * $i ) > $i )).

tff('#skF_469',type,(
    '#skF_469': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_123',type,(
    '#skF_123': ( $i * ( $i * $i ) ) > $i )).

tff(v1_setfam_1,type,(
    v1_setfam_1: $i > $o )).

tff('#skF_169',type,(
    '#skF_169': ( $i * $i ) > $i )).

tff(o_1_0_setfam_1,type,(
    o_1_0_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_96',type,(
    '#skF_96': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(a_2_1_mcart_1,type,(
    a_2_1_mcart_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_143',type,(
    '#skF_143': ( $i * $i ) > $i )).

tff(v4_funct_1,type,(
    v4_funct_1: $i > $o )).

tff('#skF_78',type,(
    '#skF_78': ( $i * $i ) > $i )).

tff('#skF_172',type,(
    '#skF_172': ( $i * $i ) > $i )).

tff('#skF_240',type,(
    '#skF_240': ( $i * $i ) > $i )).

tff('#skF_173',type,(
    '#skF_173': ( $i * $i ) > $i )).

tff('#skF_400',type,(
    '#skF_400': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_88',type,(
    '#skF_88': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_473',type,(
    '#skF_473': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_425',type,(
    '#skF_425': ( $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_156',type,(
    '#skF_156': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * ( $i * $i ) ) > $o )).

tff('#skF_197',type,(
    '#skF_197': ( $i * $i ) > $i )).

tff('#skF_494',type,(
    '#skF_494': $i > $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_446',type,(
    '#skF_446': $i > $i )).

tff('#skF_485',type,(
    '#skF_485': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(v6_ordinal1,type,(
    v6_ordinal1: $i > $o )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_160',type,(
    '#skF_160': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_563',type,(
    '#skF_563': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_277',type,(
    '#skF_277': $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_472',type,(
    '#skF_472': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_566',type,(
    '#skF_566': ( $i * $i ) > $i )).

tff('#skF_290',type,(
    '#skF_290': ( $i * $i ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_74',type,(
    '#skF_74': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_196',type,(
    '#skF_196': $i > $i )).

tff('#skF_267',type,(
    '#skF_267': ( $i * ( $i * $i ) ) > $i )).

tff(k4_setfam_1,type,(
    k4_setfam_1: ( $i * $i ) > $i )).

tff('#skF_534',type,(
    '#skF_534': $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_49',type,(
    '#skF_49': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_608',type,(
    '#skF_608': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff(k2_ordinal1,type,(
    k2_ordinal1: $i > $i )).

tff('#skF_466',type,(
    '#skF_466': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_611',type,(
    '#skF_611': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_215',type,(
    '#skF_215': $i > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_477',type,(
    '#skF_477': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_163',type,(
    '#skF_163': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_507',type,(
    '#skF_507': $i > $i )).

tff('#skF_514',type,(
    '#skF_514': ( $i * ( $i * $i ) ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_232',type,(
    '#skF_232': $i > $i )).

tff('#skF_618',type,(
    '#skF_618': $i )).

tff('#skF_141',type,(
    '#skF_141': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_585',type,(
    '#skF_585': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_411',type,(
    '#skF_411': $i > $i )).

tff('#skF_321',type,(
    '#skF_321': $i > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(a_2_0_mcart_1,type,(
    a_2_0_mcart_1: ( $i * $i ) > $i )).

tff('#skF_592',type,(
    '#skF_592': ( $i * $i ) > $i )).

tff('#skF_224',type,(
    '#skF_224': ( $i * $i ) > $i )).

tff('#skF_110',type,(
    '#skF_110': ( $i * $i ) > $i )).

tff('#skF_428',type,(
    '#skF_428': ( $i * $i ) > $i )).

tff('#skF_97',type,(
    '#skF_97': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_244',type,(
    '#skF_244': ( $i * $i ) > $i )).

tff('#skF_154',type,(
    '#skF_154': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_251',type,(
    '#skF_251': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_379',type,(
    '#skF_379': ( $i * $i ) > $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_401',type,(
    '#skF_401': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_448',type,(
    '#skF_448': $i > $i )).

tff('#skF_508',type,(
    '#skF_508': ( $i * $i ) > $i )).

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff('#skF_184',type,(
    '#skF_184': ( $i * $i ) > $i )).

tff('#skF_107',type,(
    '#skF_107': ( $i * $i ) > $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff('#skF_504',type,(
    '#skF_504': $i )).

tff('#skF_164',type,(
    '#skF_164': $i > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_470',type,(
    '#skF_470': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_80',type,(
    '#skF_80': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_193',type,(
    '#skF_193': ( $i * $i ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff('#skF_619',type,(
    '#skF_619': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(v2_setfam_1,type,(
    v2_setfam_1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_220',type,(
    '#skF_220': $i )).

tff('#skF_383',type,(
    '#skF_383': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_547',type,(
    '#skF_547': $i > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_231',type,(
    '#skF_231': $i > $i )).

tff('#skF_413',type,(
    '#skF_413': ( $i * $i ) > $i )).

tff('#skF_365',type,(
    '#skF_365': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_201',type,(
    '#skF_201': ( $i * $i ) > $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_554',type,(
    '#skF_554': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_166',type,(
    '#skF_166': ( $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#skF_212',type,(
    '#skF_212': ( $i * $i ) > $i )).

tff('#skF_90',type,(
    '#skF_90': $i > $i )).

tff('#skF_206',type,(
    '#skF_206': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_405',type,(
    '#skF_405': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_457',type,(
    '#skF_457': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_486',type,(
    '#skF_486': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_461',type,(
    '#skF_461': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_126',type,(
    '#skF_126': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_513',type,(
    '#skF_513': ( $i * $i ) > $i )).

tff('#skF_71',type,(
    '#skF_71': ( $i * $i ) > $i )).

tff('#skF_234',type,(
    '#skF_234': $i > $i )).

tff('#skF_222',type,(
    '#skF_222': ( $i * $i ) > $i )).

tff(o_2_4_funct_2,type,(
    o_2_4_funct_2: ( $i * $i ) > $i )).

tff('#skF_195',type,(
    '#skF_195': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_307',type,(
    '#skF_307': ( $i * ( $i * $i ) ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_119',type,(
    '#skF_119': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_328',type,(
    '#skF_328': ( $i * $i ) > $i )).

tff('#skF_64',type,(
    '#skF_64': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_576',type,(
    '#skF_576': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_362',type,(
    '#skF_362': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_276',type,(
    '#skF_276': $i > $i )).

tff('#skF_581',type,(
    '#skF_581': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_223',type,(
    '#skF_223': ( $i * $i ) > $i )).

tff('#skF_348',type,(
    '#skF_348': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_600',type,(
    '#skF_600': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_544',type,(
    '#skF_544': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_612',type,(
    '#skF_612': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_252',type,(
    '#skF_252': ( $i * ( $i * $i ) ) > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff('#skF_170',type,(
    '#skF_170': ( $i * $i ) > $i )).

tff('#skF_561',type,(
    '#skF_561': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_493',type,(
    '#skF_493': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_103',type,(
    '#skF_103': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_216',type,(
    '#skF_216': $i )).

tff('#skF_479',type,(
    '#skF_479': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_229',type,(
    '#skF_229': ( $i * $i ) > $i )).

tff('#skF_294',type,(
    '#skF_294': ( $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_335',type,(
    '#skF_335': ( $i * $i ) > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_279',type,(
    '#skF_279': $i > $i )).

tff('#skF_260',type,(
    '#skF_260': ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_434',type,(
    '#skF_434': $i > $i )).

tff('#skF_460',type,(
    '#skF_460': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_443',type,(
    '#skF_443': $i > $i )).

tff('#skF_548',type,(
    '#skF_548': $i > $i )).

tff('#skF_467',type,(
    '#skF_467': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#skF_189',type,(
    '#skF_189': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_211',type,(
    '#skF_211': ( $i * $i ) > $i )).

tff('#skF_579',type,(
    '#skF_579': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_236',type,(
    '#skF_236': $i > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff(o_1_6_relat_1,type,(
    o_1_6_relat_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_495',type,(
    '#skF_495': ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_607',type,(
    '#skF_607': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_340',type,(
    '#skF_340': ( $i * $i ) > $i )).

tff('#skF_599',type,(
    '#skF_599': ( $i * $i ) > $i )).

tff('#skF_329',type,(
    '#skF_329': $i > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_595',type,(
    '#skF_595': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#skF_476',type,(
    '#skF_476': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_182',type,(
    '#skF_182': ( $i * $i ) > $i )).

tff('#skF_185',type,(
    '#skF_185': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_551',type,(
    '#skF_551': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_580',type,(
    '#skF_580': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_398',type,(
    '#skF_398': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_389',type,(
    '#skF_389': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_366',type,(
    '#skF_366': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_610',type,(
    '#skF_610': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k3_wellord1,type,(
    k3_wellord1: ( $i * $i ) > $i )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_128',type,(
    '#skF_128': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_459',type,(
    '#skF_459': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_560',type,(
    '#skF_560': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_151',type,(
    '#skF_151': ( $i * ( $i * $i ) ) > $i )).

tff(o_1_0_ordinal1,type,(
    o_1_0_ordinal1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_465',type,(
    '#skF_465': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_50',type,(
    '#skF_50': ( $i * $i ) > $i )).

tff('#skF_367',type,(
    '#skF_367': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_451',type,(
    '#skF_451': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_89',type,(
    '#skF_89': $i > $i )).

tff('#skF_388',type,(
    '#skF_388': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(o_2_0_setfam_1,type,(
    o_2_0_setfam_1: ( $i * $i ) > $i )).

tff('#skF_140',type,(
    '#skF_140': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_178',type,(
    '#skF_178': ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_205',type,(
    '#skF_205': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(o_1_0_wellord2,type,(
    o_1_0_wellord2: $i > $i )).

tff('#skF_130',type,(
    '#skF_130': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k20_mcart_1,type,(
    k20_mcart_1: $i > $i )).

tff('#skF_397',type,(
    '#skF_397': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_77',type,(
    '#skF_77': $i > $i )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_593',type,(
    '#skF_593': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_186',type,(
    '#skF_186': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_263',type,(
    '#skF_263': ( $i * $i ) > $i )).

tff(o_2_0_ordinal1,type,(
    o_2_0_ordinal1: ( $i * $i ) > $i )).

tff('#skF_204',type,(
    '#skF_204': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_152',type,(
    '#skF_152': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_403',type,(
    '#skF_403': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_145',type,(
    '#skF_145': ( $i * $i ) > $i )).

tff('#skF_242',type,(
    '#skF_242': ( $i * $i ) > $i )).

tff('#skF_174',type,(
    '#skF_174': ( $i * $i ) > $i )).

tff(k4_partfun1,type,(
    k4_partfun1: ( $i * $i ) > $i )).

tff('#skF_233',type,(
    '#skF_233': $i > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_249',type,(
    '#skF_249': ( $i * $i ) > $i )).

tff('#skF_285',type,(
    '#skF_285': $i > $i )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_359',type,(
    '#skF_359': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_368',type,(
    '#skF_368': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_594',type,(
    '#skF_594': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * $i ) > $i )).

tff('#skF_532',type,(
    '#skF_532': $i > $i )).

tff('#skF_315',type,(
    '#skF_315': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_230',type,(
    '#skF_230': $i > $i )).

tff('#skF_481',type,(
    '#skF_481': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_207',type,(
    '#skF_207': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_104',type,(
    '#skF_104': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_512',type,(
    '#skF_512': ( $i * $i ) > $i )).

tff('#skF_525',type,(
    '#skF_525': $i > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * $i ) > $i )).

tff('#skF_373',type,(
    '#skF_373': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_181',type,(
    '#skF_181': ( $i * $i ) > $i )).

tff('#skF_336',type,(
    '#skF_336': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_43',type,(
    '#skF_43': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_537',type,(
    '#skF_537': ( $i * $i ) > $i )).

tff('#skF_52',type,(
    '#skF_52': ( $i * $i ) > $i )).

tff('#skF_137',type,(
    '#skF_137': $i > $i )).

tff('#skF_54',type,(
    '#skF_54': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_614',type,(
    '#skF_614': ( $i * $i ) > $i )).

tff('#skF_274',type,(
    '#skF_274': $i > $i )).

tff('#skF_482',type,(
    '#skF_482': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_454',type,(
    '#skF_454': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_431',type,(
    '#skF_431': ( $i * $i ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_125',type,(
    '#skF_125': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_191',type,(
    '#skF_191': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#skF_458',type,(
    '#skF_458': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_502',type,(
    '#skF_502': ( $i * $i ) > $i )).

tff('#skF_309',type,(
    '#skF_309': ( $i * $i ) > $i )).

tff('#skF_341',type,(
    '#skF_341': ( $i * $i ) > $i )).

tff(k18_mcart_1,type,(
    k18_mcart_1: $i > $i )).

tff('#skF_424',type,(
    '#skF_424': $i > $i )).

tff('#skF_62',type,(
    '#skF_62': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_288',type,(
    '#skF_288': ( $i * $i ) > $i )).

tff('#skF_339',type,(
    '#skF_339': $i > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#skF_55',type,(
    '#skF_55': ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_496',type,(
    '#skF_496': ( $i * $i ) > $i )).

tff('#skF_331',type,(
    '#skF_331': ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * ( $i * $i ) ) > $o )).

tff('#skF_562',type,(
    '#skF_562': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_157',type,(
    '#skF_157': ( $i * ( $i * $i ) ) > $i )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_354',type,(
    '#skF_354': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_101',type,(
    '#skF_101': ( $i * ( $i * $i ) ) > $i )).

tff(k16_mcart_1,type,(
    k16_mcart_1: $i > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_333',type,(
    '#skF_333': ( $i * $i ) > $i )).

tff('#skF_409',type,(
    '#skF_409': $i > $i )).

tff('#skF_179',type,(
    '#skF_179': ( $i * $i ) > $i )).

tff('#skF_243',type,(
    '#skF_243': $i > $i )).

tff('#skF_241',type,(
    '#skF_241': $i > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(o_2_0_wellord1,type,(
    o_2_0_wellord1: ( $i * $i ) > $i )).

tff('#skF_542',type,(
    '#skF_542': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_226',type,(
    '#skF_226': ( $i * $i ) > $i )).

tff('#skF_177',type,(
    '#skF_177': ( $i * $i ) > $i )).

tff('#skF_426',type,(
    '#skF_426': $i > $i )).

tff('#skF_120',type,(
    '#skF_120': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_102',type,(
    '#skF_102': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_402',type,(
    '#skF_402': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_105',type,(
    '#skF_105': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_447',type,(
    '#skF_447': $i > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff('#skF_569',type,(
    '#skF_569': ( $i * $i ) > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_214',type,(
    '#skF_214': $i > $i )).

tff('#skF_135',type,(
    '#skF_135': $i )).

tff('#skF_613',type,(
    '#skF_613': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_122',type,(
    '#skF_122': ( $i * ( $i * $i ) ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_444',type,(
    '#skF_444': $i > $i )).

tff('#skF_506',type,(
    '#skF_506': $i > $i )).

tff('#skF_570',type,(
    '#skF_570': $i > $i )).

tff(o_2_0_relat_1,type,(
    o_2_0_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_270',type,(
    '#skF_270': ( $i * $i ) > $i )).

tff('#skF_262',type,(
    '#skF_262': ( $i * $i ) > $i )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * ( $i * $i ) ) > $o )).

tff(v3_funct_1,type,(
    v3_funct_1: $i > $o )).

tff('#skF_381',type,(
    '#skF_381': ( $i * $i ) > $i )).

tff('#skF_345',type,(
    '#skF_345': ( $i * ( $i * $i ) ) > $i )).

tff(o_1_1_relat_1,type,(
    o_1_1_relat_1: $i > $i )).

tff('#skF_574',type,(
    '#skF_574': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_304',type,(
    '#skF_304': $i > $i )).

tff('#skF_536',type,(
    '#skF_536': $i > $i )).

tff('#skF_273',type,(
    '#skF_273': $i > $i )).

tff('#skF_415',type,(
    '#skF_415': ( $i * $i ) > $i )).

tff('#skF_375',type,(
    '#skF_375': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_603',type,(
    '#skF_603': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_591',type,(
    '#skF_591': ( $i * ( $i * $i ) ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_258',type,(
    '#skF_258': $i > $i )).

tff('#skF_227',type,(
    '#skF_227': $i > $i )).

tff('#skF_147',type,(
    '#skF_147': ( $i * $i ) > $i )).

tff(o_1_2_relat_1,type,(
    o_1_2_relat_1: $i > $i )).

tff('#skF_293',type,(
    '#skF_293': $i > $i )).

tff('#skF_259',type,(
    '#skF_259': ( $i * $i ) > $i )).

tff('#skF_463',type,(
    '#skF_463': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_516',type,(
    '#skF_516': ( $i * $i ) > $i )).

tff('#skF_575',type,(
    '#skF_575': ( $i * ( $i * $i ) ) > $i )).

tff(o_3_0_wellord2,type,(
    o_3_0_wellord2: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_312',type,(
    '#skF_312': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_601',type,(
    '#skF_601': ( $i * ( $i * $i ) ) > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff('#skF_213',type,(
    '#skF_213': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_132',type,(
    '#skF_132': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_124',type,(
    '#skF_124': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_295',type,(
    '#skF_295': $i > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(k19_mcart_1,type,(
    k19_mcart_1: $i > $i )).

tff('#skF_529',type,(
    '#skF_529': $i > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_597',type,(
    '#skF_597': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_237',type,(
    '#skF_237': $i > $i )).

tff('#skF_590',type,(
    '#skF_590': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_483',type,(
    '#skF_483': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_210',type,(
    '#skF_210': ( $i * $i ) > $i )).

tff('#skF_250',type,(
    '#skF_250': ( $i * $i ) > $i )).

tff('#skF_609',type,(
    '#skF_609': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_360',type,(
    '#skF_360': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(o_3_1_funct_2,type,(
    o_3_1_funct_2: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_344',type,(
    '#skF_344': ( $i * $i ) > $i )).

tff('#skF_439',type,(
    '#skF_439': ( $i * $i ) > $i )).

tff('#skF_524',type,(
    '#skF_524': $i > $i )).

tff('#skF_394',type,(
    '#skF_394': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff('#skF_543',type,(
    '#skF_543': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_438',type,(
    '#skF_438': $i > $i )).

tff('#skF_283',type,(
    '#skF_283': $i > $i )).

tff('#skF_129',type,(
    '#skF_129': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_374',type,(
    '#skF_374': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_150',type,(
    '#skF_150': ( $i * ( $i * $i ) ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_553',type,(
    '#skF_553': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_346',type,(
    '#skF_346': ( $i * $i ) > $i )).

tff('#skF_445',type,(
    '#skF_445': $i > $i )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_98',type,(
    '#skF_98': ( $i * $i ) > $i )).

tff('#skF_441',type,(
    '#skF_441': $i > $i )).

tff('#skF_134',type,(
    '#skF_134': $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_83',type,(
    '#skF_83': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_587',type,(
    '#skF_587': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_440',type,(
    '#skF_440': ( $i * $i ) > $i )).

tff('#skF_139',type,(
    '#skF_139': $i > $i )).

tff('#skF_351',type,(
    '#skF_351': ( $i * $i ) > $i )).

tff('#skF_239',type,(
    '#skF_239': $i > $i )).

tff(k15_mcart_1,type,(
    k15_mcart_1: $i > $i )).

tff('#skF_282',type,(
    '#skF_282': $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_158',type,(
    '#skF_158': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_429',type,(
    '#skF_429': $i > $i )).

tff('#skF_450',type,(
    '#skF_450': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_194',type,(
    '#skF_194': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_350',type,(
    '#skF_350': ( $i * $i ) > $i )).

tff('#skF_245',type,(
    '#skF_245': ( $i * ( $i * $i ) ) > $i )).

tff(o_1_3_relat_1,type,(
    o_1_3_relat_1: $i > $i )).

tff('#skF_546',type,(
    '#skF_546': ( $i * ( $i * $i ) ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * ( $i * ( $i * $i ) ) ) > $o )).

tff('#skF_256',type,(
    '#skF_256': ( $i * $i ) > $i )).

tff('#skF_475',type,(
    '#skF_475': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_407',type,(
    '#skF_407': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_323',type,(
    '#skF_323': $i > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff('#skF_310',type,(
    '#skF_310': $i > $i )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff('#skF_528',type,(
    '#skF_528': $i > $i )).

tff('#skF_505',type,(
    '#skF_505': $i )).

tff('#skF_271',type,(
    '#skF_271': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff('#skF_246',type,(
    '#skF_246': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_109',type,(
    '#skF_109': ( $i * $i ) > $i )).

tff('#skF_382',type,(
    '#skF_382': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(f_15222,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

tff(f_15190,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(c_8262,plain,(
    v1_finset_1('#skF_618') ),
    inference(cnfTransformation,[status(thm)],[f_15222])).

tff(c_16018,plain,(
    ! [A_11333,B_11334] :
      ( v1_finset_1(k3_xboole_0(A_11333,B_11334))
      | ~ v1_finset_1(B_11334) ) ),
    inference(cnfTransformation,[status(thm)],[f_15190])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8260,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_618','#skF_619')) ),
    inference(cnfTransformation,[status(thm)],[f_15222])).

tff(c_8638,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_619','#skF_618')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8260])).

tff(c_16021,plain,(
    ~ v1_finset_1('#skF_618') ),
    inference(resolution,[status(thm)],[c_16018,c_8638])).

tff(c_16040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8262,c_16021])).
%------------------------------------------------------------------------------

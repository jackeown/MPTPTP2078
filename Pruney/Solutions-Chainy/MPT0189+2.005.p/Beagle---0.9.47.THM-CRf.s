%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 55.94s
% Output     : CNFRefutation 56.02s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 878 expanded)
%              Number of leaves         :   25 ( 306 expanded)
%              Depth                    :   26
%              Number of atoms          :   92 ( 862 expanded)
%              Number of equality atoms :   91 ( 861 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,D_6,C_5] : k2_enumset1(A_3,B_4,D_6,C_5) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_706,plain,(
    ! [B_115,A_117,E_116,C_119,D_118] : k2_xboole_0(k2_enumset1(A_117,B_115,C_119,D_118),k1_tarski(E_116)) = k3_enumset1(A_117,B_115,C_119,D_118,E_116) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_742,plain,(
    ! [A_40,B_41,C_42,E_116] : k3_enumset1(A_40,A_40,B_41,C_42,E_116) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(E_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_706])).

tff(c_746,plain,(
    ! [A_40,B_41,C_42,E_116] : k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(E_116)) = k2_enumset1(A_40,B_41,C_42,E_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_742])).

tff(c_140,plain,(
    ! [A_77,C_78,D_79,B_80] : k2_enumset1(A_77,C_78,D_79,B_80) = k2_enumset1(A_77,B_80,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,B_41,C_42,A_40) = k1_enumset1(A_40,B_41,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_140])).

tff(c_2739,plain,(
    ! [D_226,E_228,C_229,A_227,B_230] : k2_xboole_0(k2_enumset1(A_227,B_230,D_226,C_229),k1_tarski(E_228)) = k3_enumset1(A_227,B_230,C_229,D_226,E_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_706])).

tff(c_2790,plain,(
    ! [A_40,B_41,C_42,E_228] : k3_enumset1(A_40,B_41,A_40,C_42,E_228) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(E_228)) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2739])).

tff(c_3185,plain,(
    ! [A_251,B_252,C_253,E_254] : k3_enumset1(A_251,B_252,A_251,C_253,E_254) = k2_enumset1(A_251,B_252,C_253,E_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_2790])).

tff(c_574,plain,(
    ! [A_108,E_111,B_109,D_110,C_107] : k2_xboole_0(k1_tarski(A_108),k2_enumset1(B_109,C_107,D_110,E_111)) = k3_enumset1(A_108,B_109,C_107,D_110,E_111) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1690,plain,(
    ! [D_181,B_185,A_182,C_184,A_183] : k2_xboole_0(k1_tarski(A_183),k2_enumset1(A_182,B_185,C_184,D_181)) = k3_enumset1(A_183,A_182,B_185,D_181,C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_574])).

tff(c_8,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_tarski(A_11),k2_enumset1(B_12,C_13,D_14,E_15)) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1696,plain,(
    ! [D_181,B_185,A_182,C_184,A_183] : k3_enumset1(A_183,A_182,B_185,D_181,C_184) = k3_enumset1(A_183,A_182,B_185,C_184,D_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_1690,c_8])).

tff(c_3206,plain,(
    ! [A_251,B_252,E_254,C_253] : k3_enumset1(A_251,B_252,A_251,E_254,C_253) = k2_enumset1(A_251,B_252,C_253,E_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_3185,c_1696])).

tff(c_18,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1252,plain,(
    ! [A_157,B_158,C_159,E_160] : k2_xboole_0(k1_enumset1(A_157,B_158,C_159),k1_tarski(E_160)) = k2_enumset1(A_157,B_158,C_159,E_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_742])).

tff(c_1270,plain,(
    ! [A_38,B_39,E_160] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(E_160)) = k2_enumset1(A_38,A_38,B_39,E_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1252])).

tff(c_1274,plain,(
    ! [A_38,B_39,E_160] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(E_160)) = k1_enumset1(A_38,B_39,E_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1270])).

tff(c_1478,plain,(
    ! [A_174,A_175,B_176,C_177] : k3_enumset1(A_174,A_175,A_175,B_176,C_177) = k2_xboole_0(k1_tarski(A_174),k1_enumset1(A_175,B_176,C_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_574])).

tff(c_10138,plain,(
    ! [A_381,A_382,B_383] : k3_enumset1(A_381,A_382,A_382,A_382,B_383) = k2_xboole_0(k1_tarski(A_381),k2_tarski(A_382,B_383)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1478])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1513,plain,(
    ! [B_44,C_45,D_46] : k2_xboole_0(k1_tarski(B_44),k1_enumset1(B_44,C_45,D_46)) = k2_enumset1(B_44,B_44,C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1478])).

tff(c_2687,plain,(
    ! [B_223,C_224,D_225] : k2_xboole_0(k1_tarski(B_223),k1_enumset1(B_223,C_224,D_225)) = k1_enumset1(B_223,C_224,D_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1513])).

tff(c_2733,plain,(
    ! [A_38,B_39] : k2_xboole_0(k1_tarski(A_38),k2_tarski(A_38,B_39)) = k1_enumset1(A_38,A_38,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2687])).

tff(c_2824,plain,(
    ! [A_231,B_232] : k2_xboole_0(k1_tarski(A_231),k2_tarski(A_231,B_232)) = k2_tarski(A_231,B_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2733])).

tff(c_2833,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k2_tarski(B_2,A_1)) = k2_tarski(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2824])).

tff(c_10490,plain,(
    ! [B_384,A_385] : k3_enumset1(B_384,A_385,A_385,A_385,B_384) = k2_tarski(B_384,A_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_10138,c_2833])).

tff(c_1987,plain,(
    ! [C_196,A_197,A_198,D_194,B_195] : k2_xboole_0(k1_tarski(A_198),k2_enumset1(A_197,B_195,C_196,D_194)) = k3_enumset1(A_198,A_197,C_196,D_194,B_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_574])).

tff(c_1996,plain,(
    ! [C_196,A_197,A_198,D_194,B_195] : k3_enumset1(A_198,A_197,C_196,D_194,B_195) = k3_enumset1(A_198,A_197,B_195,C_196,D_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_1987,c_8])).

tff(c_10808,plain,(
    ! [B_386,A_387] : k3_enumset1(B_386,A_387,B_386,A_387,A_387) = k2_tarski(B_386,A_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_10490,c_1996])).

tff(c_2535,plain,(
    ! [E_216,D_212,A_215,C_214,B_213] : k2_xboole_0(k2_enumset1(A_215,C_214,D_212,B_213),k1_tarski(E_216)) = k3_enumset1(A_215,B_213,C_214,D_212,E_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_706])).

tff(c_2598,plain,(
    ! [A_40,C_42,B_41,E_216] : k3_enumset1(A_40,C_42,A_40,B_41,E_216) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(E_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2535])).

tff(c_2610,plain,(
    ! [A_40,C_42,B_41,E_216] : k3_enumset1(A_40,C_42,A_40,B_41,E_216) = k2_enumset1(A_40,B_41,C_42,E_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_2598])).

tff(c_11161,plain,(
    ! [B_388,A_389] : k2_enumset1(B_388,A_389,A_389,A_389) = k2_tarski(B_388,A_389) ),
    inference(superposition,[status(thm),theory(equality)],[c_10808,c_2610])).

tff(c_733,plain,(
    ! [D_10,A_7,E_116,B_8,C_9] : k2_xboole_0(k2_enumset1(A_7,B_8,C_9,D_10),k1_tarski(E_116)) = k3_enumset1(A_7,C_9,D_10,B_8,E_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_706])).

tff(c_11181,plain,(
    ! [B_388,A_389,E_116] : k3_enumset1(B_388,A_389,A_389,A_389,E_116) = k2_xboole_0(k2_tarski(B_388,A_389),k1_tarski(E_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11161,c_733])).

tff(c_11301,plain,(
    ! [B_388,A_389,E_116] : k3_enumset1(B_388,A_389,A_389,A_389,E_116) = k1_enumset1(B_388,A_389,E_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_11181])).

tff(c_1525,plain,(
    ! [A_174,A_38,B_39] : k3_enumset1(A_174,A_38,A_38,A_38,B_39) = k2_xboole_0(k1_tarski(A_174),k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1478])).

tff(c_26624,plain,(
    ! [A_174,A_38,B_39] : k2_xboole_0(k1_tarski(A_174),k2_tarski(A_38,B_39)) = k1_enumset1(A_174,A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_1525])).

tff(c_1275,plain,(
    ! [A_161,B_162,E_163] : k2_xboole_0(k2_tarski(A_161,B_162),k1_tarski(E_163)) = k1_enumset1(A_161,B_162,E_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1270])).

tff(c_1294,plain,(
    ! [B_164,A_165,E_166] : k2_xboole_0(k2_tarski(B_164,A_165),k1_tarski(E_166)) = k1_enumset1(A_165,B_164,E_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1275])).

tff(c_1330,plain,(
    ! [B_169,A_170,E_171] : k1_enumset1(B_169,A_170,E_171) = k1_enumset1(A_170,B_169,E_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1274])).

tff(c_93,plain,(
    ! [A_73,B_74,D_75,C_76] : k2_enumset1(A_73,B_74,D_75,C_76) = k2_enumset1(A_73,B_74,C_76,D_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_207,plain,(
    ! [B_81,D_82,C_83] : k2_enumset1(B_81,B_81,D_82,C_83) = k1_enumset1(B_81,C_83,D_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_254,plain,(
    ! [B_84,D_85,C_86] : k1_enumset1(B_84,D_85,C_86) = k1_enumset1(B_84,C_86,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_20])).

tff(c_270,plain,(
    ! [C_86,D_85] : k1_enumset1(C_86,D_85,C_86) = k2_tarski(C_86,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_18])).

tff(c_1364,plain,(
    ! [B_169,E_171] : k1_enumset1(B_169,E_171,E_171) = k2_tarski(E_171,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_270])).

tff(c_1419,plain,(
    ! [B_172,E_173] : k1_enumset1(B_172,E_173,E_173) = k2_tarski(E_173,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_270])).

tff(c_1431,plain,(
    ! [E_173,B_172,E_116] : k2_xboole_0(k2_tarski(E_173,B_172),k1_tarski(E_116)) = k2_enumset1(B_172,E_173,E_173,E_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_746])).

tff(c_2103,plain,(
    ! [B_203,E_204,E_205] : k2_enumset1(B_203,E_204,E_204,E_205) = k1_enumset1(E_204,B_203,E_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1431])).

tff(c_31772,plain,(
    ! [A_532,B_533,E_534,E_535] : k3_enumset1(A_532,B_533,E_534,E_534,E_535) = k2_xboole_0(k1_tarski(A_532),k1_enumset1(E_534,B_533,E_535)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_8])).

tff(c_32355,plain,(
    ! [A_532,E_171,B_169] : k3_enumset1(A_532,E_171,B_169,B_169,E_171) = k2_xboole_0(k1_tarski(A_532),k2_tarski(E_171,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_31772])).

tff(c_32493,plain,(
    ! [A_536,E_537,B_538] : k3_enumset1(A_536,E_537,B_538,B_538,E_537) = k1_enumset1(A_536,E_537,B_538) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26624,c_32355])).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k1_tarski(E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5181,plain,(
    ! [D_317,C_318,B_314,A_316,E_315] : k3_enumset1(A_316,B_314,D_317,C_318,E_315) = k3_enumset1(A_316,B_314,C_318,D_317,E_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2739])).

tff(c_5309,plain,(
    ! [B_314,C_318,D_317,E_315] : k3_enumset1(B_314,B_314,C_318,D_317,E_315) = k2_enumset1(B_314,D_317,C_318,E_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_5181,c_22])).

tff(c_32683,plain,(
    ! [E_537,B_538] : k2_enumset1(E_537,B_538,B_538,E_537) = k1_enumset1(E_537,E_537,B_538) ),
    inference(superposition,[status(thm),theory(equality)],[c_32493,c_5309])).

tff(c_33713,plain,(
    ! [E_543,B_544] : k2_enumset1(E_543,B_544,B_544,E_543) = k2_tarski(E_543,B_544) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32683])).

tff(c_33773,plain,(
    ! [E_543,B_544,E_116] : k3_enumset1(E_543,B_544,E_543,B_544,E_116) = k2_xboole_0(k2_tarski(E_543,B_544),k1_tarski(E_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33713,c_733])).

tff(c_39069,plain,(
    ! [E_568,B_569,E_570] : k3_enumset1(E_568,B_569,E_568,B_569,E_570) = k1_enumset1(E_568,B_569,E_570) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_33773])).

tff(c_39779,plain,(
    ! [E_571,B_572,E_573] : k2_enumset1(E_571,B_572,B_572,E_573) = k1_enumset1(E_571,B_572,E_573) ),
    inference(superposition,[status(thm),theory(equality)],[c_39069,c_2610])).

tff(c_39893,plain,(
    ! [A_11,E_571,B_572,E_573] : k3_enumset1(A_11,E_571,B_572,B_572,E_573) = k2_xboole_0(k1_tarski(A_11),k1_enumset1(E_571,B_572,E_573)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39779,c_8])).

tff(c_1468,plain,(
    ! [B_172,E_173,E_116] : k2_enumset1(B_172,E_173,E_173,E_116) = k1_enumset1(E_173,B_172,E_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1431])).

tff(c_2819,plain,(
    ! [A_40,B_41,C_42,E_228] : k3_enumset1(A_40,B_41,A_40,C_42,E_228) = k2_enumset1(A_40,B_41,C_42,E_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_2790])).

tff(c_604,plain,(
    ! [A_3,A_108,D_6,C_5,B_4] : k2_xboole_0(k1_tarski(A_108),k2_enumset1(A_3,B_4,C_5,D_6)) = k3_enumset1(A_108,A_3,B_4,D_6,C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_574])).

tff(c_11720,plain,(
    ! [D_396,A_397,B_400,A_398,C_399] : k3_enumset1(A_398,A_397,C_399,D_396,B_400) = k3_enumset1(A_398,A_397,B_400,D_396,C_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1987])).

tff(c_90757,plain,(
    ! [A_999,B_1000,E_1001,C_1002] : k3_enumset1(A_999,B_1000,E_1001,C_1002,A_999) = k2_enumset1(A_999,B_1000,C_1002,E_1001) ),
    inference(superposition,[status(thm),theory(equality)],[c_2819,c_11720])).

tff(c_2029,plain,(
    ! [A_198,A_40,C_42,B_41] : k3_enumset1(A_198,A_40,C_42,A_40,B_41) = k2_xboole_0(k1_tarski(A_198),k1_enumset1(A_40,B_41,C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_1987])).

tff(c_91003,plain,(
    ! [A_999,C_1002,E_1001] : k2_xboole_0(k1_tarski(A_999),k1_enumset1(C_1002,A_999,E_1001)) = k2_enumset1(A_999,C_1002,C_1002,E_1001) ),
    inference(superposition,[status(thm),theory(equality)],[c_90757,c_2029])).

tff(c_191481,plain,(
    ! [A_1443,C_1444,E_1445] : k2_xboole_0(k1_tarski(A_1443),k1_enumset1(C_1444,A_1443,E_1445)) = k1_enumset1(C_1444,A_1443,E_1445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_91003])).

tff(c_227547,plain,(
    ! [B_1580,E_1581,E_1582] : k3_enumset1(B_1580,E_1581,B_1580,B_1580,E_1582) = k1_enumset1(E_1581,B_1580,E_1582) ),
    inference(superposition,[status(thm),theory(equality)],[c_39893,c_191481])).

tff(c_233718,plain,(
    ! [E_1602,B_1603,C_1604] : k2_enumset1(E_1602,B_1603,C_1604,E_1602) = k1_enumset1(B_1603,E_1602,C_1604) ),
    inference(superposition,[status(thm),theory(equality)],[c_3206,c_227547])).

tff(c_730,plain,(
    ! [D_10,A_7,E_116,B_8,C_9] : k2_xboole_0(k2_enumset1(A_7,C_9,D_10,B_8),k1_tarski(E_116)) = k3_enumset1(A_7,B_8,C_9,D_10,E_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_706])).

tff(c_233920,plain,(
    ! [E_1602,B_1603,C_1604,E_116] : k3_enumset1(E_1602,E_1602,B_1603,C_1604,E_116) = k2_xboole_0(k1_enumset1(B_1603,E_1602,C_1604),k1_tarski(E_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_233718,c_730])).

tff(c_234198,plain,(
    ! [E_1602,B_1603,C_1604,E_116] : k2_enumset1(E_1602,B_1603,C_1604,E_116) = k2_enumset1(B_1603,E_1602,C_1604,E_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_22,c_233920])).

tff(c_30,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_30])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_269409,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234198,c_234198,c_32])).

tff(c_269412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_4,c_6,c_269409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 55.94/45.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.94/45.52  
% 55.94/45.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.94/45.53  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 55.94/45.53  
% 55.94/45.53  %Foreground sorts:
% 55.94/45.53  
% 55.94/45.53  
% 55.94/45.53  %Background operators:
% 55.94/45.53  
% 55.94/45.53  
% 55.94/45.53  %Foreground operators:
% 55.94/45.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 55.94/45.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 55.94/45.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 55.94/45.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 55.94/45.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 55.94/45.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 55.94/45.53  tff('#skF_2', type, '#skF_2': $i).
% 55.94/45.53  tff('#skF_3', type, '#skF_3': $i).
% 55.94/45.53  tff('#skF_1', type, '#skF_1': $i).
% 55.94/45.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 55.94/45.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 55.94/45.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 55.94/45.53  tff('#skF_4', type, '#skF_4': $i).
% 55.94/45.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 55.94/45.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 55.94/45.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 55.94/45.53  
% 56.02/45.55  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 56.02/45.55  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 56.02/45.55  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 56.02/45.55  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 56.02/45.55  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 56.02/45.55  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 56.02/45.55  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 56.02/45.55  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 56.02/45.55  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 56.02/45.55  tff(c_4, plain, (![A_3, B_4, D_6, C_5]: (k2_enumset1(A_3, B_4, D_6, C_5)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.02/45.55  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.02/45.55  tff(c_22, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.02/45.55  tff(c_20, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.02/45.55  tff(c_706, plain, (![B_115, A_117, E_116, C_119, D_118]: (k2_xboole_0(k2_enumset1(A_117, B_115, C_119, D_118), k1_tarski(E_116))=k3_enumset1(A_117, B_115, C_119, D_118, E_116))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.02/45.55  tff(c_742, plain, (![A_40, B_41, C_42, E_116]: (k3_enumset1(A_40, A_40, B_41, C_42, E_116)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(E_116)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_706])).
% 56.02/45.55  tff(c_746, plain, (![A_40, B_41, C_42, E_116]: (k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(E_116))=k2_enumset1(A_40, B_41, C_42, E_116))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_742])).
% 56.02/45.55  tff(c_140, plain, (![A_77, C_78, D_79, B_80]: (k2_enumset1(A_77, C_78, D_79, B_80)=k2_enumset1(A_77, B_80, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.02/45.55  tff(c_202, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, B_41, C_42, A_40)=k1_enumset1(A_40, B_41, C_42))), inference(superposition, [status(thm), theory('equality')], [c_20, c_140])).
% 56.02/45.55  tff(c_2739, plain, (![D_226, E_228, C_229, A_227, B_230]: (k2_xboole_0(k2_enumset1(A_227, B_230, D_226, C_229), k1_tarski(E_228))=k3_enumset1(A_227, B_230, C_229, D_226, E_228))), inference(superposition, [status(thm), theory('equality')], [c_4, c_706])).
% 56.02/45.55  tff(c_2790, plain, (![A_40, B_41, C_42, E_228]: (k3_enumset1(A_40, B_41, A_40, C_42, E_228)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(E_228)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_2739])).
% 56.02/45.55  tff(c_3185, plain, (![A_251, B_252, C_253, E_254]: (k3_enumset1(A_251, B_252, A_251, C_253, E_254)=k2_enumset1(A_251, B_252, C_253, E_254))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_2790])).
% 56.02/45.55  tff(c_574, plain, (![A_108, E_111, B_109, D_110, C_107]: (k2_xboole_0(k1_tarski(A_108), k2_enumset1(B_109, C_107, D_110, E_111))=k3_enumset1(A_108, B_109, C_107, D_110, E_111))), inference(cnfTransformation, [status(thm)], [f_33])).
% 56.02/45.55  tff(c_1690, plain, (![D_181, B_185, A_182, C_184, A_183]: (k2_xboole_0(k1_tarski(A_183), k2_enumset1(A_182, B_185, C_184, D_181))=k3_enumset1(A_183, A_182, B_185, D_181, C_184))), inference(superposition, [status(thm), theory('equality')], [c_4, c_574])).
% 56.02/45.55  tff(c_8, plain, (![D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_enumset1(B_12, C_13, D_14, E_15))=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 56.02/45.55  tff(c_1696, plain, (![D_181, B_185, A_182, C_184, A_183]: (k3_enumset1(A_183, A_182, B_185, D_181, C_184)=k3_enumset1(A_183, A_182, B_185, C_184, D_181))), inference(superposition, [status(thm), theory('equality')], [c_1690, c_8])).
% 56.02/45.55  tff(c_3206, plain, (![A_251, B_252, E_254, C_253]: (k3_enumset1(A_251, B_252, A_251, E_254, C_253)=k2_enumset1(A_251, B_252, C_253, E_254))), inference(superposition, [status(thm), theory('equality')], [c_3185, c_1696])).
% 56.02/45.55  tff(c_18, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 56.02/45.55  tff(c_1252, plain, (![A_157, B_158, C_159, E_160]: (k2_xboole_0(k1_enumset1(A_157, B_158, C_159), k1_tarski(E_160))=k2_enumset1(A_157, B_158, C_159, E_160))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_742])).
% 56.02/45.55  tff(c_1270, plain, (![A_38, B_39, E_160]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(E_160))=k2_enumset1(A_38, A_38, B_39, E_160))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1252])).
% 56.02/45.55  tff(c_1274, plain, (![A_38, B_39, E_160]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(E_160))=k1_enumset1(A_38, B_39, E_160))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1270])).
% 56.02/45.55  tff(c_1478, plain, (![A_174, A_175, B_176, C_177]: (k3_enumset1(A_174, A_175, A_175, B_176, C_177)=k2_xboole_0(k1_tarski(A_174), k1_enumset1(A_175, B_176, C_177)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_574])).
% 56.02/45.55  tff(c_10138, plain, (![A_381, A_382, B_383]: (k3_enumset1(A_381, A_382, A_382, A_382, B_383)=k2_xboole_0(k1_tarski(A_381), k2_tarski(A_382, B_383)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1478])).
% 56.02/45.55  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 56.02/45.55  tff(c_1513, plain, (![B_44, C_45, D_46]: (k2_xboole_0(k1_tarski(B_44), k1_enumset1(B_44, C_45, D_46))=k2_enumset1(B_44, B_44, C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1478])).
% 56.02/45.55  tff(c_2687, plain, (![B_223, C_224, D_225]: (k2_xboole_0(k1_tarski(B_223), k1_enumset1(B_223, C_224, D_225))=k1_enumset1(B_223, C_224, D_225))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1513])).
% 56.02/45.55  tff(c_2733, plain, (![A_38, B_39]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(A_38, B_39))=k1_enumset1(A_38, A_38, B_39))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2687])).
% 56.02/45.55  tff(c_2824, plain, (![A_231, B_232]: (k2_xboole_0(k1_tarski(A_231), k2_tarski(A_231, B_232))=k2_tarski(A_231, B_232))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2733])).
% 56.02/45.55  tff(c_2833, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k2_tarski(B_2, A_1))=k2_tarski(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2824])).
% 56.02/45.55  tff(c_10490, plain, (![B_384, A_385]: (k3_enumset1(B_384, A_385, A_385, A_385, B_384)=k2_tarski(B_384, A_385))), inference(superposition, [status(thm), theory('equality')], [c_10138, c_2833])).
% 56.02/45.55  tff(c_1987, plain, (![C_196, A_197, A_198, D_194, B_195]: (k2_xboole_0(k1_tarski(A_198), k2_enumset1(A_197, B_195, C_196, D_194))=k3_enumset1(A_198, A_197, C_196, D_194, B_195))), inference(superposition, [status(thm), theory('equality')], [c_6, c_574])).
% 56.02/45.55  tff(c_1996, plain, (![C_196, A_197, A_198, D_194, B_195]: (k3_enumset1(A_198, A_197, C_196, D_194, B_195)=k3_enumset1(A_198, A_197, B_195, C_196, D_194))), inference(superposition, [status(thm), theory('equality')], [c_1987, c_8])).
% 56.02/45.55  tff(c_10808, plain, (![B_386, A_387]: (k3_enumset1(B_386, A_387, B_386, A_387, A_387)=k2_tarski(B_386, A_387))), inference(superposition, [status(thm), theory('equality')], [c_10490, c_1996])).
% 56.02/45.55  tff(c_2535, plain, (![E_216, D_212, A_215, C_214, B_213]: (k2_xboole_0(k2_enumset1(A_215, C_214, D_212, B_213), k1_tarski(E_216))=k3_enumset1(A_215, B_213, C_214, D_212, E_216))), inference(superposition, [status(thm), theory('equality')], [c_6, c_706])).
% 56.02/45.55  tff(c_2598, plain, (![A_40, C_42, B_41, E_216]: (k3_enumset1(A_40, C_42, A_40, B_41, E_216)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(E_216)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2535])).
% 56.02/45.55  tff(c_2610, plain, (![A_40, C_42, B_41, E_216]: (k3_enumset1(A_40, C_42, A_40, B_41, E_216)=k2_enumset1(A_40, B_41, C_42, E_216))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_2598])).
% 56.02/45.55  tff(c_11161, plain, (![B_388, A_389]: (k2_enumset1(B_388, A_389, A_389, A_389)=k2_tarski(B_388, A_389))), inference(superposition, [status(thm), theory('equality')], [c_10808, c_2610])).
% 56.02/45.55  tff(c_733, plain, (![D_10, A_7, E_116, B_8, C_9]: (k2_xboole_0(k2_enumset1(A_7, B_8, C_9, D_10), k1_tarski(E_116))=k3_enumset1(A_7, C_9, D_10, B_8, E_116))), inference(superposition, [status(thm), theory('equality')], [c_6, c_706])).
% 56.02/45.55  tff(c_11181, plain, (![B_388, A_389, E_116]: (k3_enumset1(B_388, A_389, A_389, A_389, E_116)=k2_xboole_0(k2_tarski(B_388, A_389), k1_tarski(E_116)))), inference(superposition, [status(thm), theory('equality')], [c_11161, c_733])).
% 56.02/45.55  tff(c_11301, plain, (![B_388, A_389, E_116]: (k3_enumset1(B_388, A_389, A_389, A_389, E_116)=k1_enumset1(B_388, A_389, E_116))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_11181])).
% 56.02/45.55  tff(c_1525, plain, (![A_174, A_38, B_39]: (k3_enumset1(A_174, A_38, A_38, A_38, B_39)=k2_xboole_0(k1_tarski(A_174), k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1478])).
% 56.02/45.55  tff(c_26624, plain, (![A_174, A_38, B_39]: (k2_xboole_0(k1_tarski(A_174), k2_tarski(A_38, B_39))=k1_enumset1(A_174, A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_1525])).
% 56.02/45.55  tff(c_1275, plain, (![A_161, B_162, E_163]: (k2_xboole_0(k2_tarski(A_161, B_162), k1_tarski(E_163))=k1_enumset1(A_161, B_162, E_163))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1270])).
% 56.02/45.55  tff(c_1294, plain, (![B_164, A_165, E_166]: (k2_xboole_0(k2_tarski(B_164, A_165), k1_tarski(E_166))=k1_enumset1(A_165, B_164, E_166))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1275])).
% 56.02/45.55  tff(c_1330, plain, (![B_169, A_170, E_171]: (k1_enumset1(B_169, A_170, E_171)=k1_enumset1(A_170, B_169, E_171))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1274])).
% 56.02/45.55  tff(c_93, plain, (![A_73, B_74, D_75, C_76]: (k2_enumset1(A_73, B_74, D_75, C_76)=k2_enumset1(A_73, B_74, C_76, D_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.02/45.55  tff(c_207, plain, (![B_81, D_82, C_83]: (k2_enumset1(B_81, B_81, D_82, C_83)=k1_enumset1(B_81, C_83, D_82))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 56.02/45.55  tff(c_254, plain, (![B_84, D_85, C_86]: (k1_enumset1(B_84, D_85, C_86)=k1_enumset1(B_84, C_86, D_85))), inference(superposition, [status(thm), theory('equality')], [c_207, c_20])).
% 56.02/45.55  tff(c_270, plain, (![C_86, D_85]: (k1_enumset1(C_86, D_85, C_86)=k2_tarski(C_86, D_85))), inference(superposition, [status(thm), theory('equality')], [c_254, c_18])).
% 56.02/45.55  tff(c_1364, plain, (![B_169, E_171]: (k1_enumset1(B_169, E_171, E_171)=k2_tarski(E_171, B_169))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_270])).
% 56.02/45.55  tff(c_1419, plain, (![B_172, E_173]: (k1_enumset1(B_172, E_173, E_173)=k2_tarski(E_173, B_172))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_270])).
% 56.02/45.55  tff(c_1431, plain, (![E_173, B_172, E_116]: (k2_xboole_0(k2_tarski(E_173, B_172), k1_tarski(E_116))=k2_enumset1(B_172, E_173, E_173, E_116))), inference(superposition, [status(thm), theory('equality')], [c_1419, c_746])).
% 56.02/45.55  tff(c_2103, plain, (![B_203, E_204, E_205]: (k2_enumset1(B_203, E_204, E_204, E_205)=k1_enumset1(E_204, B_203, E_205))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1431])).
% 56.02/45.55  tff(c_31772, plain, (![A_532, B_533, E_534, E_535]: (k3_enumset1(A_532, B_533, E_534, E_534, E_535)=k2_xboole_0(k1_tarski(A_532), k1_enumset1(E_534, B_533, E_535)))), inference(superposition, [status(thm), theory('equality')], [c_2103, c_8])).
% 56.02/45.55  tff(c_32355, plain, (![A_532, E_171, B_169]: (k3_enumset1(A_532, E_171, B_169, B_169, E_171)=k2_xboole_0(k1_tarski(A_532), k2_tarski(E_171, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_1364, c_31772])).
% 56.02/45.55  tff(c_32493, plain, (![A_536, E_537, B_538]: (k3_enumset1(A_536, E_537, B_538, B_538, E_537)=k1_enumset1(A_536, E_537, B_538))), inference(demodulation, [status(thm), theory('equality')], [c_26624, c_32355])).
% 56.02/45.55  tff(c_10, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k1_tarski(E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.02/45.55  tff(c_5181, plain, (![D_317, C_318, B_314, A_316, E_315]: (k3_enumset1(A_316, B_314, D_317, C_318, E_315)=k3_enumset1(A_316, B_314, C_318, D_317, E_315))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2739])).
% 56.02/45.55  tff(c_5309, plain, (![B_314, C_318, D_317, E_315]: (k3_enumset1(B_314, B_314, C_318, D_317, E_315)=k2_enumset1(B_314, D_317, C_318, E_315))), inference(superposition, [status(thm), theory('equality')], [c_5181, c_22])).
% 56.02/45.55  tff(c_32683, plain, (![E_537, B_538]: (k2_enumset1(E_537, B_538, B_538, E_537)=k1_enumset1(E_537, E_537, B_538))), inference(superposition, [status(thm), theory('equality')], [c_32493, c_5309])).
% 56.02/45.55  tff(c_33713, plain, (![E_543, B_544]: (k2_enumset1(E_543, B_544, B_544, E_543)=k2_tarski(E_543, B_544))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32683])).
% 56.02/45.55  tff(c_33773, plain, (![E_543, B_544, E_116]: (k3_enumset1(E_543, B_544, E_543, B_544, E_116)=k2_xboole_0(k2_tarski(E_543, B_544), k1_tarski(E_116)))), inference(superposition, [status(thm), theory('equality')], [c_33713, c_733])).
% 56.02/45.55  tff(c_39069, plain, (![E_568, B_569, E_570]: (k3_enumset1(E_568, B_569, E_568, B_569, E_570)=k1_enumset1(E_568, B_569, E_570))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_33773])).
% 56.02/45.55  tff(c_39779, plain, (![E_571, B_572, E_573]: (k2_enumset1(E_571, B_572, B_572, E_573)=k1_enumset1(E_571, B_572, E_573))), inference(superposition, [status(thm), theory('equality')], [c_39069, c_2610])).
% 56.02/45.55  tff(c_39893, plain, (![A_11, E_571, B_572, E_573]: (k3_enumset1(A_11, E_571, B_572, B_572, E_573)=k2_xboole_0(k1_tarski(A_11), k1_enumset1(E_571, B_572, E_573)))), inference(superposition, [status(thm), theory('equality')], [c_39779, c_8])).
% 56.02/45.55  tff(c_1468, plain, (![B_172, E_173, E_116]: (k2_enumset1(B_172, E_173, E_173, E_116)=k1_enumset1(E_173, B_172, E_116))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1431])).
% 56.02/45.55  tff(c_2819, plain, (![A_40, B_41, C_42, E_228]: (k3_enumset1(A_40, B_41, A_40, C_42, E_228)=k2_enumset1(A_40, B_41, C_42, E_228))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_2790])).
% 56.02/45.55  tff(c_604, plain, (![A_3, A_108, D_6, C_5, B_4]: (k2_xboole_0(k1_tarski(A_108), k2_enumset1(A_3, B_4, C_5, D_6))=k3_enumset1(A_108, A_3, B_4, D_6, C_5))), inference(superposition, [status(thm), theory('equality')], [c_4, c_574])).
% 56.02/45.55  tff(c_11720, plain, (![D_396, A_397, B_400, A_398, C_399]: (k3_enumset1(A_398, A_397, C_399, D_396, B_400)=k3_enumset1(A_398, A_397, B_400, D_396, C_399))), inference(superposition, [status(thm), theory('equality')], [c_604, c_1987])).
% 56.02/45.55  tff(c_90757, plain, (![A_999, B_1000, E_1001, C_1002]: (k3_enumset1(A_999, B_1000, E_1001, C_1002, A_999)=k2_enumset1(A_999, B_1000, C_1002, E_1001))), inference(superposition, [status(thm), theory('equality')], [c_2819, c_11720])).
% 56.02/45.55  tff(c_2029, plain, (![A_198, A_40, C_42, B_41]: (k3_enumset1(A_198, A_40, C_42, A_40, B_41)=k2_xboole_0(k1_tarski(A_198), k1_enumset1(A_40, B_41, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_1987])).
% 56.02/45.55  tff(c_91003, plain, (![A_999, C_1002, E_1001]: (k2_xboole_0(k1_tarski(A_999), k1_enumset1(C_1002, A_999, E_1001))=k2_enumset1(A_999, C_1002, C_1002, E_1001))), inference(superposition, [status(thm), theory('equality')], [c_90757, c_2029])).
% 56.02/45.55  tff(c_191481, plain, (![A_1443, C_1444, E_1445]: (k2_xboole_0(k1_tarski(A_1443), k1_enumset1(C_1444, A_1443, E_1445))=k1_enumset1(C_1444, A_1443, E_1445))), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_91003])).
% 56.02/45.55  tff(c_227547, plain, (![B_1580, E_1581, E_1582]: (k3_enumset1(B_1580, E_1581, B_1580, B_1580, E_1582)=k1_enumset1(E_1581, B_1580, E_1582))), inference(superposition, [status(thm), theory('equality')], [c_39893, c_191481])).
% 56.02/45.55  tff(c_233718, plain, (![E_1602, B_1603, C_1604]: (k2_enumset1(E_1602, B_1603, C_1604, E_1602)=k1_enumset1(B_1603, E_1602, C_1604))), inference(superposition, [status(thm), theory('equality')], [c_3206, c_227547])).
% 56.02/45.55  tff(c_730, plain, (![D_10, A_7, E_116, B_8, C_9]: (k2_xboole_0(k2_enumset1(A_7, C_9, D_10, B_8), k1_tarski(E_116))=k3_enumset1(A_7, B_8, C_9, D_10, E_116))), inference(superposition, [status(thm), theory('equality')], [c_6, c_706])).
% 56.02/45.55  tff(c_233920, plain, (![E_1602, B_1603, C_1604, E_116]: (k3_enumset1(E_1602, E_1602, B_1603, C_1604, E_116)=k2_xboole_0(k1_enumset1(B_1603, E_1602, C_1604), k1_tarski(E_116)))), inference(superposition, [status(thm), theory('equality')], [c_233718, c_730])).
% 56.02/45.55  tff(c_234198, plain, (![E_1602, B_1603, C_1604, E_116]: (k2_enumset1(E_1602, B_1603, C_1604, E_116)=k2_enumset1(B_1603, E_1602, C_1604, E_116))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_22, c_233920])).
% 56.02/45.55  tff(c_30, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 56.02/45.55  tff(c_31, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_30])).
% 56.02/45.55  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_31])).
% 56.02/45.55  tff(c_269409, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_234198, c_234198, c_32])).
% 56.02/45.55  tff(c_269412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_4, c_6, c_269409])).
% 56.02/45.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.02/45.55  
% 56.02/45.55  Inference rules
% 56.02/45.55  ----------------------
% 56.02/45.55  #Ref     : 0
% 56.02/45.55  #Sup     : 60343
% 56.02/45.55  #Fact    : 0
% 56.02/45.55  #Define  : 0
% 56.02/45.55  #Split   : 0
% 56.02/45.55  #Chain   : 0
% 56.02/45.55  #Close   : 0
% 56.02/45.55  
% 56.02/45.55  Ordering : KBO
% 56.02/45.55  
% 56.02/45.55  Simplification rules
% 56.02/45.55  ----------------------
% 56.02/45.55  #Subsume      : 8107
% 56.02/45.55  #Demod        : 101154
% 56.02/45.55  #Tautology    : 39219
% 56.02/45.55  #SimpNegUnit  : 0
% 56.02/45.55  #BackRed      : 11
% 56.02/45.55  
% 56.02/45.55  #Partial instantiations: 0
% 56.02/45.55  #Strategies tried      : 1
% 56.02/45.55  
% 56.02/45.55  Timing (in seconds)
% 56.02/45.55  ----------------------
% 56.02/45.55  Preprocessing        : 0.49
% 56.02/45.55  Parsing              : 0.25
% 56.02/45.55  CNF conversion       : 0.03
% 56.02/45.55  Main loop            : 44.12
% 56.02/45.55  Inferencing          : 5.78
% 56.02/45.55  Reduction            : 30.11
% 56.02/45.55  Demodulation         : 28.50
% 56.02/45.55  BG Simplification    : 0.53
% 56.02/45.55  Subsumption          : 6.05
% 56.02/45.55  Abstraction          : 1.14
% 56.02/45.55  MUC search           : 0.00
% 56.02/45.55  Cooper               : 0.00
% 56.02/45.55  Total                : 44.67
% 56.02/45.55  Index Insertion      : 0.00
% 56.02/45.55  Index Deletion       : 0.00
% 56.02/45.55  Index Matching       : 0.00
% 56.02/45.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

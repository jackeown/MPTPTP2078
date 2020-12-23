%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 196 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :   63 ( 177 expanded)
%              Number of equality atoms :   62 ( 176 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_20,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [B_88,F_86,C_91,D_87,E_89,A_90] : k2_xboole_0(k3_enumset1(A_90,B_88,C_91,D_87,E_89),k1_tarski(F_86)) = k4_enumset1(A_90,B_88,C_91,D_87,E_89,F_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [C_42,F_86,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,F_86) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(F_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_146,plain,(
    ! [C_42,F_86,A_40,D_43,B_41] : k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(F_86)) = k3_enumset1(A_40,B_41,C_42,D_43,F_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_18,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [C_95,A_92,B_96,F_94,D_93] : k2_xboole_0(k2_enumset1(A_92,B_96,C_95,D_93),k1_tarski(F_94)) = k3_enumset1(A_92,B_96,C_95,D_93,F_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_156,plain,(
    ! [A_37,B_38,C_39,F_94] : k3_enumset1(A_37,A_37,B_38,C_39,F_94) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(F_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_159,plain,(
    ! [A_37,B_38,C_39,F_94] : k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(F_94)) = k2_enumset1(A_37,B_38,C_39,F_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_16,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_97,B_98,C_99,F_100] : k2_xboole_0(k1_enumset1(A_97,B_98,C_99),k1_tarski(F_100)) = k2_enumset1(A_97,B_98,C_99,F_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_175,plain,(
    ! [A_35,B_36,F_100] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(F_100)) = k2_enumset1(A_35,A_35,B_36,F_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_160])).

tff(c_178,plain,(
    ! [A_35,B_36,F_100] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(F_100)) = k1_enumset1(A_35,B_36,F_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_8,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k3_enumset1(A_13,B_14,C_15,D_16,E_17),k1_tarski(F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [A_109,B_108,D_112,G_110,C_106,E_107,F_111] : k2_xboole_0(k3_enumset1(A_109,B_108,C_106,D_112,E_107),k2_tarski(F_111,G_110)) = k5_enumset1(A_109,B_108,C_106,D_112,E_107,F_111,G_110) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [A_109,B_108,D_112,A_34,C_106,E_107] : k5_enumset1(A_109,B_108,C_106,D_112,E_107,A_34,A_34) = k2_xboole_0(k3_enumset1(A_109,B_108,C_106,D_112,E_107),k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_201])).

tff(c_401,plain,(
    ! [E_149,B_148,C_152,D_151,A_150,A_147] : k5_enumset1(A_150,B_148,C_152,D_151,E_149,A_147,A_147) = k4_enumset1(A_150,B_148,C_152,D_151,E_149,A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_213])).

tff(c_24,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] : k5_enumset1(A_49,A_49,B_50,C_51,D_52,E_53,F_54) = k4_enumset1(A_49,B_50,C_51,D_52,E_53,F_54) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_408,plain,(
    ! [E_149,B_148,C_152,D_151,A_147] : k4_enumset1(B_148,C_152,D_151,E_149,A_147,A_147) = k4_enumset1(B_148,B_148,C_152,D_151,E_149,A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_24])).

tff(c_420,plain,(
    ! [B_155,E_156,A_153,D_154,C_157] : k4_enumset1(B_155,C_157,D_154,E_156,A_153,A_153) = k3_enumset1(B_155,C_157,D_154,E_156,A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_408])).

tff(c_430,plain,(
    ! [C_157,D_154,E_156,A_153] : k3_enumset1(C_157,D_154,E_156,A_153,A_153) = k3_enumset1(C_157,C_157,D_154,E_156,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_22])).

tff(c_443,plain,(
    ! [C_158,D_159,E_160,A_161] : k3_enumset1(C_158,D_159,E_160,A_161,A_161) = k2_enumset1(C_158,D_159,E_160,A_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_430])).

tff(c_462,plain,(
    ! [D_159,E_160,A_161] : k2_enumset1(D_159,E_160,A_161,A_161) = k2_enumset1(D_159,D_159,E_160,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_20])).

tff(c_514,plain,(
    ! [D_168,E_169,A_170] : k2_enumset1(D_168,E_169,A_170,A_170) = k1_enumset1(D_168,E_169,A_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_462])).

tff(c_539,plain,(
    ! [E_169,A_170] : k1_enumset1(E_169,E_169,A_170) = k1_enumset1(E_169,A_170,A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_18])).

tff(c_561,plain,(
    ! [E_171,A_172] : k1_enumset1(E_171,A_172,A_172) = k2_tarski(E_171,A_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_539])).

tff(c_570,plain,(
    ! [E_171,A_172,F_94] : k2_xboole_0(k2_tarski(E_171,A_172),k1_tarski(F_94)) = k2_enumset1(E_171,A_172,A_172,F_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_159])).

tff(c_883,plain,(
    ! [E_200,A_201,F_202] : k2_enumset1(E_200,A_201,A_201,F_202) = k1_enumset1(E_200,A_201,F_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_570])).

tff(c_919,plain,(
    ! [E_200,A_201,F_202,F_86] : k3_enumset1(E_200,A_201,A_201,F_202,F_86) = k2_xboole_0(k1_enumset1(E_200,A_201,F_202),k1_tarski(F_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_146])).

tff(c_1238,plain,(
    ! [E_222,A_223,F_224,F_225] : k3_enumset1(E_222,A_223,A_223,F_224,F_225) = k2_enumset1(E_222,A_223,F_224,F_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_919])).

tff(c_1272,plain,(
    ! [F_225,F_18,E_222,F_224,A_223] : k4_enumset1(E_222,A_223,A_223,F_224,F_225,F_18) = k2_xboole_0(k2_enumset1(E_222,A_223,F_224,F_225),k1_tarski(F_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_8])).

tff(c_1315,plain,(
    ! [F_225,F_18,E_222,F_224,A_223] : k4_enumset1(E_222,A_223,A_223,F_224,F_225,F_18) = k3_enumset1(E_222,A_223,F_224,F_225,F_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1272])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k2_tarski(F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_27,D_29,G_32,A_26,E_30,F_31,H_33,C_28] : k2_xboole_0(k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31),k2_tarski(G_32,H_33)) = k6_enumset1(A_26,B_27,C_28,D_29,E_30,F_31,G_32,H_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_426,plain,(
    ! [B_155,G_32,E_156,H_33,A_153,D_154,C_157] : k6_enumset1(B_155,C_157,D_154,E_156,A_153,A_153,G_32,H_33) = k2_xboole_0(k3_enumset1(B_155,C_157,D_154,E_156,A_153),k2_tarski(G_32,H_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_12])).

tff(c_439,plain,(
    ! [B_155,G_32,E_156,H_33,A_153,D_154,C_157] : k6_enumset1(B_155,C_157,D_154,E_156,A_153,A_153,G_32,H_33) = k5_enumset1(B_155,C_157,D_154,E_156,A_153,G_32,H_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_426])).

tff(c_26,plain,(
    ! [B_56,A_55,C_57] : k1_enumset1(B_56,A_55,C_57) = k1_enumset1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_284,plain,(
    ! [C_125,G_123,D_121,A_126,B_124,H_127,F_122,E_128] : k2_xboole_0(k2_enumset1(A_126,B_124,C_125,D_121),k2_enumset1(E_128,F_122,G_123,H_127)) = k6_enumset1(A_126,B_124,C_125,D_121,E_128,F_122,G_123,H_127) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_974,plain,(
    ! [D_209,A_203,B_206,C_205,A_204,B_207,C_208] : k6_enumset1(A_203,B_207,C_205,D_209,A_204,A_204,B_206,C_208) = k2_xboole_0(k2_enumset1(A_203,B_207,C_205,D_209),k1_enumset1(A_204,B_206,C_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_3281,plain,(
    ! [B_372,C_376,A_370,B_371,A_373,D_375,C_374] : k6_enumset1(A_370,B_372,C_374,D_375,A_373,A_373,B_371,C_376) = k2_xboole_0(k2_enumset1(A_370,B_372,C_374,D_375),k1_enumset1(B_371,A_373,C_376)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_974])).

tff(c_308,plain,(
    ! [C_39,B_38,C_125,A_37,D_121,A_126,B_124] : k6_enumset1(A_126,B_124,C_125,D_121,A_37,A_37,B_38,C_39) = k2_xboole_0(k2_enumset1(A_126,B_124,C_125,D_121),k1_enumset1(A_37,B_38,C_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_3302,plain,(
    ! [B_372,C_376,A_370,B_371,A_373,D_375,C_374] : k6_enumset1(A_370,B_372,C_374,D_375,B_371,B_371,A_373,C_376) = k6_enumset1(A_370,B_372,C_374,D_375,A_373,A_373,B_371,C_376) ),
    inference(superposition,[status(thm),theory(equality)],[c_3281,c_308])).

tff(c_8377,plain,(
    ! [A_517,C_513,B_515,C_511,A_516,B_514,D_512] : k5_enumset1(A_517,B_514,C_511,D_512,B_515,A_516,C_513) = k5_enumset1(A_517,B_514,C_511,D_512,A_516,B_515,C_513) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_439,c_3302])).

tff(c_8479,plain,(
    ! [C_522,C_521,B_519,A_518,B_523,D_520] : k5_enumset1(B_519,B_519,C_521,D_520,A_518,B_523,C_522) = k4_enumset1(B_519,C_521,D_520,B_523,A_518,C_522) ),
    inference(superposition,[status(thm),theory(equality)],[c_8377,c_24])).

tff(c_8630,plain,(
    ! [E_532,B_533,D_536,C_531,A_535,F_534] : k4_enumset1(A_535,B_533,C_531,E_532,D_536,F_534) = k4_enumset1(A_535,B_533,C_531,D_536,E_532,F_534) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8479])).

tff(c_9660,plain,(
    ! [B_549,D_547,C_548,E_546,A_550] : k4_enumset1(A_550,A_550,B_549,D_547,C_548,E_546) = k3_enumset1(A_550,B_549,C_548,D_547,E_546) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8630])).

tff(c_9776,plain,(
    ! [A_223,F_225,F_224,F_18] : k3_enumset1(A_223,A_223,F_225,F_224,F_18) = k3_enumset1(A_223,A_223,F_224,F_225,F_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_9660])).

tff(c_9831,plain,(
    ! [A_223,F_225,F_224,F_18] : k2_enumset1(A_223,F_225,F_224,F_18) = k2_enumset1(A_223,F_224,F_225,F_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_9776])).

tff(c_28,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_11949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9831,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.85  
% 8.20/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.85  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.20/2.85  
% 8.20/2.85  %Foreground sorts:
% 8.20/2.85  
% 8.20/2.85  
% 8.20/2.85  %Background operators:
% 8.20/2.85  
% 8.20/2.85  
% 8.20/2.85  %Foreground operators:
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.20/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.20/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.20/2.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.20/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.20/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.20/2.85  tff('#skF_2', type, '#skF_2': $i).
% 8.20/2.85  tff('#skF_3', type, '#skF_3': $i).
% 8.20/2.85  tff('#skF_1', type, '#skF_1': $i).
% 8.20/2.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.20/2.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.20/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/2.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.20/2.85  
% 8.20/2.87  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.20/2.87  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 8.20/2.87  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 8.20/2.87  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.20/2.87  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.20/2.87  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.20/2.87  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 8.20/2.87  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 8.20/2.87  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 8.20/2.87  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 8.20/2.87  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 8.20/2.87  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 8.20/2.87  tff(c_20, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.20/2.87  tff(c_22, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.20/2.87  tff(c_134, plain, (![B_88, F_86, C_91, D_87, E_89, A_90]: (k2_xboole_0(k3_enumset1(A_90, B_88, C_91, D_87, E_89), k1_tarski(F_86))=k4_enumset1(A_90, B_88, C_91, D_87, E_89, F_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.20/2.87  tff(c_143, plain, (![C_42, F_86, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, F_86)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(F_86)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_134])).
% 8.20/2.87  tff(c_146, plain, (![C_42, F_86, A_40, D_43, B_41]: (k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(F_86))=k3_enumset1(A_40, B_41, C_42, D_43, F_86))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_143])).
% 8.20/2.87  tff(c_18, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.20/2.87  tff(c_147, plain, (![C_95, A_92, B_96, F_94, D_93]: (k2_xboole_0(k2_enumset1(A_92, B_96, C_95, D_93), k1_tarski(F_94))=k3_enumset1(A_92, B_96, C_95, D_93, F_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_143])).
% 8.20/2.87  tff(c_156, plain, (![A_37, B_38, C_39, F_94]: (k3_enumset1(A_37, A_37, B_38, C_39, F_94)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(F_94)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 8.20/2.87  tff(c_159, plain, (![A_37, B_38, C_39, F_94]: (k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(F_94))=k2_enumset1(A_37, B_38, C_39, F_94))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_156])).
% 8.20/2.87  tff(c_16, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/2.87  tff(c_160, plain, (![A_97, B_98, C_99, F_100]: (k2_xboole_0(k1_enumset1(A_97, B_98, C_99), k1_tarski(F_100))=k2_enumset1(A_97, B_98, C_99, F_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_156])).
% 8.20/2.87  tff(c_175, plain, (![A_35, B_36, F_100]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(F_100))=k2_enumset1(A_35, A_35, B_36, F_100))), inference(superposition, [status(thm), theory('equality')], [c_16, c_160])).
% 8.20/2.87  tff(c_178, plain, (![A_35, B_36, F_100]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(F_100))=k1_enumset1(A_35, B_36, F_100))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_175])).
% 8.20/2.87  tff(c_8, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k3_enumset1(A_13, B_14, C_15, D_16, E_17), k1_tarski(F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.20/2.87  tff(c_14, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.20/2.87  tff(c_201, plain, (![A_109, B_108, D_112, G_110, C_106, E_107, F_111]: (k2_xboole_0(k3_enumset1(A_109, B_108, C_106, D_112, E_107), k2_tarski(F_111, G_110))=k5_enumset1(A_109, B_108, C_106, D_112, E_107, F_111, G_110))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/2.87  tff(c_213, plain, (![A_109, B_108, D_112, A_34, C_106, E_107]: (k5_enumset1(A_109, B_108, C_106, D_112, E_107, A_34, A_34)=k2_xboole_0(k3_enumset1(A_109, B_108, C_106, D_112, E_107), k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_201])).
% 8.20/2.87  tff(c_401, plain, (![E_149, B_148, C_152, D_151, A_150, A_147]: (k5_enumset1(A_150, B_148, C_152, D_151, E_149, A_147, A_147)=k4_enumset1(A_150, B_148, C_152, D_151, E_149, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_213])).
% 8.20/2.87  tff(c_24, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (k5_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54)=k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.20/2.87  tff(c_408, plain, (![E_149, B_148, C_152, D_151, A_147]: (k4_enumset1(B_148, C_152, D_151, E_149, A_147, A_147)=k4_enumset1(B_148, B_148, C_152, D_151, E_149, A_147))), inference(superposition, [status(thm), theory('equality')], [c_401, c_24])).
% 8.20/2.87  tff(c_420, plain, (![B_155, E_156, A_153, D_154, C_157]: (k4_enumset1(B_155, C_157, D_154, E_156, A_153, A_153)=k3_enumset1(B_155, C_157, D_154, E_156, A_153))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_408])).
% 8.20/2.87  tff(c_430, plain, (![C_157, D_154, E_156, A_153]: (k3_enumset1(C_157, D_154, E_156, A_153, A_153)=k3_enumset1(C_157, C_157, D_154, E_156, A_153))), inference(superposition, [status(thm), theory('equality')], [c_420, c_22])).
% 8.20/2.87  tff(c_443, plain, (![C_158, D_159, E_160, A_161]: (k3_enumset1(C_158, D_159, E_160, A_161, A_161)=k2_enumset1(C_158, D_159, E_160, A_161))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_430])).
% 8.20/2.87  tff(c_462, plain, (![D_159, E_160, A_161]: (k2_enumset1(D_159, E_160, A_161, A_161)=k2_enumset1(D_159, D_159, E_160, A_161))), inference(superposition, [status(thm), theory('equality')], [c_443, c_20])).
% 8.20/2.87  tff(c_514, plain, (![D_168, E_169, A_170]: (k2_enumset1(D_168, E_169, A_170, A_170)=k1_enumset1(D_168, E_169, A_170))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_462])).
% 8.20/2.87  tff(c_539, plain, (![E_169, A_170]: (k1_enumset1(E_169, E_169, A_170)=k1_enumset1(E_169, A_170, A_170))), inference(superposition, [status(thm), theory('equality')], [c_514, c_18])).
% 8.20/2.87  tff(c_561, plain, (![E_171, A_172]: (k1_enumset1(E_171, A_172, A_172)=k2_tarski(E_171, A_172))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_539])).
% 8.20/2.87  tff(c_570, plain, (![E_171, A_172, F_94]: (k2_xboole_0(k2_tarski(E_171, A_172), k1_tarski(F_94))=k2_enumset1(E_171, A_172, A_172, F_94))), inference(superposition, [status(thm), theory('equality')], [c_561, c_159])).
% 8.20/2.87  tff(c_883, plain, (![E_200, A_201, F_202]: (k2_enumset1(E_200, A_201, A_201, F_202)=k1_enumset1(E_200, A_201, F_202))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_570])).
% 8.20/2.87  tff(c_919, plain, (![E_200, A_201, F_202, F_86]: (k3_enumset1(E_200, A_201, A_201, F_202, F_86)=k2_xboole_0(k1_enumset1(E_200, A_201, F_202), k1_tarski(F_86)))), inference(superposition, [status(thm), theory('equality')], [c_883, c_146])).
% 8.20/2.87  tff(c_1238, plain, (![E_222, A_223, F_224, F_225]: (k3_enumset1(E_222, A_223, A_223, F_224, F_225)=k2_enumset1(E_222, A_223, F_224, F_225))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_919])).
% 8.20/2.87  tff(c_1272, plain, (![F_225, F_18, E_222, F_224, A_223]: (k4_enumset1(E_222, A_223, A_223, F_224, F_225, F_18)=k2_xboole_0(k2_enumset1(E_222, A_223, F_224, F_225), k1_tarski(F_18)))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_8])).
% 8.20/2.87  tff(c_1315, plain, (![F_225, F_18, E_222, F_224, A_223]: (k4_enumset1(E_222, A_223, A_223, F_224, F_225, F_18)=k3_enumset1(E_222, A_223, F_224, F_225, F_18))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1272])).
% 8.20/2.87  tff(c_10, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k2_tarski(F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/2.87  tff(c_12, plain, (![B_27, D_29, G_32, A_26, E_30, F_31, H_33, C_28]: (k2_xboole_0(k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31), k2_tarski(G_32, H_33))=k6_enumset1(A_26, B_27, C_28, D_29, E_30, F_31, G_32, H_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.20/2.87  tff(c_426, plain, (![B_155, G_32, E_156, H_33, A_153, D_154, C_157]: (k6_enumset1(B_155, C_157, D_154, E_156, A_153, A_153, G_32, H_33)=k2_xboole_0(k3_enumset1(B_155, C_157, D_154, E_156, A_153), k2_tarski(G_32, H_33)))), inference(superposition, [status(thm), theory('equality')], [c_420, c_12])).
% 8.20/2.87  tff(c_439, plain, (![B_155, G_32, E_156, H_33, A_153, D_154, C_157]: (k6_enumset1(B_155, C_157, D_154, E_156, A_153, A_153, G_32, H_33)=k5_enumset1(B_155, C_157, D_154, E_156, A_153, G_32, H_33))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_426])).
% 8.20/2.87  tff(c_26, plain, (![B_56, A_55, C_57]: (k1_enumset1(B_56, A_55, C_57)=k1_enumset1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.20/2.87  tff(c_284, plain, (![C_125, G_123, D_121, A_126, B_124, H_127, F_122, E_128]: (k2_xboole_0(k2_enumset1(A_126, B_124, C_125, D_121), k2_enumset1(E_128, F_122, G_123, H_127))=k6_enumset1(A_126, B_124, C_125, D_121, E_128, F_122, G_123, H_127))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/2.87  tff(c_974, plain, (![D_209, A_203, B_206, C_205, A_204, B_207, C_208]: (k6_enumset1(A_203, B_207, C_205, D_209, A_204, A_204, B_206, C_208)=k2_xboole_0(k2_enumset1(A_203, B_207, C_205, D_209), k1_enumset1(A_204, B_206, C_208)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_284])).
% 8.20/2.87  tff(c_3281, plain, (![B_372, C_376, A_370, B_371, A_373, D_375, C_374]: (k6_enumset1(A_370, B_372, C_374, D_375, A_373, A_373, B_371, C_376)=k2_xboole_0(k2_enumset1(A_370, B_372, C_374, D_375), k1_enumset1(B_371, A_373, C_376)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_974])).
% 8.20/2.87  tff(c_308, plain, (![C_39, B_38, C_125, A_37, D_121, A_126, B_124]: (k6_enumset1(A_126, B_124, C_125, D_121, A_37, A_37, B_38, C_39)=k2_xboole_0(k2_enumset1(A_126, B_124, C_125, D_121), k1_enumset1(A_37, B_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_284])).
% 8.20/2.87  tff(c_3302, plain, (![B_372, C_376, A_370, B_371, A_373, D_375, C_374]: (k6_enumset1(A_370, B_372, C_374, D_375, B_371, B_371, A_373, C_376)=k6_enumset1(A_370, B_372, C_374, D_375, A_373, A_373, B_371, C_376))), inference(superposition, [status(thm), theory('equality')], [c_3281, c_308])).
% 8.20/2.87  tff(c_8377, plain, (![A_517, C_513, B_515, C_511, A_516, B_514, D_512]: (k5_enumset1(A_517, B_514, C_511, D_512, B_515, A_516, C_513)=k5_enumset1(A_517, B_514, C_511, D_512, A_516, B_515, C_513))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_439, c_3302])).
% 8.20/2.87  tff(c_8479, plain, (![C_522, C_521, B_519, A_518, B_523, D_520]: (k5_enumset1(B_519, B_519, C_521, D_520, A_518, B_523, C_522)=k4_enumset1(B_519, C_521, D_520, B_523, A_518, C_522))), inference(superposition, [status(thm), theory('equality')], [c_8377, c_24])).
% 8.20/2.87  tff(c_8630, plain, (![E_532, B_533, D_536, C_531, A_535, F_534]: (k4_enumset1(A_535, B_533, C_531, E_532, D_536, F_534)=k4_enumset1(A_535, B_533, C_531, D_536, E_532, F_534))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8479])).
% 8.20/2.87  tff(c_9660, plain, (![B_549, D_547, C_548, E_546, A_550]: (k4_enumset1(A_550, A_550, B_549, D_547, C_548, E_546)=k3_enumset1(A_550, B_549, C_548, D_547, E_546))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8630])).
% 8.20/2.87  tff(c_9776, plain, (![A_223, F_225, F_224, F_18]: (k3_enumset1(A_223, A_223, F_225, F_224, F_18)=k3_enumset1(A_223, A_223, F_224, F_225, F_18))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_9660])).
% 8.20/2.87  tff(c_9831, plain, (![A_223, F_225, F_224, F_18]: (k2_enumset1(A_223, F_225, F_224, F_18)=k2_enumset1(A_223, F_224, F_225, F_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_9776])).
% 8.20/2.87  tff(c_28, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.20/2.87  tff(c_11949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9831, c_28])).
% 8.20/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.87  
% 8.20/2.87  Inference rules
% 8.20/2.87  ----------------------
% 8.20/2.87  #Ref     : 0
% 8.20/2.87  #Sup     : 2680
% 8.20/2.87  #Fact    : 0
% 8.20/2.87  #Define  : 0
% 8.20/2.87  #Split   : 0
% 8.20/2.87  #Chain   : 0
% 8.20/2.87  #Close   : 0
% 8.20/2.87  
% 8.20/2.87  Ordering : KBO
% 8.20/2.87  
% 8.20/2.87  Simplification rules
% 8.20/2.87  ----------------------
% 8.20/2.87  #Subsume      : 160
% 8.20/2.87  #Demod        : 3195
% 8.20/2.87  #Tautology    : 1858
% 8.20/2.87  #SimpNegUnit  : 0
% 8.20/2.87  #BackRed      : 4
% 8.20/2.87  
% 8.20/2.87  #Partial instantiations: 0
% 8.20/2.87  #Strategies tried      : 1
% 8.20/2.87  
% 8.20/2.87  Timing (in seconds)
% 8.20/2.87  ----------------------
% 8.20/2.87  Preprocessing        : 0.31
% 8.20/2.87  Parsing              : 0.16
% 8.20/2.87  CNF conversion       : 0.02
% 8.20/2.87  Main loop            : 1.75
% 8.20/2.87  Inferencing          : 0.53
% 8.20/2.87  Reduction            : 0.91
% 8.20/2.87  Demodulation         : 0.80
% 8.20/2.87  BG Simplification    : 0.06
% 8.20/2.87  Subsumption          : 0.19
% 8.20/2.87  Abstraction          : 0.10
% 8.20/2.87  MUC search           : 0.00
% 8.20/2.87  Cooper               : 0.00
% 8.20/2.87  Total                : 2.09
% 8.20/2.87  Index Insertion      : 0.00
% 8.20/2.87  Index Deletion       : 0.00
% 8.20/2.87  Index Matching       : 0.00
% 8.20/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

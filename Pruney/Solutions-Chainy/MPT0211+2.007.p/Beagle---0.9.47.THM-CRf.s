%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 9.20s
% Output     : CNFRefutation 9.20s
% Verified   : 
% Statistics : Number of formulae       :  102 (1440 expanded)
%              Number of leaves         :   28 ( 496 expanded)
%              Depth                    :   22
%              Number of atoms          :   85 (1423 expanded)
%              Number of equality atoms :   84 (1422 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_18,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [B_77,C_78,E_80,A_79,D_76] : k2_xboole_0(k1_tarski(A_79),k2_enumset1(B_77,C_78,D_76,E_80)) = k3_enumset1(A_79,B_77,C_78,D_76,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_79,A_32,B_33,C_34] : k3_enumset1(A_79,A_32,A_32,B_33,C_34) = k2_xboole_0(k1_tarski(A_79),k1_enumset1(A_32,B_33,C_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_138,plain,(
    ! [A_87,A_88,B_89,C_90] : k3_enumset1(A_87,A_88,A_88,B_89,C_90) = k2_xboole_0(k1_tarski(A_87),k1_enumset1(A_88,B_89,C_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_20,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_88,B_89,C_90] : k2_xboole_0(k1_tarski(A_88),k1_enumset1(A_88,B_89,C_90)) = k2_enumset1(A_88,A_88,B_89,C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_20])).

tff(c_168,plain,(
    ! [A_91,B_92,C_93] : k2_xboole_0(k1_tarski(A_91),k1_enumset1(A_91,B_92,C_93)) = k1_enumset1(A_91,B_92,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_181,plain,(
    ! [A_32,B_33,C_34] : k3_enumset1(A_32,A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_168])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    ! [A_114,A_115,B_116] : k3_enumset1(A_114,A_115,A_115,A_115,B_116) = k2_xboole_0(k1_tarski(A_114),k2_tarski(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_184,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),k2_tarski(A_30,B_31)) = k1_enumset1(A_30,A_30,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_168])).

tff(c_187,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),k2_tarski(A_30,B_31)) = k2_tarski(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_390,plain,(
    ! [A_117,B_118] : k3_enumset1(A_117,A_117,A_117,A_117,B_118) = k2_tarski(A_117,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_187])).

tff(c_411,plain,(
    ! [A_117,B_118] : k2_enumset1(A_117,A_117,A_117,B_118) = k2_tarski(A_117,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_20])).

tff(c_22,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [A_102,C_104,D_103,B_100,E_101,F_99] : k2_xboole_0(k3_enumset1(A_102,B_100,C_104,D_103,E_101),k1_tarski(F_99)) = k4_enumset1(A_102,B_100,C_104,D_103,E_101,F_99) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [A_35,B_36,C_37,D_38,F_99] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,F_99) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(F_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_247])).

tff(c_1230,plain,(
    ! [C_158,A_156,F_157,D_159,B_160] : k2_xboole_0(k2_enumset1(A_156,B_160,C_158,D_159),k1_tarski(F_157)) = k3_enumset1(A_156,B_160,C_158,D_159,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_259])).

tff(c_1242,plain,(
    ! [A_117,B_118,F_157] : k3_enumset1(A_117,A_117,A_117,B_118,F_157) = k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(F_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_1230])).

tff(c_1249,plain,(
    ! [A_117,B_118,F_157] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(F_157)) = k1_enumset1(A_117,B_118,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_1242])).

tff(c_262,plain,(
    ! [A_35,B_36,C_37,D_38,F_99] : k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(F_99)) = k3_enumset1(A_35,B_36,C_37,D_38,F_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_259])).

tff(c_14,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49) = k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_559,plain,(
    ! [B_137,C_132,E_133,F_134,A_131,D_136,G_135] : k2_xboole_0(k3_enumset1(A_131,B_137,C_132,D_136,E_133),k2_tarski(F_134,G_135)) = k5_enumset1(A_131,B_137,C_132,D_136,E_133,F_134,G_135) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_583,plain,(
    ! [A_35,F_134,B_36,C_37,D_38,G_135] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,F_134,G_135) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k2_tarski(F_134,G_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_559])).

tff(c_1765,plain,(
    ! [C_200,F_203,D_201,G_199,A_198,B_202] : k2_xboole_0(k2_enumset1(A_198,B_202,C_200,D_201),k2_tarski(F_203,G_199)) = k4_enumset1(A_198,B_202,C_200,D_201,F_203,G_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_583])).

tff(c_1789,plain,(
    ! [C_200,A_29,D_201,A_198,B_202] : k4_enumset1(A_198,B_202,C_200,D_201,A_29,A_29) = k2_xboole_0(k2_enumset1(A_198,B_202,C_200,D_201),k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1765])).

tff(c_2008,plain,(
    ! [C_216,A_214,A_215,B_217,D_213] : k4_enumset1(A_215,B_217,C_216,D_213,A_214,A_214) = k3_enumset1(A_215,B_217,C_216,D_213,A_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_1789])).

tff(c_2035,plain,(
    ! [B_217,C_216,D_213,A_214] : k3_enumset1(B_217,C_216,D_213,A_214,A_214) = k3_enumset1(B_217,B_217,C_216,D_213,A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_22])).

tff(c_2074,plain,(
    ! [B_218,C_219,D_220,A_221] : k3_enumset1(B_218,C_219,D_220,A_221,A_221) = k2_enumset1(B_218,C_219,D_220,A_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2035])).

tff(c_2115,plain,(
    ! [D_220,A_221] : k2_enumset1(D_220,D_220,D_220,A_221) = k1_enumset1(D_220,A_221,A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_181])).

tff(c_2187,plain,(
    ! [D_222,A_223] : k1_enumset1(D_222,A_223,A_223) = k2_tarski(D_222,A_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_2115])).

tff(c_1245,plain,(
    ! [A_32,B_33,C_34,F_157] : k3_enumset1(A_32,A_32,B_33,C_34,F_157) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(F_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1230])).

tff(c_1250,plain,(
    ! [A_32,B_33,C_34,F_157] : k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(F_157)) = k2_enumset1(A_32,B_33,C_34,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1245])).

tff(c_2196,plain,(
    ! [D_222,A_223,F_157] : k2_xboole_0(k2_tarski(D_222,A_223),k1_tarski(F_157)) = k2_enumset1(D_222,A_223,A_223,F_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_2187,c_1250])).

tff(c_2240,plain,(
    ! [D_222,A_223,F_157] : k2_enumset1(D_222,A_223,A_223,F_157) = k1_enumset1(D_222,A_223,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_2196])).

tff(c_2126,plain,(
    ! [C_219,D_220,A_221] : k2_enumset1(C_219,D_220,A_221,A_221) = k2_enumset1(C_219,C_219,D_220,A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_20])).

tff(c_2178,plain,(
    ! [C_219,D_220,A_221] : k2_enumset1(C_219,D_220,A_221,A_221) = k1_enumset1(C_219,D_220,A_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2126])).

tff(c_2067,plain,(
    ! [B_217,C_216,D_213,A_214] : k3_enumset1(B_217,C_216,D_213,A_214,A_214) = k2_enumset1(B_217,C_216,D_213,A_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2035])).

tff(c_339,plain,(
    ! [A_115,B_116] : k3_enumset1(A_115,A_115,A_115,A_115,B_116) = k2_tarski(A_115,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_187])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [A_94,B_95] : k2_xboole_0(k1_tarski(A_94),k2_tarski(A_94,B_95)) = k2_tarski(A_94,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_197,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k2_tarski(B_4,A_3)) = k2_tarski(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_188])).

tff(c_471,plain,(
    ! [B_128,A_129] : k3_enumset1(B_128,A_129,A_129,A_129,B_128) = k2_tarski(B_128,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_197])).

tff(c_498,plain,(
    ! [A_129] : k2_enumset1(A_129,A_129,A_129,A_129) = k2_tarski(A_129,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_20])).

tff(c_527,plain,(
    ! [A_129] : k2_enumset1(A_129,A_129,A_129,A_129) = k1_tarski(A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_498])).

tff(c_1239,plain,(
    ! [A_129,F_157] : k3_enumset1(A_129,A_129,A_129,A_129,F_157) = k2_xboole_0(k1_tarski(A_129),k1_tarski(F_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_1230])).

tff(c_1248,plain,(
    ! [A_129,F_157] : k2_xboole_0(k1_tarski(A_129),k1_tarski(F_157)) = k2_tarski(A_129,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_1239])).

tff(c_161,plain,(
    ! [A_87,A_30,B_31] : k3_enumset1(A_87,A_30,A_30,A_30,B_31) = k2_xboole_0(k1_tarski(A_87),k2_tarski(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_2108,plain,(
    ! [B_218,A_221] : k2_xboole_0(k1_tarski(B_218),k2_tarski(A_221,A_221)) = k2_enumset1(B_218,A_221,A_221,A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_161])).

tff(c_2644,plain,(
    ! [B_240,A_241] : k2_enumset1(B_240,A_241,A_241,A_241) = k2_tarski(B_240,A_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_14,c_2108])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_tarski(A_5),k2_enumset1(B_6,C_7,D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2706,plain,(
    ! [A_242,B_243,A_244] : k3_enumset1(A_242,B_243,A_244,A_244,A_244) = k2_xboole_0(k1_tarski(A_242),k2_tarski(B_243,A_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2644,c_6])).

tff(c_3358,plain,(
    ! [A_256,B_257] : k3_enumset1(A_256,A_256,B_257,B_257,B_257) = k2_tarski(A_256,B_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2706])).

tff(c_3504,plain,(
    ! [A_258,B_259] : k2_enumset1(A_258,A_258,B_259,B_259) = k2_tarski(A_258,B_259) ),
    inference(superposition,[status(thm),theory(equality)],[c_3358,c_2067])).

tff(c_4667,plain,(
    ! [A_286,A_287,B_288] : k3_enumset1(A_286,A_287,A_287,B_288,B_288) = k2_xboole_0(k1_tarski(A_286),k2_tarski(A_287,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3504,c_6])).

tff(c_2862,plain,(
    ! [A_242,A_3,B_4] : k3_enumset1(A_242,A_3,B_4,B_4,B_4) = k2_xboole_0(k1_tarski(A_242),k2_tarski(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2706])).

tff(c_4691,plain,(
    ! [A_286,B_288,A_287] : k3_enumset1(A_286,B_288,A_287,A_287,A_287) = k3_enumset1(A_286,A_287,A_287,B_288,B_288) ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_2862])).

tff(c_4893,plain,(
    ! [A_286,B_288,A_287] : k1_enumset1(A_286,B_288,A_287) = k1_enumset1(A_286,A_287,B_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2240,c_2178,c_2067,c_2067,c_4691])).

tff(c_1364,plain,(
    ! [A_165,B_166,F_167] : k2_xboole_0(k2_tarski(A_165,B_166),k1_tarski(F_167)) = k1_enumset1(A_165,B_166,F_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_1242])).

tff(c_1383,plain,(
    ! [B_168,A_169,F_170] : k2_xboole_0(k2_tarski(B_168,A_169),k1_tarski(F_170)) = k1_enumset1(A_169,B_168,F_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1364])).

tff(c_1389,plain,(
    ! [B_168,A_169,F_170] : k1_enumset1(B_168,A_169,F_170) = k1_enumset1(A_169,B_168,F_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_1383,c_1249])).

tff(c_2317,plain,(
    ! [F_231,B_232] : k1_enumset1(F_231,B_232,F_231) = k2_tarski(B_232,F_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_2187])).

tff(c_2330,plain,(
    ! [B_232,F_231,F_157] : k2_xboole_0(k2_tarski(B_232,F_231),k1_tarski(F_157)) = k2_enumset1(F_231,B_232,F_231,F_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_2317,c_1250])).

tff(c_2379,plain,(
    ! [F_231,B_232,F_157] : k2_enumset1(F_231,B_232,F_231,F_157) = k1_enumset1(B_232,F_231,F_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_2330])).

tff(c_1780,plain,(
    ! [B_33,C_34,F_203,G_199,A_32] : k4_enumset1(A_32,A_32,B_33,C_34,F_203,G_199) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k2_tarski(F_203,G_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1765])).

tff(c_3977,plain,(
    ! [G_270,A_269,B_267,C_268,F_266] : k2_xboole_0(k1_enumset1(A_269,B_267,C_268),k2_tarski(F_266,G_270)) = k3_enumset1(A_269,B_267,C_268,F_266,G_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1780])).

tff(c_4007,plain,(
    ! [A_30,B_31,F_266,G_270] : k3_enumset1(A_30,A_30,B_31,F_266,G_270) = k2_xboole_0(k2_tarski(A_30,B_31),k2_tarski(F_266,G_270)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3977])).

tff(c_4020,plain,(
    ! [A_30,B_31,F_266,G_270] : k2_xboole_0(k2_tarski(A_30,B_31),k2_tarski(F_266,G_270)) = k2_enumset1(A_30,B_31,F_266,G_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4007])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_28])).

tff(c_4934,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4893,c_29])).

tff(c_13402,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4020,c_4934])).

tff(c_13405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4893,c_1389,c_2379,c_13402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.20/3.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.10  
% 9.20/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.11  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 9.20/3.11  
% 9.20/3.11  %Foreground sorts:
% 9.20/3.11  
% 9.20/3.11  
% 9.20/3.11  %Background operators:
% 9.20/3.11  
% 9.20/3.11  
% 9.20/3.11  %Foreground operators:
% 9.20/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.20/3.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.20/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.20/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.20/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.20/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.20/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.20/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.20/3.11  tff('#skF_2', type, '#skF_2': $i).
% 9.20/3.11  tff('#skF_3', type, '#skF_3': $i).
% 9.20/3.11  tff('#skF_1', type, '#skF_1': $i).
% 9.20/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.20/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.20/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.20/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.20/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.20/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.20/3.11  
% 9.20/3.14  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 9.20/3.14  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 9.20/3.14  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 9.20/3.14  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.20/3.14  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 9.20/3.14  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 9.20/3.14  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.20/3.14  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 9.20/3.14  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 9.20/3.14  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.20/3.14  tff(f_54, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 9.20/3.14  tff(c_18, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.20/3.14  tff(c_117, plain, (![B_77, C_78, E_80, A_79, D_76]: (k2_xboole_0(k1_tarski(A_79), k2_enumset1(B_77, C_78, D_76, E_80))=k3_enumset1(A_79, B_77, C_78, D_76, E_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.20/3.14  tff(c_126, plain, (![A_79, A_32, B_33, C_34]: (k3_enumset1(A_79, A_32, A_32, B_33, C_34)=k2_xboole_0(k1_tarski(A_79), k1_enumset1(A_32, B_33, C_34)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 9.20/3.14  tff(c_138, plain, (![A_87, A_88, B_89, C_90]: (k3_enumset1(A_87, A_88, A_88, B_89, C_90)=k2_xboole_0(k1_tarski(A_87), k1_enumset1(A_88, B_89, C_90)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 9.20/3.14  tff(c_20, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.20/3.14  tff(c_148, plain, (![A_88, B_89, C_90]: (k2_xboole_0(k1_tarski(A_88), k1_enumset1(A_88, B_89, C_90))=k2_enumset1(A_88, A_88, B_89, C_90))), inference(superposition, [status(thm), theory('equality')], [c_138, c_20])).
% 9.20/3.14  tff(c_168, plain, (![A_91, B_92, C_93]: (k2_xboole_0(k1_tarski(A_91), k1_enumset1(A_91, B_92, C_93))=k1_enumset1(A_91, B_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_148])).
% 9.20/3.14  tff(c_181, plain, (![A_32, B_33, C_34]: (k3_enumset1(A_32, A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(superposition, [status(thm), theory('equality')], [c_126, c_168])).
% 9.20/3.14  tff(c_16, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.20/3.14  tff(c_315, plain, (![A_114, A_115, B_116]: (k3_enumset1(A_114, A_115, A_115, A_115, B_116)=k2_xboole_0(k1_tarski(A_114), k2_tarski(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 9.20/3.14  tff(c_184, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), k2_tarski(A_30, B_31))=k1_enumset1(A_30, A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_16, c_168])).
% 9.20/3.14  tff(c_187, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), k2_tarski(A_30, B_31))=k2_tarski(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_184])).
% 9.20/3.14  tff(c_390, plain, (![A_117, B_118]: (k3_enumset1(A_117, A_117, A_117, A_117, B_118)=k2_tarski(A_117, B_118))), inference(superposition, [status(thm), theory('equality')], [c_315, c_187])).
% 9.20/3.14  tff(c_411, plain, (![A_117, B_118]: (k2_enumset1(A_117, A_117, A_117, B_118)=k2_tarski(A_117, B_118))), inference(superposition, [status(thm), theory('equality')], [c_390, c_20])).
% 9.20/3.14  tff(c_22, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.20/3.14  tff(c_247, plain, (![A_102, C_104, D_103, B_100, E_101, F_99]: (k2_xboole_0(k3_enumset1(A_102, B_100, C_104, D_103, E_101), k1_tarski(F_99))=k4_enumset1(A_102, B_100, C_104, D_103, E_101, F_99))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.20/3.14  tff(c_259, plain, (![A_35, B_36, C_37, D_38, F_99]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, F_99)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(F_99)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_247])).
% 9.20/3.14  tff(c_1230, plain, (![C_158, A_156, F_157, D_159, B_160]: (k2_xboole_0(k2_enumset1(A_156, B_160, C_158, D_159), k1_tarski(F_157))=k3_enumset1(A_156, B_160, C_158, D_159, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_259])).
% 9.20/3.14  tff(c_1242, plain, (![A_117, B_118, F_157]: (k3_enumset1(A_117, A_117, A_117, B_118, F_157)=k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(F_157)))), inference(superposition, [status(thm), theory('equality')], [c_411, c_1230])).
% 9.20/3.14  tff(c_1249, plain, (![A_117, B_118, F_157]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(F_157))=k1_enumset1(A_117, B_118, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_1242])).
% 9.20/3.14  tff(c_262, plain, (![A_35, B_36, C_37, D_38, F_99]: (k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(F_99))=k3_enumset1(A_35, B_36, C_37, D_38, F_99))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_259])).
% 9.20/3.14  tff(c_14, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.20/3.14  tff(c_24, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.20/3.14  tff(c_559, plain, (![B_137, C_132, E_133, F_134, A_131, D_136, G_135]: (k2_xboole_0(k3_enumset1(A_131, B_137, C_132, D_136, E_133), k2_tarski(F_134, G_135))=k5_enumset1(A_131, B_137, C_132, D_136, E_133, F_134, G_135))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.20/3.14  tff(c_583, plain, (![A_35, F_134, B_36, C_37, D_38, G_135]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, F_134, G_135)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k2_tarski(F_134, G_135)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_559])).
% 9.20/3.14  tff(c_1765, plain, (![C_200, F_203, D_201, G_199, A_198, B_202]: (k2_xboole_0(k2_enumset1(A_198, B_202, C_200, D_201), k2_tarski(F_203, G_199))=k4_enumset1(A_198, B_202, C_200, D_201, F_203, G_199))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_583])).
% 9.20/3.14  tff(c_1789, plain, (![C_200, A_29, D_201, A_198, B_202]: (k4_enumset1(A_198, B_202, C_200, D_201, A_29, A_29)=k2_xboole_0(k2_enumset1(A_198, B_202, C_200, D_201), k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1765])).
% 9.20/3.14  tff(c_2008, plain, (![C_216, A_214, A_215, B_217, D_213]: (k4_enumset1(A_215, B_217, C_216, D_213, A_214, A_214)=k3_enumset1(A_215, B_217, C_216, D_213, A_214))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_1789])).
% 9.20/3.14  tff(c_2035, plain, (![B_217, C_216, D_213, A_214]: (k3_enumset1(B_217, C_216, D_213, A_214, A_214)=k3_enumset1(B_217, B_217, C_216, D_213, A_214))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_22])).
% 9.20/3.14  tff(c_2074, plain, (![B_218, C_219, D_220, A_221]: (k3_enumset1(B_218, C_219, D_220, A_221, A_221)=k2_enumset1(B_218, C_219, D_220, A_221))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2035])).
% 9.20/3.14  tff(c_2115, plain, (![D_220, A_221]: (k2_enumset1(D_220, D_220, D_220, A_221)=k1_enumset1(D_220, A_221, A_221))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_181])).
% 9.20/3.14  tff(c_2187, plain, (![D_222, A_223]: (k1_enumset1(D_222, A_223, A_223)=k2_tarski(D_222, A_223))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_2115])).
% 9.20/3.14  tff(c_1245, plain, (![A_32, B_33, C_34, F_157]: (k3_enumset1(A_32, A_32, B_33, C_34, F_157)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(F_157)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1230])).
% 9.20/3.14  tff(c_1250, plain, (![A_32, B_33, C_34, F_157]: (k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(F_157))=k2_enumset1(A_32, B_33, C_34, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1245])).
% 9.20/3.14  tff(c_2196, plain, (![D_222, A_223, F_157]: (k2_xboole_0(k2_tarski(D_222, A_223), k1_tarski(F_157))=k2_enumset1(D_222, A_223, A_223, F_157))), inference(superposition, [status(thm), theory('equality')], [c_2187, c_1250])).
% 9.20/3.14  tff(c_2240, plain, (![D_222, A_223, F_157]: (k2_enumset1(D_222, A_223, A_223, F_157)=k1_enumset1(D_222, A_223, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_2196])).
% 9.20/3.14  tff(c_2126, plain, (![C_219, D_220, A_221]: (k2_enumset1(C_219, D_220, A_221, A_221)=k2_enumset1(C_219, C_219, D_220, A_221))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_20])).
% 9.20/3.14  tff(c_2178, plain, (![C_219, D_220, A_221]: (k2_enumset1(C_219, D_220, A_221, A_221)=k1_enumset1(C_219, D_220, A_221))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2126])).
% 9.20/3.14  tff(c_2067, plain, (![B_217, C_216, D_213, A_214]: (k3_enumset1(B_217, C_216, D_213, A_214, A_214)=k2_enumset1(B_217, C_216, D_213, A_214))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2035])).
% 9.20/3.14  tff(c_339, plain, (![A_115, B_116]: (k3_enumset1(A_115, A_115, A_115, A_115, B_116)=k2_tarski(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_315, c_187])).
% 9.20/3.14  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.20/3.14  tff(c_188, plain, (![A_94, B_95]: (k2_xboole_0(k1_tarski(A_94), k2_tarski(A_94, B_95))=k2_tarski(A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_184])).
% 9.20/3.14  tff(c_197, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(B_4, A_3))=k2_tarski(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_188])).
% 9.20/3.14  tff(c_471, plain, (![B_128, A_129]: (k3_enumset1(B_128, A_129, A_129, A_129, B_128)=k2_tarski(B_128, A_129))), inference(superposition, [status(thm), theory('equality')], [c_315, c_197])).
% 9.20/3.14  tff(c_498, plain, (![A_129]: (k2_enumset1(A_129, A_129, A_129, A_129)=k2_tarski(A_129, A_129))), inference(superposition, [status(thm), theory('equality')], [c_471, c_20])).
% 9.20/3.14  tff(c_527, plain, (![A_129]: (k2_enumset1(A_129, A_129, A_129, A_129)=k1_tarski(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_498])).
% 9.20/3.14  tff(c_1239, plain, (![A_129, F_157]: (k3_enumset1(A_129, A_129, A_129, A_129, F_157)=k2_xboole_0(k1_tarski(A_129), k1_tarski(F_157)))), inference(superposition, [status(thm), theory('equality')], [c_527, c_1230])).
% 9.20/3.14  tff(c_1248, plain, (![A_129, F_157]: (k2_xboole_0(k1_tarski(A_129), k1_tarski(F_157))=k2_tarski(A_129, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_1239])).
% 9.20/3.14  tff(c_161, plain, (![A_87, A_30, B_31]: (k3_enumset1(A_87, A_30, A_30, A_30, B_31)=k2_xboole_0(k1_tarski(A_87), k2_tarski(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 9.20/3.14  tff(c_2108, plain, (![B_218, A_221]: (k2_xboole_0(k1_tarski(B_218), k2_tarski(A_221, A_221))=k2_enumset1(B_218, A_221, A_221, A_221))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_161])).
% 9.20/3.14  tff(c_2644, plain, (![B_240, A_241]: (k2_enumset1(B_240, A_241, A_241, A_241)=k2_tarski(B_240, A_241))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_14, c_2108])).
% 9.20/3.14  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k1_tarski(A_5), k2_enumset1(B_6, C_7, D_8, E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.20/3.14  tff(c_2706, plain, (![A_242, B_243, A_244]: (k3_enumset1(A_242, B_243, A_244, A_244, A_244)=k2_xboole_0(k1_tarski(A_242), k2_tarski(B_243, A_244)))), inference(superposition, [status(thm), theory('equality')], [c_2644, c_6])).
% 9.20/3.14  tff(c_3358, plain, (![A_256, B_257]: (k3_enumset1(A_256, A_256, B_257, B_257, B_257)=k2_tarski(A_256, B_257))), inference(superposition, [status(thm), theory('equality')], [c_187, c_2706])).
% 9.20/3.14  tff(c_3504, plain, (![A_258, B_259]: (k2_enumset1(A_258, A_258, B_259, B_259)=k2_tarski(A_258, B_259))), inference(superposition, [status(thm), theory('equality')], [c_3358, c_2067])).
% 9.20/3.14  tff(c_4667, plain, (![A_286, A_287, B_288]: (k3_enumset1(A_286, A_287, A_287, B_288, B_288)=k2_xboole_0(k1_tarski(A_286), k2_tarski(A_287, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_3504, c_6])).
% 9.20/3.14  tff(c_2862, plain, (![A_242, A_3, B_4]: (k3_enumset1(A_242, A_3, B_4, B_4, B_4)=k2_xboole_0(k1_tarski(A_242), k2_tarski(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2706])).
% 9.20/3.14  tff(c_4691, plain, (![A_286, B_288, A_287]: (k3_enumset1(A_286, B_288, A_287, A_287, A_287)=k3_enumset1(A_286, A_287, A_287, B_288, B_288))), inference(superposition, [status(thm), theory('equality')], [c_4667, c_2862])).
% 9.20/3.14  tff(c_4893, plain, (![A_286, B_288, A_287]: (k1_enumset1(A_286, B_288, A_287)=k1_enumset1(A_286, A_287, B_288))), inference(demodulation, [status(thm), theory('equality')], [c_2240, c_2178, c_2067, c_2067, c_4691])).
% 9.20/3.14  tff(c_1364, plain, (![A_165, B_166, F_167]: (k2_xboole_0(k2_tarski(A_165, B_166), k1_tarski(F_167))=k1_enumset1(A_165, B_166, F_167))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_1242])).
% 9.20/3.14  tff(c_1383, plain, (![B_168, A_169, F_170]: (k2_xboole_0(k2_tarski(B_168, A_169), k1_tarski(F_170))=k1_enumset1(A_169, B_168, F_170))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1364])).
% 9.20/3.14  tff(c_1389, plain, (![B_168, A_169, F_170]: (k1_enumset1(B_168, A_169, F_170)=k1_enumset1(A_169, B_168, F_170))), inference(superposition, [status(thm), theory('equality')], [c_1383, c_1249])).
% 9.20/3.14  tff(c_2317, plain, (![F_231, B_232]: (k1_enumset1(F_231, B_232, F_231)=k2_tarski(B_232, F_231))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_2187])).
% 9.20/3.14  tff(c_2330, plain, (![B_232, F_231, F_157]: (k2_xboole_0(k2_tarski(B_232, F_231), k1_tarski(F_157))=k2_enumset1(F_231, B_232, F_231, F_157))), inference(superposition, [status(thm), theory('equality')], [c_2317, c_1250])).
% 9.20/3.14  tff(c_2379, plain, (![F_231, B_232, F_157]: (k2_enumset1(F_231, B_232, F_231, F_157)=k1_enumset1(B_232, F_231, F_157))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_2330])).
% 9.20/3.14  tff(c_1780, plain, (![B_33, C_34, F_203, G_199, A_32]: (k4_enumset1(A_32, A_32, B_33, C_34, F_203, G_199)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k2_tarski(F_203, G_199)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1765])).
% 9.20/3.14  tff(c_3977, plain, (![G_270, A_269, B_267, C_268, F_266]: (k2_xboole_0(k1_enumset1(A_269, B_267, C_268), k2_tarski(F_266, G_270))=k3_enumset1(A_269, B_267, C_268, F_266, G_270))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1780])).
% 9.20/3.14  tff(c_4007, plain, (![A_30, B_31, F_266, G_270]: (k3_enumset1(A_30, A_30, B_31, F_266, G_270)=k2_xboole_0(k2_tarski(A_30, B_31), k2_tarski(F_266, G_270)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3977])).
% 9.20/3.14  tff(c_4020, plain, (![A_30, B_31, F_266, G_270]: (k2_xboole_0(k2_tarski(A_30, B_31), k2_tarski(F_266, G_270))=k2_enumset1(A_30, B_31, F_266, G_270))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4007])).
% 9.20/3.14  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.20/3.14  tff(c_29, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_28])).
% 9.20/3.14  tff(c_4934, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4893, c_29])).
% 9.20/3.14  tff(c_13402, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4020, c_4934])).
% 9.20/3.14  tff(c_13405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4893, c_1389, c_2379, c_13402])).
% 9.20/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.14  
% 9.20/3.14  Inference rules
% 9.20/3.14  ----------------------
% 9.20/3.14  #Ref     : 0
% 9.20/3.14  #Sup     : 3063
% 9.20/3.14  #Fact    : 0
% 9.20/3.14  #Define  : 0
% 9.20/3.14  #Split   : 0
% 9.20/3.14  #Chain   : 0
% 9.20/3.14  #Close   : 0
% 9.20/3.14  
% 9.20/3.14  Ordering : KBO
% 9.20/3.14  
% 9.20/3.14  Simplification rules
% 9.20/3.14  ----------------------
% 9.20/3.14  #Subsume      : 227
% 9.20/3.14  #Demod        : 3971
% 9.20/3.14  #Tautology    : 2172
% 9.20/3.14  #SimpNegUnit  : 0
% 9.20/3.14  #BackRed      : 22
% 9.20/3.14  
% 9.20/3.14  #Partial instantiations: 0
% 9.20/3.14  #Strategies tried      : 1
% 9.20/3.14  
% 9.20/3.14  Timing (in seconds)
% 9.20/3.14  ----------------------
% 9.20/3.15  Preprocessing        : 0.29
% 9.20/3.15  Parsing              : 0.15
% 9.20/3.15  CNF conversion       : 0.02
% 9.20/3.15  Main loop            : 2.00
% 9.20/3.15  Inferencing          : 0.65
% 9.20/3.15  Reduction            : 0.97
% 9.20/3.15  Demodulation         : 0.84
% 9.20/3.15  BG Simplification    : 0.07
% 9.20/3.15  Subsumption          : 0.23
% 9.20/3.15  Abstraction          : 0.11
% 9.20/3.15  MUC search           : 0.00
% 9.20/3.15  Cooper               : 0.00
% 9.20/3.15  Total                : 2.36
% 9.20/3.15  Index Insertion      : 0.00
% 9.20/3.15  Index Deletion       : 0.00
% 9.20/3.15  Index Matching       : 0.00
% 9.20/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

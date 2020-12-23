%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 13.68s
% Output     : CNFRefutation 13.68s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 540 expanded)
%              Number of leaves         :   28 ( 194 expanded)
%              Depth                    :   21
%              Number of atoms          :   80 ( 522 expanded)
%              Number of equality atoms :   79 ( 521 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_30,plain,(
    ! [A_59,C_61,B_60] : k1_enumset1(A_59,C_61,B_60) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_37,B_38,C_39,D_40] : k3_enumset1(A_37,A_37,B_38,C_39,D_40) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_44,C_43,A_41,B_42,E_45] : k4_enumset1(A_41,A_41,B_42,C_43,D_44,E_45) = k3_enumset1(A_41,B_42,C_43,D_44,E_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_750,plain,(
    ! [D_122,A_119,F_121,B_120,E_123,C_118] : k2_xboole_0(k3_enumset1(A_119,B_120,C_118,D_122,E_123),k1_tarski(F_121)) = k4_enumset1(A_119,B_120,C_118,D_122,E_123,F_121) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_759,plain,(
    ! [C_39,B_38,A_37,D_40,F_121] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,F_121) = k2_xboole_0(k2_enumset1(A_37,B_38,C_39,D_40),k1_tarski(F_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_750])).

tff(c_1372,plain,(
    ! [C_165,B_163,F_166,A_162,D_164] : k2_xboole_0(k2_enumset1(A_162,B_163,C_165,D_164),k1_tarski(F_166)) = k3_enumset1(A_162,B_163,C_165,D_164,F_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_759])).

tff(c_1405,plain,(
    ! [A_34,B_35,C_36,F_166] : k3_enumset1(A_34,A_34,B_35,C_36,F_166) = k2_xboole_0(k1_enumset1(A_34,B_35,C_36),k1_tarski(F_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1372])).

tff(c_6518,plain,(
    ! [A_334,B_335,C_336,F_337] : k2_xboole_0(k1_enumset1(A_334,B_335,C_336),k1_tarski(F_337)) = k2_enumset1(A_334,B_335,C_336,F_337) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1405])).

tff(c_6560,plain,(
    ! [A_32,B_33,F_337] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(F_337)) = k2_enumset1(A_32,A_32,B_33,F_337) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6518])).

tff(c_6565,plain,(
    ! [A_32,B_33,F_337] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(F_337)) = k1_enumset1(A_32,B_33,F_337) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6560])).

tff(c_586,plain,(
    ! [E_108,D_103,F_104,A_107,C_106,B_105] : k2_xboole_0(k1_enumset1(A_107,B_105,C_106),k1_enumset1(D_103,E_108,F_104)) = k4_enumset1(A_107,B_105,C_106,D_103,E_108,F_104) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_655,plain,(
    ! [E_108,B_33,D_103,F_104,A_32] : k4_enumset1(A_32,A_32,B_33,D_103,E_108,F_104) = k2_xboole_0(k2_tarski(A_32,B_33),k1_enumset1(D_103,E_108,F_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_586])).

tff(c_661,plain,(
    ! [E_108,B_33,D_103,F_104,A_32] : k2_xboole_0(k2_tarski(A_32,B_33),k1_enumset1(D_103,E_108,F_104)) = k3_enumset1(A_32,B_33,D_103,E_108,F_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_655])).

tff(c_8,plain,(
    ! [B_12,C_13,A_11] : k1_enumset1(B_12,C_13,A_11) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2741,plain,(
    ! [A_217,B_216,C_213,B_214,A_215,C_218] : k2_xboole_0(k1_enumset1(A_217,B_214,C_218),k1_enumset1(A_215,B_216,C_213)) = k4_enumset1(A_217,B_214,C_218,B_216,C_213,A_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_586])).

tff(c_2834,plain,(
    ! [B_33,B_216,C_213,A_215,A_32] : k4_enumset1(A_32,A_32,B_33,B_216,C_213,A_215) = k2_xboole_0(k2_tarski(A_32,B_33),k1_enumset1(A_215,B_216,C_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2741])).

tff(c_5409,plain,(
    ! [B_285,A_284,B_283,A_286,C_287] : k3_enumset1(A_286,B_285,B_283,C_287,A_284) = k3_enumset1(A_286,B_285,A_284,B_283,C_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_24,c_2834])).

tff(c_16,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_662,plain,(
    ! [A_113,D_109,E_111,F_112,B_110] : k2_xboole_0(k2_tarski(A_113,B_110),k1_enumset1(D_109,E_111,F_112)) = k3_enumset1(A_113,B_110,D_109,E_111,F_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_655])).

tff(c_704,plain,(
    ! [A_31,D_109,E_111,F_112] : k3_enumset1(A_31,A_31,D_109,E_111,F_112) = k2_xboole_0(k1_tarski(A_31),k1_enumset1(D_109,E_111,F_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_662])).

tff(c_708,plain,(
    ! [A_114,D_115,E_116,F_117] : k2_xboole_0(k1_tarski(A_114),k1_enumset1(D_115,E_116,F_117)) = k2_enumset1(A_114,D_115,E_116,F_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_704])).

tff(c_1023,plain,(
    ! [A_151,A_152,B_153] : k2_xboole_0(k1_tarski(A_151),k2_tarski(A_152,B_153)) = k2_enumset1(A_151,A_152,A_152,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_708])).

tff(c_1056,plain,(
    ! [A_152,B_153] : k2_xboole_0(k1_tarski(A_152),k2_tarski(A_152,B_153)) = k1_enumset1(A_152,A_152,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_20])).

tff(c_1172,plain,(
    ! [A_156,B_157] : k2_xboole_0(k1_tarski(A_156),k2_tarski(A_156,B_157)) = k2_tarski(A_156,B_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1056])).

tff(c_747,plain,(
    ! [A_114,A_32,B_33] : k2_xboole_0(k1_tarski(A_114),k2_tarski(A_32,B_33)) = k2_enumset1(A_114,A_32,A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_708])).

tff(c_1178,plain,(
    ! [A_156,B_157] : k2_enumset1(A_156,A_156,A_156,B_157) = k2_tarski(A_156,B_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_747])).

tff(c_148,plain,(
    ! [B_72,C_73,A_74] : k1_enumset1(B_72,C_73,A_74) = k1_enumset1(A_74,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_188,plain,(
    ! [A_74,C_73] : k1_enumset1(A_74,C_73,C_73) = k2_tarski(C_73,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_18])).

tff(c_763,plain,(
    ! [A_124,C_125,A_126] : k2_xboole_0(k1_tarski(A_124),k2_tarski(C_125,A_126)) = k2_enumset1(A_124,A_126,C_125,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_708])).

tff(c_860,plain,(
    ! [A_139,A_140] : k2_xboole_0(k1_tarski(A_139),k1_tarski(A_140)) = k2_enumset1(A_139,A_140,A_140,A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_763])).

tff(c_773,plain,(
    ! [A_126,C_125] : k2_xboole_0(k1_tarski(A_126),k2_tarski(C_125,A_126)) = k1_enumset1(A_126,C_125,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_20])).

tff(c_793,plain,(
    ! [A_127,C_128] : k2_xboole_0(k1_tarski(A_127),k2_tarski(C_128,A_127)) = k2_tarski(C_128,A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_773])).

tff(c_809,plain,(
    ! [A_31] : k2_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k2_tarski(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_793])).

tff(c_812,plain,(
    ! [A_31] : k2_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k1_tarski(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_809])).

tff(c_874,plain,(
    ! [A_140] : k2_enumset1(A_140,A_140,A_140,A_140) = k1_tarski(A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_812])).

tff(c_2649,plain,(
    ! [A_208,F_209] : k3_enumset1(A_208,A_208,A_208,A_208,F_209) = k2_xboole_0(k1_tarski(A_208),k1_tarski(F_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_1372])).

tff(c_2668,plain,(
    ! [A_208,F_209] : k2_xboole_0(k1_tarski(A_208),k1_tarski(F_209)) = k2_enumset1(A_208,A_208,A_208,F_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_22])).

tff(c_2687,plain,(
    ! [A_208,F_209] : k2_xboole_0(k1_tarski(A_208),k1_tarski(F_209)) = k2_tarski(A_208,F_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_2668])).

tff(c_1393,plain,(
    ! [A_140,F_166] : k3_enumset1(A_140,A_140,A_140,A_140,F_166) = k2_xboole_0(k1_tarski(A_140),k1_tarski(F_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_1372])).

tff(c_2721,plain,(
    ! [A_140,F_166] : k3_enumset1(A_140,A_140,A_140,A_140,F_166) = k2_tarski(A_140,F_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_1393])).

tff(c_5528,plain,(
    ! [C_290,A_291] : k3_enumset1(C_290,C_290,A_291,C_290,C_290) = k2_tarski(C_290,A_291) ),
    inference(superposition,[status(thm),theory(equality)],[c_5409,c_2721])).

tff(c_12,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] : k2_xboole_0(k3_enumset1(A_17,B_18,C_19,D_20,E_21),k1_tarski(F_22)) = k4_enumset1(A_17,B_18,C_19,D_20,E_21,F_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5552,plain,(
    ! [C_290,A_291,F_22] : k4_enumset1(C_290,C_290,A_291,C_290,C_290,F_22) = k2_xboole_0(k2_tarski(C_290,A_291),k1_tarski(F_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5528,c_12])).

tff(c_35626,plain,(
    ! [C_717,A_718,F_719] : k4_enumset1(C_717,C_717,A_718,C_717,C_717,F_719) = k1_enumset1(C_717,A_718,F_719) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_5552])).

tff(c_35790,plain,(
    ! [C_717,A_718,F_719] : k3_enumset1(C_717,A_718,C_717,C_717,F_719) = k1_enumset1(C_717,A_718,F_719) ),
    inference(superposition,[status(thm),theory(equality)],[c_35626,c_24])).

tff(c_2844,plain,(
    ! [B_33,B_216,C_213,A_215,A_32] : k3_enumset1(A_32,B_33,B_216,C_213,A_215) = k3_enumset1(A_32,B_33,A_215,B_216,C_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_24,c_2834])).

tff(c_52,plain,(
    ! [A_65,C_66,B_67] : k1_enumset1(A_65,C_66,B_67) = k1_enumset1(A_65,B_67,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    ! [B_67,C_66] : k1_enumset1(B_67,C_66,B_67) = k2_tarski(B_67,C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_692,plain,(
    ! [A_113,B_110,B_67,C_66] : k3_enumset1(A_113,B_110,B_67,C_66,B_67) = k2_xboole_0(k2_tarski(A_113,B_110),k2_tarski(B_67,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_662])).

tff(c_6542,plain,(
    ! [C_73,A_74,F_337] : k2_xboole_0(k2_tarski(C_73,A_74),k1_tarski(F_337)) = k2_enumset1(A_74,C_73,C_73,F_337) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6518])).

tff(c_6616,plain,(
    ! [A_348,C_349,F_350] : k2_enumset1(A_348,C_349,C_349,F_350) = k1_enumset1(C_349,A_348,F_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_6542])).

tff(c_1412,plain,(
    ! [A_167,A_168,B_169,C_170] : k2_xboole_0(k1_tarski(A_167),k1_enumset1(A_168,B_169,C_170)) = k2_enumset1(A_167,A_168,C_170,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_708])).

tff(c_707,plain,(
    ! [A_31,D_109,E_111,F_112] : k2_xboole_0(k1_tarski(A_31),k1_enumset1(D_109,E_111,F_112)) = k2_enumset1(A_31,D_109,E_111,F_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_704])).

tff(c_1418,plain,(
    ! [A_167,A_168,C_170,B_169] : k2_enumset1(A_167,A_168,C_170,B_169) = k2_enumset1(A_167,A_168,B_169,C_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_707])).

tff(c_2975,plain,(
    ! [A_221,B_222,C_223,A_224] : k2_xboole_0(k1_tarski(A_221),k1_enumset1(B_222,C_223,A_224)) = k2_enumset1(A_221,A_224,B_222,C_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_708])).

tff(c_744,plain,(
    ! [A_114,A_59,B_60,C_61] : k2_xboole_0(k1_tarski(A_114),k1_enumset1(A_59,B_60,C_61)) = k2_enumset1(A_114,A_59,C_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_708])).

tff(c_3066,plain,(
    ! [A_227,B_228,A_229,C_230] : k2_enumset1(A_227,B_228,A_229,C_230) = k2_enumset1(A_227,A_229,B_228,C_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_744])).

tff(c_3271,plain,(
    ! [A_231,B_232,C_233] : k2_enumset1(A_231,B_232,A_231,C_233) = k1_enumset1(A_231,B_232,C_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_3066,c_20])).

tff(c_3387,plain,(
    ! [C_170,A_168,B_169] : k2_enumset1(C_170,A_168,B_169,C_170) = k1_enumset1(C_170,A_168,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_1418,c_3271])).

tff(c_6643,plain,(
    ! [F_350,C_349] : k1_enumset1(F_350,C_349,C_349) = k1_enumset1(C_349,F_350,F_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_6616,c_3387])).

tff(c_6795,plain,(
    ! [F_350,C_349] : k2_tarski(F_350,C_349) = k2_tarski(C_349,F_350) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_188,c_6643])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_6880,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6795,c_6795,c_33])).

tff(c_8076,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_6880])).

tff(c_8077,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_8076])).

tff(c_36014,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35790,c_8077])).

tff(c_36017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.68/6.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.68/6.54  
% 13.68/6.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.68/6.54  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.68/6.54  
% 13.68/6.54  %Foreground sorts:
% 13.68/6.54  
% 13.68/6.54  
% 13.68/6.54  %Background operators:
% 13.68/6.54  
% 13.68/6.54  
% 13.68/6.54  %Foreground operators:
% 13.68/6.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.68/6.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.68/6.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.68/6.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.68/6.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.68/6.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.68/6.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.68/6.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.68/6.54  tff('#skF_2', type, '#skF_2': $i).
% 13.68/6.54  tff('#skF_3', type, '#skF_3': $i).
% 13.68/6.54  tff('#skF_1', type, '#skF_1': $i).
% 13.68/6.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.68/6.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.68/6.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.68/6.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.68/6.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.68/6.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.68/6.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.68/6.54  
% 13.68/6.56  tff(f_55, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 13.68/6.56  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 13.68/6.56  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.68/6.56  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 13.68/6.56  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 13.68/6.56  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 13.68/6.56  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 13.68/6.56  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 13.68/6.56  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.68/6.56  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 13.68/6.56  tff(c_30, plain, (![A_59, C_61, B_60]: (k1_enumset1(A_59, C_61, B_60)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.68/6.56  tff(c_20, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.68/6.56  tff(c_18, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.68/6.56  tff(c_22, plain, (![A_37, B_38, C_39, D_40]: (k3_enumset1(A_37, A_37, B_38, C_39, D_40)=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.68/6.56  tff(c_24, plain, (![D_44, C_43, A_41, B_42, E_45]: (k4_enumset1(A_41, A_41, B_42, C_43, D_44, E_45)=k3_enumset1(A_41, B_42, C_43, D_44, E_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.68/6.56  tff(c_750, plain, (![D_122, A_119, F_121, B_120, E_123, C_118]: (k2_xboole_0(k3_enumset1(A_119, B_120, C_118, D_122, E_123), k1_tarski(F_121))=k4_enumset1(A_119, B_120, C_118, D_122, E_123, F_121))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.68/6.56  tff(c_759, plain, (![C_39, B_38, A_37, D_40, F_121]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, F_121)=k2_xboole_0(k2_enumset1(A_37, B_38, C_39, D_40), k1_tarski(F_121)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_750])).
% 13.68/6.56  tff(c_1372, plain, (![C_165, B_163, F_166, A_162, D_164]: (k2_xboole_0(k2_enumset1(A_162, B_163, C_165, D_164), k1_tarski(F_166))=k3_enumset1(A_162, B_163, C_165, D_164, F_166))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_759])).
% 13.68/6.56  tff(c_1405, plain, (![A_34, B_35, C_36, F_166]: (k3_enumset1(A_34, A_34, B_35, C_36, F_166)=k2_xboole_0(k1_enumset1(A_34, B_35, C_36), k1_tarski(F_166)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1372])).
% 13.68/6.56  tff(c_6518, plain, (![A_334, B_335, C_336, F_337]: (k2_xboole_0(k1_enumset1(A_334, B_335, C_336), k1_tarski(F_337))=k2_enumset1(A_334, B_335, C_336, F_337))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1405])).
% 13.68/6.56  tff(c_6560, plain, (![A_32, B_33, F_337]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(F_337))=k2_enumset1(A_32, A_32, B_33, F_337))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6518])).
% 13.68/6.56  tff(c_6565, plain, (![A_32, B_33, F_337]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(F_337))=k1_enumset1(A_32, B_33, F_337))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6560])).
% 13.68/6.56  tff(c_586, plain, (![E_108, D_103, F_104, A_107, C_106, B_105]: (k2_xboole_0(k1_enumset1(A_107, B_105, C_106), k1_enumset1(D_103, E_108, F_104))=k4_enumset1(A_107, B_105, C_106, D_103, E_108, F_104))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.68/6.56  tff(c_655, plain, (![E_108, B_33, D_103, F_104, A_32]: (k4_enumset1(A_32, A_32, B_33, D_103, E_108, F_104)=k2_xboole_0(k2_tarski(A_32, B_33), k1_enumset1(D_103, E_108, F_104)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_586])).
% 13.68/6.56  tff(c_661, plain, (![E_108, B_33, D_103, F_104, A_32]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_enumset1(D_103, E_108, F_104))=k3_enumset1(A_32, B_33, D_103, E_108, F_104))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_655])).
% 13.68/6.56  tff(c_8, plain, (![B_12, C_13, A_11]: (k1_enumset1(B_12, C_13, A_11)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.68/6.56  tff(c_2741, plain, (![A_217, B_216, C_213, B_214, A_215, C_218]: (k2_xboole_0(k1_enumset1(A_217, B_214, C_218), k1_enumset1(A_215, B_216, C_213))=k4_enumset1(A_217, B_214, C_218, B_216, C_213, A_215))), inference(superposition, [status(thm), theory('equality')], [c_8, c_586])).
% 13.68/6.56  tff(c_2834, plain, (![B_33, B_216, C_213, A_215, A_32]: (k4_enumset1(A_32, A_32, B_33, B_216, C_213, A_215)=k2_xboole_0(k2_tarski(A_32, B_33), k1_enumset1(A_215, B_216, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2741])).
% 13.68/6.56  tff(c_5409, plain, (![B_285, A_284, B_283, A_286, C_287]: (k3_enumset1(A_286, B_285, B_283, C_287, A_284)=k3_enumset1(A_286, B_285, A_284, B_283, C_287))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_24, c_2834])).
% 13.68/6.56  tff(c_16, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.68/6.56  tff(c_662, plain, (![A_113, D_109, E_111, F_112, B_110]: (k2_xboole_0(k2_tarski(A_113, B_110), k1_enumset1(D_109, E_111, F_112))=k3_enumset1(A_113, B_110, D_109, E_111, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_655])).
% 13.68/6.56  tff(c_704, plain, (![A_31, D_109, E_111, F_112]: (k3_enumset1(A_31, A_31, D_109, E_111, F_112)=k2_xboole_0(k1_tarski(A_31), k1_enumset1(D_109, E_111, F_112)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_662])).
% 13.68/6.56  tff(c_708, plain, (![A_114, D_115, E_116, F_117]: (k2_xboole_0(k1_tarski(A_114), k1_enumset1(D_115, E_116, F_117))=k2_enumset1(A_114, D_115, E_116, F_117))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_704])).
% 13.68/6.56  tff(c_1023, plain, (![A_151, A_152, B_153]: (k2_xboole_0(k1_tarski(A_151), k2_tarski(A_152, B_153))=k2_enumset1(A_151, A_152, A_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_18, c_708])).
% 13.68/6.56  tff(c_1056, plain, (![A_152, B_153]: (k2_xboole_0(k1_tarski(A_152), k2_tarski(A_152, B_153))=k1_enumset1(A_152, A_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_1023, c_20])).
% 13.68/6.56  tff(c_1172, plain, (![A_156, B_157]: (k2_xboole_0(k1_tarski(A_156), k2_tarski(A_156, B_157))=k2_tarski(A_156, B_157))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1056])).
% 13.68/6.56  tff(c_747, plain, (![A_114, A_32, B_33]: (k2_xboole_0(k1_tarski(A_114), k2_tarski(A_32, B_33))=k2_enumset1(A_114, A_32, A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_18, c_708])).
% 13.68/6.56  tff(c_1178, plain, (![A_156, B_157]: (k2_enumset1(A_156, A_156, A_156, B_157)=k2_tarski(A_156, B_157))), inference(superposition, [status(thm), theory('equality')], [c_1172, c_747])).
% 13.68/6.56  tff(c_148, plain, (![B_72, C_73, A_74]: (k1_enumset1(B_72, C_73, A_74)=k1_enumset1(A_74, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.68/6.56  tff(c_188, plain, (![A_74, C_73]: (k1_enumset1(A_74, C_73, C_73)=k2_tarski(C_73, A_74))), inference(superposition, [status(thm), theory('equality')], [c_148, c_18])).
% 13.68/6.56  tff(c_763, plain, (![A_124, C_125, A_126]: (k2_xboole_0(k1_tarski(A_124), k2_tarski(C_125, A_126))=k2_enumset1(A_124, A_126, C_125, C_125))), inference(superposition, [status(thm), theory('equality')], [c_188, c_708])).
% 13.68/6.56  tff(c_860, plain, (![A_139, A_140]: (k2_xboole_0(k1_tarski(A_139), k1_tarski(A_140))=k2_enumset1(A_139, A_140, A_140, A_140))), inference(superposition, [status(thm), theory('equality')], [c_16, c_763])).
% 13.68/6.56  tff(c_773, plain, (![A_126, C_125]: (k2_xboole_0(k1_tarski(A_126), k2_tarski(C_125, A_126))=k1_enumset1(A_126, C_125, C_125))), inference(superposition, [status(thm), theory('equality')], [c_763, c_20])).
% 13.68/6.56  tff(c_793, plain, (![A_127, C_128]: (k2_xboole_0(k1_tarski(A_127), k2_tarski(C_128, A_127))=k2_tarski(C_128, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_773])).
% 13.68/6.56  tff(c_809, plain, (![A_31]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k2_tarski(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_16, c_793])).
% 13.68/6.56  tff(c_812, plain, (![A_31]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k1_tarski(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_809])).
% 13.68/6.56  tff(c_874, plain, (![A_140]: (k2_enumset1(A_140, A_140, A_140, A_140)=k1_tarski(A_140))), inference(superposition, [status(thm), theory('equality')], [c_860, c_812])).
% 13.68/6.56  tff(c_2649, plain, (![A_208, F_209]: (k3_enumset1(A_208, A_208, A_208, A_208, F_209)=k2_xboole_0(k1_tarski(A_208), k1_tarski(F_209)))), inference(superposition, [status(thm), theory('equality')], [c_874, c_1372])).
% 13.68/6.56  tff(c_2668, plain, (![A_208, F_209]: (k2_xboole_0(k1_tarski(A_208), k1_tarski(F_209))=k2_enumset1(A_208, A_208, A_208, F_209))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_22])).
% 13.68/6.56  tff(c_2687, plain, (![A_208, F_209]: (k2_xboole_0(k1_tarski(A_208), k1_tarski(F_209))=k2_tarski(A_208, F_209))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_2668])).
% 13.68/6.56  tff(c_1393, plain, (![A_140, F_166]: (k3_enumset1(A_140, A_140, A_140, A_140, F_166)=k2_xboole_0(k1_tarski(A_140), k1_tarski(F_166)))), inference(superposition, [status(thm), theory('equality')], [c_874, c_1372])).
% 13.68/6.56  tff(c_2721, plain, (![A_140, F_166]: (k3_enumset1(A_140, A_140, A_140, A_140, F_166)=k2_tarski(A_140, F_166))), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_1393])).
% 13.68/6.56  tff(c_5528, plain, (![C_290, A_291]: (k3_enumset1(C_290, C_290, A_291, C_290, C_290)=k2_tarski(C_290, A_291))), inference(superposition, [status(thm), theory('equality')], [c_5409, c_2721])).
% 13.68/6.56  tff(c_12, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (k2_xboole_0(k3_enumset1(A_17, B_18, C_19, D_20, E_21), k1_tarski(F_22))=k4_enumset1(A_17, B_18, C_19, D_20, E_21, F_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.68/6.56  tff(c_5552, plain, (![C_290, A_291, F_22]: (k4_enumset1(C_290, C_290, A_291, C_290, C_290, F_22)=k2_xboole_0(k2_tarski(C_290, A_291), k1_tarski(F_22)))), inference(superposition, [status(thm), theory('equality')], [c_5528, c_12])).
% 13.68/6.56  tff(c_35626, plain, (![C_717, A_718, F_719]: (k4_enumset1(C_717, C_717, A_718, C_717, C_717, F_719)=k1_enumset1(C_717, A_718, F_719))), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_5552])).
% 13.68/6.56  tff(c_35790, plain, (![C_717, A_718, F_719]: (k3_enumset1(C_717, A_718, C_717, C_717, F_719)=k1_enumset1(C_717, A_718, F_719))), inference(superposition, [status(thm), theory('equality')], [c_35626, c_24])).
% 13.68/6.56  tff(c_2844, plain, (![B_33, B_216, C_213, A_215, A_32]: (k3_enumset1(A_32, B_33, B_216, C_213, A_215)=k3_enumset1(A_32, B_33, A_215, B_216, C_213))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_24, c_2834])).
% 13.68/6.56  tff(c_52, plain, (![A_65, C_66, B_67]: (k1_enumset1(A_65, C_66, B_67)=k1_enumset1(A_65, B_67, C_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.68/6.56  tff(c_68, plain, (![B_67, C_66]: (k1_enumset1(B_67, C_66, B_67)=k2_tarski(B_67, C_66))), inference(superposition, [status(thm), theory('equality')], [c_52, c_18])).
% 13.68/6.56  tff(c_692, plain, (![A_113, B_110, B_67, C_66]: (k3_enumset1(A_113, B_110, B_67, C_66, B_67)=k2_xboole_0(k2_tarski(A_113, B_110), k2_tarski(B_67, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_662])).
% 13.68/6.56  tff(c_6542, plain, (![C_73, A_74, F_337]: (k2_xboole_0(k2_tarski(C_73, A_74), k1_tarski(F_337))=k2_enumset1(A_74, C_73, C_73, F_337))), inference(superposition, [status(thm), theory('equality')], [c_188, c_6518])).
% 13.68/6.56  tff(c_6616, plain, (![A_348, C_349, F_350]: (k2_enumset1(A_348, C_349, C_349, F_350)=k1_enumset1(C_349, A_348, F_350))), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_6542])).
% 13.68/6.56  tff(c_1412, plain, (![A_167, A_168, B_169, C_170]: (k2_xboole_0(k1_tarski(A_167), k1_enumset1(A_168, B_169, C_170))=k2_enumset1(A_167, A_168, C_170, B_169))), inference(superposition, [status(thm), theory('equality')], [c_30, c_708])).
% 13.68/6.56  tff(c_707, plain, (![A_31, D_109, E_111, F_112]: (k2_xboole_0(k1_tarski(A_31), k1_enumset1(D_109, E_111, F_112))=k2_enumset1(A_31, D_109, E_111, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_704])).
% 13.68/6.56  tff(c_1418, plain, (![A_167, A_168, C_170, B_169]: (k2_enumset1(A_167, A_168, C_170, B_169)=k2_enumset1(A_167, A_168, B_169, C_170))), inference(superposition, [status(thm), theory('equality')], [c_1412, c_707])).
% 13.68/6.56  tff(c_2975, plain, (![A_221, B_222, C_223, A_224]: (k2_xboole_0(k1_tarski(A_221), k1_enumset1(B_222, C_223, A_224))=k2_enumset1(A_221, A_224, B_222, C_223))), inference(superposition, [status(thm), theory('equality')], [c_8, c_708])).
% 13.68/6.56  tff(c_744, plain, (![A_114, A_59, B_60, C_61]: (k2_xboole_0(k1_tarski(A_114), k1_enumset1(A_59, B_60, C_61))=k2_enumset1(A_114, A_59, C_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_30, c_708])).
% 13.68/6.56  tff(c_3066, plain, (![A_227, B_228, A_229, C_230]: (k2_enumset1(A_227, B_228, A_229, C_230)=k2_enumset1(A_227, A_229, B_228, C_230))), inference(superposition, [status(thm), theory('equality')], [c_2975, c_744])).
% 13.68/6.56  tff(c_3271, plain, (![A_231, B_232, C_233]: (k2_enumset1(A_231, B_232, A_231, C_233)=k1_enumset1(A_231, B_232, C_233))), inference(superposition, [status(thm), theory('equality')], [c_3066, c_20])).
% 13.68/6.56  tff(c_3387, plain, (![C_170, A_168, B_169]: (k2_enumset1(C_170, A_168, B_169, C_170)=k1_enumset1(C_170, A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_1418, c_3271])).
% 13.68/6.56  tff(c_6643, plain, (![F_350, C_349]: (k1_enumset1(F_350, C_349, C_349)=k1_enumset1(C_349, F_350, F_350))), inference(superposition, [status(thm), theory('equality')], [c_6616, c_3387])).
% 13.68/6.56  tff(c_6795, plain, (![F_350, C_349]: (k2_tarski(F_350, C_349)=k2_tarski(C_349, F_350))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_188, c_6643])).
% 13.68/6.56  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.68/6.56  tff(c_33, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 13.68/6.56  tff(c_6880, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6795, c_6795, c_33])).
% 13.68/6.56  tff(c_8076, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_6880])).
% 13.68/6.56  tff(c_8077, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_8076])).
% 13.68/6.56  tff(c_36014, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35790, c_8077])).
% 13.68/6.56  tff(c_36017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_36014])).
% 13.68/6.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.68/6.56  
% 13.68/6.56  Inference rules
% 13.68/6.56  ----------------------
% 13.68/6.56  #Ref     : 0
% 13.68/6.56  #Sup     : 8978
% 13.68/6.56  #Fact    : 0
% 13.68/6.56  #Define  : 0
% 13.68/6.57  #Split   : 0
% 13.68/6.57  #Chain   : 0
% 13.68/6.57  #Close   : 0
% 13.68/6.57  
% 13.68/6.57  Ordering : KBO
% 13.68/6.57  
% 13.68/6.57  Simplification rules
% 13.68/6.57  ----------------------
% 13.68/6.57  #Subsume      : 1932
% 13.68/6.57  #Demod        : 6807
% 13.68/6.57  #Tautology    : 5043
% 13.68/6.57  #SimpNegUnit  : 0
% 13.68/6.57  #BackRed      : 11
% 13.68/6.57  
% 13.68/6.57  #Partial instantiations: 0
% 13.68/6.57  #Strategies tried      : 1
% 13.68/6.57  
% 13.68/6.57  Timing (in seconds)
% 13.68/6.57  ----------------------
% 13.68/6.57  Preprocessing        : 0.37
% 13.68/6.57  Parsing              : 0.19
% 13.68/6.57  CNF conversion       : 0.02
% 13.68/6.57  Main loop            : 5.34
% 13.68/6.57  Inferencing          : 1.12
% 13.68/6.57  Reduction            : 3.33
% 13.68/6.57  Demodulation         : 3.12
% 13.68/6.57  BG Simplification    : 0.11
% 13.68/6.57  Subsumption          : 0.62
% 13.68/6.57  Abstraction          : 0.20
% 13.68/6.57  MUC search           : 0.00
% 13.68/6.57  Cooper               : 0.00
% 13.68/6.57  Total                : 5.76
% 13.68/6.57  Index Insertion      : 0.00
% 13.68/6.57  Index Deletion       : 0.00
% 13.68/6.57  Index Matching       : 0.00
% 13.68/6.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

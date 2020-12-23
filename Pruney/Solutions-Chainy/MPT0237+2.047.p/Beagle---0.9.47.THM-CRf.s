%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   85 (1056 expanded)
%              Number of leaves         :   30 ( 371 expanded)
%              Depth                    :   24
%              Number of atoms          :   67 (1038 expanded)
%              Number of equality atoms :   66 (1037 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49) = k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [H_100,A_99,E_96,B_102,C_101,G_95,D_97,F_98] : k2_xboole_0(k2_enumset1(A_99,B_102,C_101,D_97),k2_enumset1(E_96,F_98,G_95,H_100)) = k6_enumset1(A_99,B_102,C_101,D_97,E_96,F_98,G_95,H_100) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = k2_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_37])).

tff(c_225,plain,(
    ! [E_112,F_113,G_114,H_115] : k6_enumset1(E_112,F_113,G_114,H_115,E_112,F_113,G_114,H_115) = k3_tarski(k1_tarski(k2_enumset1(E_112,F_113,G_114,H_115))) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_46])).

tff(c_22,plain,(
    ! [A_50,B_51,G_56,E_54,C_52,D_53,F_55] : k6_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,G_56) = k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,G_56) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [F_113,G_114,H_115] : k5_enumset1(F_113,G_114,H_115,F_113,F_113,G_114,H_115) = k3_tarski(k1_tarski(k2_enumset1(F_113,F_113,G_114,H_115))) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_22])).

tff(c_261,plain,(
    ! [F_116,G_117,H_118] : k5_enumset1(F_116,G_117,H_118,F_116,F_116,G_117,H_118) = k3_tarski(k1_tarski(k1_enumset1(F_116,G_117,H_118))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_241])).

tff(c_274,plain,(
    ! [G_117,H_118] : k4_enumset1(G_117,H_118,G_117,G_117,G_117,H_118) = k3_tarski(k1_tarski(k1_enumset1(G_117,G_117,H_118))) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_20])).

tff(c_294,plain,(
    ! [G_119,H_120] : k4_enumset1(G_119,H_120,G_119,G_119,G_119,H_120) = k3_tarski(k1_tarski(k2_tarski(G_119,H_120))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_274])).

tff(c_307,plain,(
    ! [H_120] : k3_tarski(k1_tarski(k2_tarski(H_120,H_120))) = k3_enumset1(H_120,H_120,H_120,H_120,H_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_18])).

tff(c_346,plain,(
    ! [H_130] : k3_tarski(k1_tarski(k1_tarski(H_130))) = k3_enumset1(H_130,H_130,H_130,H_130,H_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_307])).

tff(c_377,plain,(
    ! [H_131] : k3_tarski(k1_tarski(k1_tarski(H_131))) = k2_enumset1(H_131,H_131,H_131,H_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_16])).

tff(c_323,plain,(
    ! [H_120] : k3_tarski(k1_tarski(k1_tarski(H_120))) = k3_enumset1(H_120,H_120,H_120,H_120,H_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_307])).

tff(c_386,plain,(
    ! [H_131] : k3_enumset1(H_131,H_131,H_131,H_131,H_131) = k2_enumset1(H_131,H_131,H_131,H_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_323])).

tff(c_420,plain,(
    ! [H_131] : k3_enumset1(H_131,H_131,H_131,H_131,H_131) = k1_tarski(H_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_14,c_386])).

tff(c_425,plain,(
    ! [H_120] : k3_tarski(k1_tarski(k1_tarski(H_120))) = k1_tarski(H_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_323])).

tff(c_361,plain,(
    ! [H_130] : k3_tarski(k1_tarski(k1_tarski(H_130))) = k2_enumset1(H_130,H_130,H_130,H_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_16])).

tff(c_458,plain,(
    ! [H_134] : k2_enumset1(H_134,H_134,H_134,H_134) = k1_tarski(H_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_361])).

tff(c_509,plain,(
    ! [H_142] : k1_enumset1(H_142,H_142,H_142) = k1_tarski(H_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14])).

tff(c_257,plain,(
    ! [F_113,G_114,H_115] : k5_enumset1(F_113,G_114,H_115,F_113,F_113,G_114,H_115) = k3_tarski(k1_tarski(k1_enumset1(F_113,G_114,H_115))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_241])).

tff(c_518,plain,(
    ! [H_142] : k5_enumset1(H_142,H_142,H_142,H_142,H_142,H_142,H_142) = k3_tarski(k1_tarski(k1_tarski(H_142))) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_257])).

tff(c_530,plain,(
    ! [H_142] : k5_enumset1(H_142,H_142,H_142,H_142,H_142,H_142,H_142) = k1_tarski(H_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_518])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,H_10,G_9,E_7,B_4] : k2_xboole_0(k2_enumset1(A_3,B_4,C_5,D_6),k2_enumset1(E_7,F_8,G_9,H_10)) = k6_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9,H_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_327,plain,(
    ! [B_126,D_127,H_129,I_121,G_124,C_123,F_122,A_125,E_128] : k2_xboole_0(k3_enumset1(A_125,B_126,C_123,D_127,E_128),k2_enumset1(F_122,G_124,H_129,I_121)) = k7_enumset1(A_125,B_126,C_123,D_127,E_128,F_122,G_124,H_129,I_121) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_339,plain,(
    ! [A_35,B_36,C_37,D_38,H_129,I_121,G_124,F_122] : k7_enumset1(A_35,A_35,B_36,C_37,D_38,F_122,G_124,H_129,I_121) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k2_enumset1(F_122,G_124,H_129,I_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_327])).

tff(c_345,plain,(
    ! [A_35,B_36,C_37,D_38,H_129,I_121,G_124,F_122] : k7_enumset1(A_35,A_35,B_36,C_37,D_38,F_122,G_124,H_129,I_121) = k6_enumset1(A_35,B_36,C_37,D_38,F_122,G_124,H_129,I_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_339])).

tff(c_210,plain,(
    ! [E_108,C_103,I_106,A_109,D_107,F_110,H_111,B_105,G_104] : k2_xboole_0(k6_enumset1(A_109,B_105,C_103,D_107,E_108,F_110,G_104,H_111),k1_tarski(I_106)) = k7_enumset1(A_109,B_105,C_103,D_107,E_108,F_110,G_104,H_111,I_106) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_222,plain,(
    ! [A_50,I_106,B_51,G_56,E_54,C_52,D_53,F_55] : k7_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,G_56,I_106) = k2_xboole_0(k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,G_56),k1_tarski(I_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_210])).

tff(c_1193,plain,(
    ! [I_182,D_188,E_181,C_184,F_187,B_186,A_183,G_185] : k2_xboole_0(k5_enumset1(A_183,B_186,C_184,D_188,E_181,F_187,G_185),k1_tarski(I_182)) = k6_enumset1(A_183,B_186,C_184,D_188,E_181,F_187,G_185,I_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_222])).

tff(c_1464,plain,(
    ! [H_201,I_202] : k6_enumset1(H_201,H_201,H_201,H_201,H_201,H_201,H_201,I_202) = k2_xboole_0(k1_tarski(H_201),k1_tarski(I_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1193])).

tff(c_1597,plain,(
    ! [H_205,I_206] : k5_enumset1(H_205,H_205,H_205,H_205,H_205,H_205,I_206) = k2_xboole_0(k1_tarski(H_205),k1_tarski(I_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_22])).

tff(c_1214,plain,(
    ! [H_142,I_182] : k6_enumset1(H_142,H_142,H_142,H_142,H_142,H_142,H_142,I_182) = k2_xboole_0(k1_tarski(H_142),k1_tarski(I_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1193])).

tff(c_1606,plain,(
    ! [H_205,I_206] : k6_enumset1(H_205,H_205,H_205,H_205,H_205,H_205,H_205,I_206) = k5_enumset1(H_205,H_205,H_205,H_205,H_205,H_205,I_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_1214])).

tff(c_1711,plain,(
    ! [H_205,I_206] : k6_enumset1(H_205,H_205,H_205,H_205,H_205,H_205,H_205,I_206) = k2_tarski(H_205,I_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_16,c_18,c_20,c_1606])).

tff(c_1732,plain,(
    ! [H_142,I_182] : k2_xboole_0(k1_tarski(H_142),k1_tarski(I_182)) = k2_tarski(H_142,I_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1214])).

tff(c_445,plain,(
    ! [H_130] : k2_enumset1(H_130,H_130,H_130,H_130) = k1_tarski(H_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_361])).

tff(c_199,plain,(
    ! [B_33,C_34,H_100,E_96,G_95,A_32,F_98] : k6_enumset1(A_32,A_32,B_33,C_34,E_96,F_98,G_95,H_100) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k2_enumset1(E_96,F_98,G_95,H_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_183])).

tff(c_487,plain,(
    ! [E_140,B_136,A_139,G_135,H_141,F_137,C_138] : k2_xboole_0(k1_enumset1(A_139,B_136,C_138),k2_enumset1(E_140,F_137,G_135,H_141)) = k5_enumset1(A_139,B_136,C_138,E_140,F_137,G_135,H_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_199])).

tff(c_916,plain,(
    ! [A_168,B_169,C_170,H_171] : k5_enumset1(A_168,B_169,C_170,H_171,H_171,H_171,H_171) = k2_xboole_0(k1_enumset1(A_168,B_169,C_170),k1_tarski(H_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_487])).

tff(c_941,plain,(
    ! [B_169,C_170,H_171] : k4_enumset1(B_169,C_170,H_171,H_171,H_171,H_171) = k2_xboole_0(k1_enumset1(B_169,B_169,C_170),k1_tarski(H_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_20])).

tff(c_1050,plain,(
    ! [B_175,C_176,H_177] : k4_enumset1(B_175,C_176,H_177,H_177,H_177,H_177) = k2_xboole_0(k2_tarski(B_175,C_176),k1_tarski(H_177)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_941])).

tff(c_1074,plain,(
    ! [C_176,H_177] : k3_enumset1(C_176,H_177,H_177,H_177,H_177) = k2_xboole_0(k2_tarski(C_176,C_176),k1_tarski(H_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_18])).

tff(c_1103,plain,(
    ! [C_176,H_177] : k3_enumset1(C_176,H_177,H_177,H_177,H_177) = k2_xboole_0(k1_tarski(C_176),k1_tarski(H_177)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1074])).

tff(c_1804,plain,(
    ! [C_176,H_177] : k3_enumset1(C_176,H_177,H_177,H_177,H_177) = k2_tarski(C_176,H_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_1103])).

tff(c_24,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_1110,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_27])).

tff(c_1878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_1110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:23:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.58  
% 3.65/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.59  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 3.65/1.59  
% 3.65/1.59  %Foreground sorts:
% 3.65/1.59  
% 3.65/1.59  
% 3.65/1.59  %Background operators:
% 3.65/1.59  
% 3.65/1.59  
% 3.65/1.59  %Foreground operators:
% 3.65/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.65/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.65/1.59  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.65/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.65/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.65/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.65/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.65/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.59  
% 3.65/1.60  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.65/1.60  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.65/1.60  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.65/1.60  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.65/1.60  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.65/1.60  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.65/1.60  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 3.65/1.60  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.65/1.60  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.65/1.60  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 3.65/1.60  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 3.65/1.60  tff(f_52, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.65/1.60  tff(c_12, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.60  tff(c_14, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.60  tff(c_16, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.60  tff(c_18, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/1.60  tff(c_20, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.65/1.60  tff(c_10, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.60  tff(c_183, plain, (![H_100, A_99, E_96, B_102, C_101, G_95, D_97, F_98]: (k2_xboole_0(k2_enumset1(A_99, B_102, C_101, D_97), k2_enumset1(E_96, F_98, G_95, H_100))=k6_enumset1(A_99, B_102, C_101, D_97, E_96, F_98, G_95, H_100))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.60  tff(c_37, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.65/1.60  tff(c_46, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=k2_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_10, c_37])).
% 3.65/1.60  tff(c_225, plain, (![E_112, F_113, G_114, H_115]: (k6_enumset1(E_112, F_113, G_114, H_115, E_112, F_113, G_114, H_115)=k3_tarski(k1_tarski(k2_enumset1(E_112, F_113, G_114, H_115))))), inference(superposition, [status(thm), theory('equality')], [c_183, c_46])).
% 3.65/1.60  tff(c_22, plain, (![A_50, B_51, G_56, E_54, C_52, D_53, F_55]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56)=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.60  tff(c_241, plain, (![F_113, G_114, H_115]: (k5_enumset1(F_113, G_114, H_115, F_113, F_113, G_114, H_115)=k3_tarski(k1_tarski(k2_enumset1(F_113, F_113, G_114, H_115))))), inference(superposition, [status(thm), theory('equality')], [c_225, c_22])).
% 3.65/1.60  tff(c_261, plain, (![F_116, G_117, H_118]: (k5_enumset1(F_116, G_117, H_118, F_116, F_116, G_117, H_118)=k3_tarski(k1_tarski(k1_enumset1(F_116, G_117, H_118))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_241])).
% 3.65/1.60  tff(c_274, plain, (![G_117, H_118]: (k4_enumset1(G_117, H_118, G_117, G_117, G_117, H_118)=k3_tarski(k1_tarski(k1_enumset1(G_117, G_117, H_118))))), inference(superposition, [status(thm), theory('equality')], [c_261, c_20])).
% 3.65/1.60  tff(c_294, plain, (![G_119, H_120]: (k4_enumset1(G_119, H_120, G_119, G_119, G_119, H_120)=k3_tarski(k1_tarski(k2_tarski(G_119, H_120))))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_274])).
% 3.65/1.60  tff(c_307, plain, (![H_120]: (k3_tarski(k1_tarski(k2_tarski(H_120, H_120)))=k3_enumset1(H_120, H_120, H_120, H_120, H_120))), inference(superposition, [status(thm), theory('equality')], [c_294, c_18])).
% 3.65/1.60  tff(c_346, plain, (![H_130]: (k3_tarski(k1_tarski(k1_tarski(H_130)))=k3_enumset1(H_130, H_130, H_130, H_130, H_130))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_307])).
% 3.65/1.60  tff(c_377, plain, (![H_131]: (k3_tarski(k1_tarski(k1_tarski(H_131)))=k2_enumset1(H_131, H_131, H_131, H_131))), inference(superposition, [status(thm), theory('equality')], [c_346, c_16])).
% 3.65/1.60  tff(c_323, plain, (![H_120]: (k3_tarski(k1_tarski(k1_tarski(H_120)))=k3_enumset1(H_120, H_120, H_120, H_120, H_120))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_307])).
% 3.65/1.60  tff(c_386, plain, (![H_131]: (k3_enumset1(H_131, H_131, H_131, H_131, H_131)=k2_enumset1(H_131, H_131, H_131, H_131))), inference(superposition, [status(thm), theory('equality')], [c_377, c_323])).
% 3.65/1.60  tff(c_420, plain, (![H_131]: (k3_enumset1(H_131, H_131, H_131, H_131, H_131)=k1_tarski(H_131))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_14, c_386])).
% 3.65/1.60  tff(c_425, plain, (![H_120]: (k3_tarski(k1_tarski(k1_tarski(H_120)))=k1_tarski(H_120))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_323])).
% 3.65/1.60  tff(c_361, plain, (![H_130]: (k3_tarski(k1_tarski(k1_tarski(H_130)))=k2_enumset1(H_130, H_130, H_130, H_130))), inference(superposition, [status(thm), theory('equality')], [c_346, c_16])).
% 3.65/1.60  tff(c_458, plain, (![H_134]: (k2_enumset1(H_134, H_134, H_134, H_134)=k1_tarski(H_134))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_361])).
% 3.65/1.60  tff(c_509, plain, (![H_142]: (k1_enumset1(H_142, H_142, H_142)=k1_tarski(H_142))), inference(superposition, [status(thm), theory('equality')], [c_458, c_14])).
% 3.65/1.60  tff(c_257, plain, (![F_113, G_114, H_115]: (k5_enumset1(F_113, G_114, H_115, F_113, F_113, G_114, H_115)=k3_tarski(k1_tarski(k1_enumset1(F_113, G_114, H_115))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_241])).
% 3.65/1.60  tff(c_518, plain, (![H_142]: (k5_enumset1(H_142, H_142, H_142, H_142, H_142, H_142, H_142)=k3_tarski(k1_tarski(k1_tarski(H_142))))), inference(superposition, [status(thm), theory('equality')], [c_509, c_257])).
% 3.65/1.60  tff(c_530, plain, (![H_142]: (k5_enumset1(H_142, H_142, H_142, H_142, H_142, H_142, H_142)=k1_tarski(H_142))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_518])).
% 3.65/1.60  tff(c_4, plain, (![A_3, F_8, D_6, C_5, H_10, G_9, E_7, B_4]: (k2_xboole_0(k2_enumset1(A_3, B_4, C_5, D_6), k2_enumset1(E_7, F_8, G_9, H_10))=k6_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9, H_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.60  tff(c_327, plain, (![B_126, D_127, H_129, I_121, G_124, C_123, F_122, A_125, E_128]: (k2_xboole_0(k3_enumset1(A_125, B_126, C_123, D_127, E_128), k2_enumset1(F_122, G_124, H_129, I_121))=k7_enumset1(A_125, B_126, C_123, D_127, E_128, F_122, G_124, H_129, I_121))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.60  tff(c_339, plain, (![A_35, B_36, C_37, D_38, H_129, I_121, G_124, F_122]: (k7_enumset1(A_35, A_35, B_36, C_37, D_38, F_122, G_124, H_129, I_121)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k2_enumset1(F_122, G_124, H_129, I_121)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_327])).
% 3.65/1.60  tff(c_345, plain, (![A_35, B_36, C_37, D_38, H_129, I_121, G_124, F_122]: (k7_enumset1(A_35, A_35, B_36, C_37, D_38, F_122, G_124, H_129, I_121)=k6_enumset1(A_35, B_36, C_37, D_38, F_122, G_124, H_129, I_121))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_339])).
% 3.65/1.60  tff(c_210, plain, (![E_108, C_103, I_106, A_109, D_107, F_110, H_111, B_105, G_104]: (k2_xboole_0(k6_enumset1(A_109, B_105, C_103, D_107, E_108, F_110, G_104, H_111), k1_tarski(I_106))=k7_enumset1(A_109, B_105, C_103, D_107, E_108, F_110, G_104, H_111, I_106))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.60  tff(c_222, plain, (![A_50, I_106, B_51, G_56, E_54, C_52, D_53, F_55]: (k7_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56, I_106)=k2_xboole_0(k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56), k1_tarski(I_106)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_210])).
% 3.65/1.60  tff(c_1193, plain, (![I_182, D_188, E_181, C_184, F_187, B_186, A_183, G_185]: (k2_xboole_0(k5_enumset1(A_183, B_186, C_184, D_188, E_181, F_187, G_185), k1_tarski(I_182))=k6_enumset1(A_183, B_186, C_184, D_188, E_181, F_187, G_185, I_182))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_222])).
% 3.65/1.60  tff(c_1464, plain, (![H_201, I_202]: (k6_enumset1(H_201, H_201, H_201, H_201, H_201, H_201, H_201, I_202)=k2_xboole_0(k1_tarski(H_201), k1_tarski(I_202)))), inference(superposition, [status(thm), theory('equality')], [c_530, c_1193])).
% 3.65/1.60  tff(c_1597, plain, (![H_205, I_206]: (k5_enumset1(H_205, H_205, H_205, H_205, H_205, H_205, I_206)=k2_xboole_0(k1_tarski(H_205), k1_tarski(I_206)))), inference(superposition, [status(thm), theory('equality')], [c_1464, c_22])).
% 3.65/1.60  tff(c_1214, plain, (![H_142, I_182]: (k6_enumset1(H_142, H_142, H_142, H_142, H_142, H_142, H_142, I_182)=k2_xboole_0(k1_tarski(H_142), k1_tarski(I_182)))), inference(superposition, [status(thm), theory('equality')], [c_530, c_1193])).
% 3.65/1.60  tff(c_1606, plain, (![H_205, I_206]: (k6_enumset1(H_205, H_205, H_205, H_205, H_205, H_205, H_205, I_206)=k5_enumset1(H_205, H_205, H_205, H_205, H_205, H_205, I_206))), inference(superposition, [status(thm), theory('equality')], [c_1597, c_1214])).
% 3.65/1.60  tff(c_1711, plain, (![H_205, I_206]: (k6_enumset1(H_205, H_205, H_205, H_205, H_205, H_205, H_205, I_206)=k2_tarski(H_205, I_206))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_16, c_18, c_20, c_1606])).
% 3.65/1.60  tff(c_1732, plain, (![H_142, I_182]: (k2_xboole_0(k1_tarski(H_142), k1_tarski(I_182))=k2_tarski(H_142, I_182))), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1214])).
% 3.65/1.60  tff(c_445, plain, (![H_130]: (k2_enumset1(H_130, H_130, H_130, H_130)=k1_tarski(H_130))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_361])).
% 3.65/1.60  tff(c_199, plain, (![B_33, C_34, H_100, E_96, G_95, A_32, F_98]: (k6_enumset1(A_32, A_32, B_33, C_34, E_96, F_98, G_95, H_100)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k2_enumset1(E_96, F_98, G_95, H_100)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_183])).
% 3.65/1.60  tff(c_487, plain, (![E_140, B_136, A_139, G_135, H_141, F_137, C_138]: (k2_xboole_0(k1_enumset1(A_139, B_136, C_138), k2_enumset1(E_140, F_137, G_135, H_141))=k5_enumset1(A_139, B_136, C_138, E_140, F_137, G_135, H_141))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_199])).
% 3.65/1.60  tff(c_916, plain, (![A_168, B_169, C_170, H_171]: (k5_enumset1(A_168, B_169, C_170, H_171, H_171, H_171, H_171)=k2_xboole_0(k1_enumset1(A_168, B_169, C_170), k1_tarski(H_171)))), inference(superposition, [status(thm), theory('equality')], [c_445, c_487])).
% 3.65/1.60  tff(c_941, plain, (![B_169, C_170, H_171]: (k4_enumset1(B_169, C_170, H_171, H_171, H_171, H_171)=k2_xboole_0(k1_enumset1(B_169, B_169, C_170), k1_tarski(H_171)))), inference(superposition, [status(thm), theory('equality')], [c_916, c_20])).
% 3.65/1.60  tff(c_1050, plain, (![B_175, C_176, H_177]: (k4_enumset1(B_175, C_176, H_177, H_177, H_177, H_177)=k2_xboole_0(k2_tarski(B_175, C_176), k1_tarski(H_177)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_941])).
% 3.65/1.60  tff(c_1074, plain, (![C_176, H_177]: (k3_enumset1(C_176, H_177, H_177, H_177, H_177)=k2_xboole_0(k2_tarski(C_176, C_176), k1_tarski(H_177)))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_18])).
% 3.65/1.60  tff(c_1103, plain, (![C_176, H_177]: (k3_enumset1(C_176, H_177, H_177, H_177, H_177)=k2_xboole_0(k1_tarski(C_176), k1_tarski(H_177)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1074])).
% 3.65/1.60  tff(c_1804, plain, (![C_176, H_177]: (k3_enumset1(C_176, H_177, H_177, H_177, H_177)=k2_tarski(C_176, H_177))), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_1103])).
% 3.65/1.60  tff(c_24, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.65/1.60  tff(c_26, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.65/1.60  tff(c_27, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.65/1.60  tff(c_1110, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_27])).
% 3.65/1.60  tff(c_1878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1804, c_1110])).
% 3.65/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.60  
% 3.65/1.60  Inference rules
% 3.65/1.60  ----------------------
% 3.65/1.60  #Ref     : 0
% 3.65/1.60  #Sup     : 443
% 3.65/1.60  #Fact    : 0
% 3.65/1.60  #Define  : 0
% 3.65/1.60  #Split   : 0
% 3.65/1.60  #Chain   : 0
% 3.65/1.60  #Close   : 0
% 3.65/1.60  
% 3.65/1.60  Ordering : KBO
% 3.65/1.60  
% 3.65/1.60  Simplification rules
% 3.65/1.60  ----------------------
% 3.65/1.60  #Subsume      : 20
% 3.65/1.60  #Demod        : 527
% 3.65/1.60  #Tautology    : 290
% 3.65/1.60  #SimpNegUnit  : 0
% 3.65/1.60  #BackRed      : 10
% 3.65/1.60  
% 3.65/1.60  #Partial instantiations: 0
% 3.65/1.60  #Strategies tried      : 1
% 3.65/1.60  
% 3.65/1.60  Timing (in seconds)
% 3.65/1.60  ----------------------
% 3.65/1.61  Preprocessing        : 0.30
% 3.65/1.61  Parsing              : 0.16
% 3.65/1.61  CNF conversion       : 0.02
% 3.65/1.61  Main loop            : 0.53
% 3.65/1.61  Inferencing          : 0.21
% 3.65/1.61  Reduction            : 0.21
% 3.65/1.61  Demodulation         : 0.18
% 3.65/1.61  BG Simplification    : 0.03
% 3.65/1.61  Subsumption          : 0.05
% 3.65/1.61  Abstraction          : 0.04
% 3.65/1.61  MUC search           : 0.00
% 3.65/1.61  Cooper               : 0.00
% 3.65/1.61  Total                : 0.86
% 3.65/1.61  Index Insertion      : 0.00
% 3.65/1.61  Index Deletion       : 0.00
% 3.65/1.61  Index Matching       : 0.00
% 3.65/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

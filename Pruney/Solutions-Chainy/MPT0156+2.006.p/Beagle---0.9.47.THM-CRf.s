%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 257 expanded)
%              Number of leaves         :   29 (  99 expanded)
%              Depth                    :   25
%              Number of atoms          :   68 ( 240 expanded)
%              Number of equality atoms :   67 ( 239 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k1_tarski(A_21),k2_enumset1(B_22,C_23,D_24,E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_tarski(A_17),k1_enumset1(B_18,C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_51,B_52,C_53] : k2_enumset1(A_51,A_51,B_52,C_53) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [A_64,B_65,C_66,D_67] : k2_xboole_0(k2_tarski(A_64,B_65),k2_tarski(C_66,D_67)) = k2_enumset1(A_64,B_65,C_66,D_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_48,C_66,D_67] : k2_xboole_0(k1_tarski(A_48),k2_tarski(C_66,D_67)) = k2_enumset1(A_48,A_48,C_66,D_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_87,plain,(
    ! [A_48,C_66,D_67] : k2_xboole_0(k1_tarski(A_48),k2_tarski(C_66,D_67)) = k1_enumset1(A_48,C_66,D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_8,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_68,C_69,D_70] : k2_xboole_0(k1_tarski(A_68),k2_tarski(C_69,D_70)) = k1_enumset1(A_68,C_69,D_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_97,plain,(
    ! [A_68,A_48] : k2_xboole_0(k1_tarski(A_68),k1_tarski(A_48)) = k1_enumset1(A_68,A_48,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_88])).

tff(c_100,plain,(
    ! [A_68,A_48] : k1_enumset1(A_68,A_48,A_48) = k2_tarski(A_68,A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_120,plain,(
    ! [A_73,B_74,C_75,D_76] : k2_xboole_0(k1_tarski(A_73),k1_enumset1(B_74,C_75,D_76)) = k2_enumset1(A_73,B_74,C_75,D_76) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [A_73,A_68,A_48] : k2_xboole_0(k1_tarski(A_73),k2_tarski(A_68,A_48)) = k2_enumset1(A_73,A_68,A_48,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_120])).

tff(c_135,plain,(
    ! [A_73,A_68,A_48] : k2_enumset1(A_73,A_68,A_48,A_48) = k1_enumset1(A_73,A_68,A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_129])).

tff(c_84,plain,(
    ! [A_64,B_65,A_48] : k2_xboole_0(k2_tarski(A_64,B_65),k1_tarski(A_48)) = k2_enumset1(A_64,B_65,A_48,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_185,plain,(
    ! [A_64,B_65,A_48] : k2_xboole_0(k2_tarski(A_64,B_65),k1_tarski(A_48)) = k1_enumset1(A_64,B_65,A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_84])).

tff(c_132,plain,(
    ! [A_73,A_49,B_50] : k2_xboole_0(k1_tarski(A_73),k2_tarski(A_49,B_50)) = k2_enumset1(A_73,A_49,A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_120])).

tff(c_136,plain,(
    ! [A_73,A_49,B_50] : k2_enumset1(A_73,A_49,A_49,B_50) = k1_enumset1(A_73,A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_132])).

tff(c_199,plain,(
    ! [E_90,B_89,D_87,C_88,A_86] : k2_xboole_0(k1_tarski(A_86),k2_enumset1(B_89,C_88,D_87,E_90)) = k3_enumset1(A_86,B_89,C_88,D_87,E_90) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [A_86,A_51,B_52,C_53] : k3_enumset1(A_86,A_51,A_51,B_52,C_53) = k2_xboole_0(k1_tarski(A_86),k1_enumset1(A_51,B_52,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_199])).

tff(c_219,plain,(
    ! [A_86,A_51,B_52,C_53] : k3_enumset1(A_86,A_51,A_51,B_52,C_53) = k2_enumset1(A_86,A_51,B_52,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_214])).

tff(c_307,plain,(
    ! [B_115,H_119,F_116,D_120,G_121,A_118,C_117,E_114] : k2_xboole_0(k1_enumset1(A_118,B_115,C_117),k3_enumset1(D_120,E_114,F_116,G_121,H_119)) = k6_enumset1(A_118,B_115,C_117,D_120,E_114,F_116,G_121,H_119) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_379,plain,(
    ! [H_135,E_132,D_133,G_138,A_137,B_134,F_136] : k6_enumset1(A_137,A_137,B_134,D_133,E_132,F_136,G_138,H_135) = k2_xboole_0(k2_tarski(A_137,B_134),k3_enumset1(D_133,E_132,F_136,G_138,H_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_307])).

tff(c_427,plain,(
    ! [B_148,A_145,A_150,B_146,C_149,A_147] : k6_enumset1(A_150,A_150,B_148,A_147,A_145,A_145,B_146,C_149) = k2_xboole_0(k2_tarski(A_150,B_148),k2_enumset1(A_147,A_145,B_146,C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_379])).

tff(c_536,plain,(
    ! [A_167,A_166,B_164,B_165,A_168] : k6_enumset1(A_167,A_167,B_164,A_168,A_166,A_166,A_166,B_165) = k2_xboole_0(k2_tarski(A_167,B_164),k1_enumset1(A_168,A_166,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_427])).

tff(c_14,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k2_xboole_0(k1_tarski(A_26),k3_enumset1(B_27,C_28,D_29,E_30,F_31)) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_403,plain,(
    ! [H_135,E_132,D_133,A_48,G_138,F_136] : k6_enumset1(A_48,A_48,A_48,D_133,E_132,F_136,G_138,H_135) = k2_xboole_0(k1_tarski(A_48),k3_enumset1(D_133,E_132,F_136,G_138,H_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_379])).

tff(c_408,plain,(
    ! [H_135,E_132,D_133,A_48,G_138,F_136] : k6_enumset1(A_48,A_48,A_48,D_133,E_132,F_136,G_138,H_135) = k4_enumset1(A_48,D_133,E_132,F_136,G_138,H_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_403])).

tff(c_553,plain,(
    ! [B_164,A_168,A_166,B_165] : k4_enumset1(B_164,A_168,A_166,A_166,A_166,B_165) = k2_xboole_0(k2_tarski(B_164,B_164),k1_enumset1(A_168,A_166,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_408])).

tff(c_603,plain,(
    ! [B_169,A_170,A_171,B_172] : k4_enumset1(B_169,A_170,A_171,A_171,A_171,B_172) = k2_enumset1(B_169,A_170,A_171,B_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_553])).

tff(c_208,plain,(
    ! [A_86,A_73,A_68,A_48] : k3_enumset1(A_86,A_73,A_68,A_48,A_48) = k2_xboole_0(k1_tarski(A_86),k1_enumset1(A_73,A_68,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_199])).

tff(c_265,plain,(
    ! [A_105,A_106,A_107,A_108] : k3_enumset1(A_105,A_106,A_107,A_108,A_108) = k2_enumset1(A_105,A_106,A_107,A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_275,plain,(
    ! [A_108,A_105,A_106,A_26,A_107] : k4_enumset1(A_26,A_105,A_106,A_107,A_108,A_108) = k2_xboole_0(k1_tarski(A_26),k2_enumset1(A_105,A_106,A_107,A_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_14])).

tff(c_293,plain,(
    ! [A_108,A_105,A_106,A_26,A_107] : k4_enumset1(A_26,A_105,A_106,A_107,A_108,A_108) = k3_enumset1(A_26,A_105,A_106,A_107,A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_275])).

tff(c_610,plain,(
    ! [B_169,A_170,B_172] : k3_enumset1(B_169,A_170,B_172,B_172,B_172) = k2_enumset1(B_169,A_170,B_172,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_293])).

tff(c_667,plain,(
    ! [B_181,A_182,B_183] : k3_enumset1(B_181,A_182,B_183,B_183,B_183) = k1_enumset1(B_181,A_182,B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_610])).

tff(c_692,plain,(
    ! [B_181,B_183] : k2_enumset1(B_181,B_183,B_183,B_183) = k1_enumset1(B_181,B_183,B_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_219])).

tff(c_717,plain,(
    ! [B_184,B_185] : k2_enumset1(B_184,B_185,B_185,B_185) = k2_tarski(B_184,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_692])).

tff(c_742,plain,(
    ! [B_185] : k1_enumset1(B_185,B_185,B_185) = k2_tarski(B_185,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_24])).

tff(c_763,plain,(
    ! [B_185] : k1_enumset1(B_185,B_185,B_185) = k1_tarski(B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_742])).

tff(c_946,plain,(
    ! [B_200,A_202,B_199,A_198,C_201] : k6_enumset1(A_202,A_202,B_200,A_198,A_198,A_198,B_199,C_201) = k2_xboole_0(k2_tarski(A_202,B_200),k1_enumset1(A_198,B_199,C_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_427])).

tff(c_989,plain,(
    ! [A_202,B_200,B_185] : k6_enumset1(A_202,A_202,B_200,B_185,B_185,B_185,B_185,B_185) = k2_xboole_0(k2_tarski(A_202,B_200),k1_tarski(B_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_946])).

tff(c_1265,plain,(
    ! [A_217,B_218,B_219] : k6_enumset1(A_217,A_217,B_218,B_219,B_219,B_219,B_219,B_219) = k1_enumset1(A_217,B_218,B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_989])).

tff(c_466,plain,(
    ! [A_145,A_48,B_146,C_149,A_147] : k6_enumset1(A_48,A_48,A_48,A_147,A_145,A_145,B_146,C_149) = k2_xboole_0(k1_tarski(A_48),k2_enumset1(A_147,A_145,B_146,C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_427])).

tff(c_475,plain,(
    ! [A_145,A_48,B_146,C_149,A_147] : k6_enumset1(A_48,A_48,A_48,A_147,A_145,A_145,B_146,C_149) = k3_enumset1(A_48,A_147,A_145,B_146,C_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_466])).

tff(c_1284,plain,(
    ! [B_218,B_219] : k3_enumset1(B_218,B_219,B_219,B_219,B_219) = k1_enumset1(B_218,B_218,B_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_475])).

tff(c_1348,plain,(
    ! [B_220,B_221] : k3_enumset1(B_220,B_221,B_221,B_221,B_221) = k2_tarski(B_220,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1284])).

tff(c_18,plain,(
    ! [E_44,H_47,C_42,G_46,F_45,A_40,D_43,B_41] : k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_enumset1(F_45,G_46,H_47)) = k6_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46,H_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1416,plain,(
    ! [B_226,B_225,F_223,G_222,H_224] : k6_enumset1(B_225,B_226,B_226,B_226,B_226,F_223,G_222,H_224) = k2_xboole_0(k2_tarski(B_225,B_226),k1_enumset1(F_223,G_222,H_224)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1348,c_18])).

tff(c_640,plain,(
    ! [D_173,F_178,H_180,A_176,B_174,G_177,C_175,E_179] : k2_xboole_0(k2_enumset1(A_176,B_174,C_175,D_173),k2_enumset1(E_179,F_178,G_177,H_180)) = k6_enumset1(A_176,B_174,C_175,D_173,E_179,F_178,G_177,H_180) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_661,plain,(
    ! [B_52,F_178,H_180,G_177,C_53,A_51,E_179] : k6_enumset1(A_51,A_51,B_52,C_53,E_179,F_178,G_177,H_180) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k2_enumset1(E_179,F_178,G_177,H_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_640])).

tff(c_1430,plain,(
    ! [B_226,F_223,G_222,H_224] : k2_xboole_0(k1_enumset1(B_226,B_226,B_226),k2_enumset1(B_226,F_223,G_222,H_224)) = k2_xboole_0(k2_tarski(B_226,B_226),k1_enumset1(F_223,G_222,H_224)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1416,c_661])).

tff(c_1528,plain,(
    ! [B_226,F_223,G_222,H_224] : k3_enumset1(B_226,B_226,F_223,G_222,H_224) = k2_enumset1(B_226,F_223,G_222,H_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_20,c_22,c_20,c_1430])).

tff(c_26,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:06:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.60  
% 3.58/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.61  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.61  
% 3.58/1.61  %Foreground sorts:
% 3.58/1.61  
% 3.58/1.61  
% 3.58/1.61  %Background operators:
% 3.58/1.61  
% 3.58/1.61  
% 3.58/1.61  %Foreground operators:
% 3.58/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.58/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.58/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.58/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.58/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.58/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.58/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.61  
% 3.92/1.62  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.92/1.62  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.92/1.62  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.92/1.62  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.92/1.62  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.92/1.62  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.92/1.62  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.92/1.62  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 3.92/1.62  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.92/1.62  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 3.92/1.62  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 3.92/1.62  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.92/1.62  tff(c_12, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k1_tarski(A_21), k2_enumset1(B_22, C_23, D_24, E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.92/1.62  tff(c_10, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_tarski(A_17), k1_enumset1(B_18, C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.62  tff(c_20, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.62  tff(c_22, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.62  tff(c_24, plain, (![A_51, B_52, C_53]: (k2_enumset1(A_51, A_51, B_52, C_53)=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.62  tff(c_72, plain, (![A_64, B_65, C_66, D_67]: (k2_xboole_0(k2_tarski(A_64, B_65), k2_tarski(C_66, D_67))=k2_enumset1(A_64, B_65, C_66, D_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.92/1.62  tff(c_81, plain, (![A_48, C_66, D_67]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(C_66, D_67))=k2_enumset1(A_48, A_48, C_66, D_67))), inference(superposition, [status(thm), theory('equality')], [c_20, c_72])).
% 3.92/1.62  tff(c_87, plain, (![A_48, C_66, D_67]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(C_66, D_67))=k1_enumset1(A_48, C_66, D_67))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 3.92/1.62  tff(c_8, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.92/1.62  tff(c_88, plain, (![A_68, C_69, D_70]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(C_69, D_70))=k1_enumset1(A_68, C_69, D_70))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 3.92/1.62  tff(c_97, plain, (![A_68, A_48]: (k2_xboole_0(k1_tarski(A_68), k1_tarski(A_48))=k1_enumset1(A_68, A_48, A_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_88])).
% 3.92/1.62  tff(c_100, plain, (![A_68, A_48]: (k1_enumset1(A_68, A_48, A_48)=k2_tarski(A_68, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_97])).
% 3.92/1.62  tff(c_120, plain, (![A_73, B_74, C_75, D_76]: (k2_xboole_0(k1_tarski(A_73), k1_enumset1(B_74, C_75, D_76))=k2_enumset1(A_73, B_74, C_75, D_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.62  tff(c_129, plain, (![A_73, A_68, A_48]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(A_68, A_48))=k2_enumset1(A_73, A_68, A_48, A_48))), inference(superposition, [status(thm), theory('equality')], [c_100, c_120])).
% 3.92/1.62  tff(c_135, plain, (![A_73, A_68, A_48]: (k2_enumset1(A_73, A_68, A_48, A_48)=k1_enumset1(A_73, A_68, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_129])).
% 3.92/1.62  tff(c_84, plain, (![A_64, B_65, A_48]: (k2_xboole_0(k2_tarski(A_64, B_65), k1_tarski(A_48))=k2_enumset1(A_64, B_65, A_48, A_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_72])).
% 3.92/1.62  tff(c_185, plain, (![A_64, B_65, A_48]: (k2_xboole_0(k2_tarski(A_64, B_65), k1_tarski(A_48))=k1_enumset1(A_64, B_65, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_84])).
% 3.92/1.62  tff(c_132, plain, (![A_73, A_49, B_50]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(A_49, B_50))=k2_enumset1(A_73, A_49, A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_22, c_120])).
% 3.92/1.62  tff(c_136, plain, (![A_73, A_49, B_50]: (k2_enumset1(A_73, A_49, A_49, B_50)=k1_enumset1(A_73, A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_132])).
% 3.92/1.62  tff(c_199, plain, (![E_90, B_89, D_87, C_88, A_86]: (k2_xboole_0(k1_tarski(A_86), k2_enumset1(B_89, C_88, D_87, E_90))=k3_enumset1(A_86, B_89, C_88, D_87, E_90))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.92/1.62  tff(c_214, plain, (![A_86, A_51, B_52, C_53]: (k3_enumset1(A_86, A_51, A_51, B_52, C_53)=k2_xboole_0(k1_tarski(A_86), k1_enumset1(A_51, B_52, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_199])).
% 3.92/1.62  tff(c_219, plain, (![A_86, A_51, B_52, C_53]: (k3_enumset1(A_86, A_51, A_51, B_52, C_53)=k2_enumset1(A_86, A_51, B_52, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_214])).
% 3.92/1.62  tff(c_307, plain, (![B_115, H_119, F_116, D_120, G_121, A_118, C_117, E_114]: (k2_xboole_0(k1_enumset1(A_118, B_115, C_117), k3_enumset1(D_120, E_114, F_116, G_121, H_119))=k6_enumset1(A_118, B_115, C_117, D_120, E_114, F_116, G_121, H_119))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.92/1.62  tff(c_379, plain, (![H_135, E_132, D_133, G_138, A_137, B_134, F_136]: (k6_enumset1(A_137, A_137, B_134, D_133, E_132, F_136, G_138, H_135)=k2_xboole_0(k2_tarski(A_137, B_134), k3_enumset1(D_133, E_132, F_136, G_138, H_135)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_307])).
% 3.92/1.62  tff(c_427, plain, (![B_148, A_145, A_150, B_146, C_149, A_147]: (k6_enumset1(A_150, A_150, B_148, A_147, A_145, A_145, B_146, C_149)=k2_xboole_0(k2_tarski(A_150, B_148), k2_enumset1(A_147, A_145, B_146, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_379])).
% 3.92/1.62  tff(c_536, plain, (![A_167, A_166, B_164, B_165, A_168]: (k6_enumset1(A_167, A_167, B_164, A_168, A_166, A_166, A_166, B_165)=k2_xboole_0(k2_tarski(A_167, B_164), k1_enumset1(A_168, A_166, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_427])).
% 3.92/1.62  tff(c_14, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k2_xboole_0(k1_tarski(A_26), k3_enumset1(B_27, C_28, D_29, E_30, F_31))=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.62  tff(c_403, plain, (![H_135, E_132, D_133, A_48, G_138, F_136]: (k6_enumset1(A_48, A_48, A_48, D_133, E_132, F_136, G_138, H_135)=k2_xboole_0(k1_tarski(A_48), k3_enumset1(D_133, E_132, F_136, G_138, H_135)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_379])).
% 3.92/1.62  tff(c_408, plain, (![H_135, E_132, D_133, A_48, G_138, F_136]: (k6_enumset1(A_48, A_48, A_48, D_133, E_132, F_136, G_138, H_135)=k4_enumset1(A_48, D_133, E_132, F_136, G_138, H_135))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_403])).
% 3.92/1.62  tff(c_553, plain, (![B_164, A_168, A_166, B_165]: (k4_enumset1(B_164, A_168, A_166, A_166, A_166, B_165)=k2_xboole_0(k2_tarski(B_164, B_164), k1_enumset1(A_168, A_166, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_408])).
% 3.92/1.62  tff(c_603, plain, (![B_169, A_170, A_171, B_172]: (k4_enumset1(B_169, A_170, A_171, A_171, A_171, B_172)=k2_enumset1(B_169, A_170, A_171, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_553])).
% 3.92/1.62  tff(c_208, plain, (![A_86, A_73, A_68, A_48]: (k3_enumset1(A_86, A_73, A_68, A_48, A_48)=k2_xboole_0(k1_tarski(A_86), k1_enumset1(A_73, A_68, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_199])).
% 3.92/1.62  tff(c_265, plain, (![A_105, A_106, A_107, A_108]: (k3_enumset1(A_105, A_106, A_107, A_108, A_108)=k2_enumset1(A_105, A_106, A_107, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_208])).
% 3.92/1.62  tff(c_275, plain, (![A_108, A_105, A_106, A_26, A_107]: (k4_enumset1(A_26, A_105, A_106, A_107, A_108, A_108)=k2_xboole_0(k1_tarski(A_26), k2_enumset1(A_105, A_106, A_107, A_108)))), inference(superposition, [status(thm), theory('equality')], [c_265, c_14])).
% 3.92/1.62  tff(c_293, plain, (![A_108, A_105, A_106, A_26, A_107]: (k4_enumset1(A_26, A_105, A_106, A_107, A_108, A_108)=k3_enumset1(A_26, A_105, A_106, A_107, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_275])).
% 3.92/1.62  tff(c_610, plain, (![B_169, A_170, B_172]: (k3_enumset1(B_169, A_170, B_172, B_172, B_172)=k2_enumset1(B_169, A_170, B_172, B_172))), inference(superposition, [status(thm), theory('equality')], [c_603, c_293])).
% 3.92/1.62  tff(c_667, plain, (![B_181, A_182, B_183]: (k3_enumset1(B_181, A_182, B_183, B_183, B_183)=k1_enumset1(B_181, A_182, B_183))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_610])).
% 3.92/1.62  tff(c_692, plain, (![B_181, B_183]: (k2_enumset1(B_181, B_183, B_183, B_183)=k1_enumset1(B_181, B_183, B_183))), inference(superposition, [status(thm), theory('equality')], [c_667, c_219])).
% 3.92/1.62  tff(c_717, plain, (![B_184, B_185]: (k2_enumset1(B_184, B_185, B_185, B_185)=k2_tarski(B_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_692])).
% 3.92/1.62  tff(c_742, plain, (![B_185]: (k1_enumset1(B_185, B_185, B_185)=k2_tarski(B_185, B_185))), inference(superposition, [status(thm), theory('equality')], [c_717, c_24])).
% 3.92/1.62  tff(c_763, plain, (![B_185]: (k1_enumset1(B_185, B_185, B_185)=k1_tarski(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_742])).
% 3.92/1.62  tff(c_946, plain, (![B_200, A_202, B_199, A_198, C_201]: (k6_enumset1(A_202, A_202, B_200, A_198, A_198, A_198, B_199, C_201)=k2_xboole_0(k2_tarski(A_202, B_200), k1_enumset1(A_198, B_199, C_201)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_427])).
% 3.92/1.62  tff(c_989, plain, (![A_202, B_200, B_185]: (k6_enumset1(A_202, A_202, B_200, B_185, B_185, B_185, B_185, B_185)=k2_xboole_0(k2_tarski(A_202, B_200), k1_tarski(B_185)))), inference(superposition, [status(thm), theory('equality')], [c_763, c_946])).
% 3.92/1.62  tff(c_1265, plain, (![A_217, B_218, B_219]: (k6_enumset1(A_217, A_217, B_218, B_219, B_219, B_219, B_219, B_219)=k1_enumset1(A_217, B_218, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_989])).
% 3.92/1.62  tff(c_466, plain, (![A_145, A_48, B_146, C_149, A_147]: (k6_enumset1(A_48, A_48, A_48, A_147, A_145, A_145, B_146, C_149)=k2_xboole_0(k1_tarski(A_48), k2_enumset1(A_147, A_145, B_146, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_427])).
% 3.92/1.62  tff(c_475, plain, (![A_145, A_48, B_146, C_149, A_147]: (k6_enumset1(A_48, A_48, A_48, A_147, A_145, A_145, B_146, C_149)=k3_enumset1(A_48, A_147, A_145, B_146, C_149))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_466])).
% 3.92/1.62  tff(c_1284, plain, (![B_218, B_219]: (k3_enumset1(B_218, B_219, B_219, B_219, B_219)=k1_enumset1(B_218, B_218, B_219))), inference(superposition, [status(thm), theory('equality')], [c_1265, c_475])).
% 3.92/1.62  tff(c_1348, plain, (![B_220, B_221]: (k3_enumset1(B_220, B_221, B_221, B_221, B_221)=k2_tarski(B_220, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1284])).
% 3.92/1.62  tff(c_18, plain, (![E_44, H_47, C_42, G_46, F_45, A_40, D_43, B_41]: (k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_enumset1(F_45, G_46, H_47))=k6_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46, H_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.62  tff(c_1416, plain, (![B_226, B_225, F_223, G_222, H_224]: (k6_enumset1(B_225, B_226, B_226, B_226, B_226, F_223, G_222, H_224)=k2_xboole_0(k2_tarski(B_225, B_226), k1_enumset1(F_223, G_222, H_224)))), inference(superposition, [status(thm), theory('equality')], [c_1348, c_18])).
% 3.92/1.62  tff(c_640, plain, (![D_173, F_178, H_180, A_176, B_174, G_177, C_175, E_179]: (k2_xboole_0(k2_enumset1(A_176, B_174, C_175, D_173), k2_enumset1(E_179, F_178, G_177, H_180))=k6_enumset1(A_176, B_174, C_175, D_173, E_179, F_178, G_177, H_180))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.62  tff(c_661, plain, (![B_52, F_178, H_180, G_177, C_53, A_51, E_179]: (k6_enumset1(A_51, A_51, B_52, C_53, E_179, F_178, G_177, H_180)=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k2_enumset1(E_179, F_178, G_177, H_180)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_640])).
% 3.92/1.62  tff(c_1430, plain, (![B_226, F_223, G_222, H_224]: (k2_xboole_0(k1_enumset1(B_226, B_226, B_226), k2_enumset1(B_226, F_223, G_222, H_224))=k2_xboole_0(k2_tarski(B_226, B_226), k1_enumset1(F_223, G_222, H_224)))), inference(superposition, [status(thm), theory('equality')], [c_1416, c_661])).
% 3.92/1.62  tff(c_1528, plain, (![B_226, F_223, G_222, H_224]: (k3_enumset1(B_226, B_226, F_223, G_222, H_224)=k2_enumset1(B_226, F_223, G_222, H_224))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_20, c_22, c_20, c_1430])).
% 3.92/1.62  tff(c_26, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.62  tff(c_2030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1528, c_26])).
% 3.92/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.62  
% 3.92/1.62  Inference rules
% 3.92/1.62  ----------------------
% 3.92/1.62  #Ref     : 0
% 3.92/1.62  #Sup     : 456
% 3.92/1.62  #Fact    : 0
% 3.92/1.62  #Define  : 0
% 3.92/1.62  #Split   : 0
% 3.92/1.62  #Chain   : 0
% 3.92/1.62  #Close   : 0
% 3.92/1.62  
% 3.92/1.62  Ordering : KBO
% 3.92/1.62  
% 3.92/1.62  Simplification rules
% 3.92/1.62  ----------------------
% 3.92/1.62  #Subsume      : 1
% 3.92/1.62  #Demod        : 553
% 3.92/1.62  #Tautology    : 298
% 3.92/1.62  #SimpNegUnit  : 0
% 3.92/1.62  #BackRed      : 1
% 3.92/1.62  
% 3.92/1.62  #Partial instantiations: 0
% 3.92/1.62  #Strategies tried      : 1
% 3.92/1.62  
% 3.92/1.62  Timing (in seconds)
% 3.92/1.62  ----------------------
% 3.92/1.63  Preprocessing        : 0.31
% 3.92/1.63  Parsing              : 0.16
% 3.92/1.63  CNF conversion       : 0.02
% 3.92/1.63  Main loop            : 0.58
% 3.92/1.63  Inferencing          : 0.24
% 3.92/1.63  Reduction            : 0.24
% 3.92/1.63  Demodulation         : 0.20
% 3.92/1.63  BG Simplification    : 0.03
% 3.92/1.63  Subsumption          : 0.05
% 3.92/1.63  Abstraction          : 0.04
% 3.92/1.63  MUC search           : 0.00
% 3.92/1.63  Cooper               : 0.00
% 3.92/1.63  Total                : 0.92
% 3.92/1.63  Index Insertion      : 0.00
% 3.92/1.63  Index Deletion       : 0.00
% 3.92/1.63  Index Matching       : 0.00
% 3.92/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------

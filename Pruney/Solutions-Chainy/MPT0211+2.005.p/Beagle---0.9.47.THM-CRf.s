%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 359 expanded)
%              Number of leaves         :   27 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :   65 ( 343 expanded)
%              Number of equality atoms :   64 ( 342 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_enumset1(A_46,A_46,B_47,C_48,D_49) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [D_80,E_84,B_81,A_83,C_82] : k2_xboole_0(k1_enumset1(A_83,B_81,C_82),k2_tarski(D_80,E_84)) = k3_enumset1(A_83,B_81,C_82,D_80,E_84) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_41,B_42,D_80,E_84] : k3_enumset1(A_41,A_41,B_42,D_80,E_84) = k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_80,E_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_154,plain,(
    ! [A_90,B_91,D_92,E_93] : k2_xboole_0(k2_tarski(A_90,B_91),k2_tarski(D_92,E_93)) = k2_enumset1(A_90,B_91,D_92,E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_175,plain,(
    ! [A_40,D_92,E_93] : k2_xboole_0(k1_tarski(A_40),k2_tarski(D_92,E_93)) = k2_enumset1(A_40,A_40,D_92,E_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_154])).

tff(c_182,plain,(
    ! [A_94,D_95,E_96] : k2_xboole_0(k1_tarski(A_94),k2_tarski(D_95,E_96)) = k1_enumset1(A_94,D_95,E_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_175])).

tff(c_317,plain,(
    ! [A_113,A_114,B_115] : k2_xboole_0(k1_tarski(A_113),k2_tarski(A_114,B_115)) = k1_enumset1(A_113,B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_182])).

tff(c_181,plain,(
    ! [A_40,D_92,E_93] : k2_xboole_0(k1_tarski(A_40),k2_tarski(D_92,E_93)) = k1_enumset1(A_40,D_92,E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_175])).

tff(c_323,plain,(
    ! [A_113,B_115,A_114] : k1_enumset1(A_113,B_115,A_114) = k1_enumset1(A_113,A_114,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_181])).

tff(c_200,plain,(
    ! [A_97,A_98] : k2_xboole_0(k1_tarski(A_97),k1_tarski(A_98)) = k1_enumset1(A_97,A_98,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_182])).

tff(c_213,plain,(
    ! [A_98] : k2_xboole_0(k1_tarski(A_98),k1_tarski(A_98)) = k2_tarski(A_98,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_230,plain,(
    ! [A_99] : k2_xboole_0(k1_tarski(A_99),k1_tarski(A_99)) = k1_tarski(A_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_213])).

tff(c_197,plain,(
    ! [A_94,A_40] : k2_xboole_0(k1_tarski(A_94),k1_tarski(A_40)) = k1_enumset1(A_94,A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_182])).

tff(c_255,plain,(
    ! [A_106] : k1_enumset1(A_106,A_106,A_106) = k1_tarski(A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_197])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k2_tarski(D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [A_106,D_8,E_9] : k3_enumset1(A_106,A_106,A_106,D_8,E_9) = k2_xboole_0(k1_tarski(A_106),k2_tarski(D_8,E_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_6])).

tff(c_281,plain,(
    ! [A_106,D_8,E_9] : k3_enumset1(A_106,A_106,A_106,D_8,E_9) = k1_enumset1(A_106,D_8,E_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_264])).

tff(c_141,plain,(
    ! [A_87,C_89,D_88,B_85,E_86] : k2_xboole_0(k1_tarski(A_87),k2_enumset1(B_85,C_89,D_88,E_86)) = k3_enumset1(A_87,B_85,C_89,D_88,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_990,plain,(
    ! [A_162,A_163,B_164,C_165] : k3_enumset1(A_162,A_163,A_163,B_164,C_165) = k2_xboole_0(k1_tarski(A_162),k1_enumset1(A_163,B_164,C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_1066,plain,(
    ! [A_162,A_41,B_42] : k3_enumset1(A_162,A_41,A_41,A_41,B_42) = k2_xboole_0(k1_tarski(A_162),k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_990])).

tff(c_1081,plain,(
    ! [A_166,A_167,B_168] : k3_enumset1(A_166,A_167,A_167,A_167,B_168) = k1_enumset1(A_166,A_167,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_1066])).

tff(c_1116,plain,(
    ! [A_167,B_168] : k2_enumset1(A_167,A_167,A_167,B_168) = k1_enumset1(A_167,A_167,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_24])).

tff(c_1148,plain,(
    ! [A_167,B_168] : k2_enumset1(A_167,A_167,A_167,B_168) = k2_tarski(A_167,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1116])).

tff(c_26,plain,(
    ! [A_50,B_51,E_54,C_52,D_53] : k4_enumset1(A_50,A_50,B_51,C_52,D_53,E_54) = k3_enumset1(A_50,B_51,C_52,D_53,E_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_492,plain,(
    ! [C_128,F_127,A_132,E_130,B_131,D_129] : k2_xboole_0(k3_enumset1(A_132,B_131,C_128,D_129,E_130),k1_tarski(F_127)) = k4_enumset1(A_132,B_131,C_128,D_129,E_130,F_127) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_501,plain,(
    ! [A_46,F_127,B_47,C_48,D_49] : k4_enumset1(A_46,A_46,B_47,C_48,D_49,F_127) = k2_xboole_0(k2_enumset1(A_46,B_47,C_48,D_49),k1_tarski(F_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_492])).

tff(c_3161,plain,(
    ! [F_247,D_245,B_244,C_246,A_248] : k2_xboole_0(k2_enumset1(A_248,B_244,C_246,D_245),k1_tarski(F_247)) = k3_enumset1(A_248,B_244,C_246,D_245,F_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_501])).

tff(c_3206,plain,(
    ! [A_167,B_168,F_247] : k3_enumset1(A_167,A_167,A_167,B_168,F_247) = k2_xboole_0(k2_tarski(A_167,B_168),k1_tarski(F_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_3161])).

tff(c_3226,plain,(
    ! [A_167,B_168,F_247] : k2_xboole_0(k2_tarski(A_167,B_168),k1_tarski(F_247)) = k1_enumset1(A_167,B_168,F_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_3206])).

tff(c_4158,plain,(
    ! [A_285,B_286,F_287] : k2_xboole_0(k2_tarski(A_285,B_286),k1_tarski(F_287)) = k1_enumset1(A_285,B_286,F_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_3206])).

tff(c_4256,plain,(
    ! [B_290,A_291,F_292] : k2_xboole_0(k2_tarski(B_290,A_291),k1_tarski(F_292)) = k1_enumset1(A_291,B_290,F_292) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4158])).

tff(c_4268,plain,(
    ! [B_168,A_167,F_247] : k1_enumset1(B_168,A_167,F_247) = k1_enumset1(A_167,B_168,F_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_3226,c_4256])).

tff(c_1726,plain,(
    ! [A_196,B_197,D_198,E_199] : k2_xboole_0(k2_tarski(A_196,B_197),k2_tarski(D_198,E_199)) = k2_enumset1(B_197,A_196,D_198,E_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_154])).

tff(c_140,plain,(
    ! [A_41,B_42,D_80,E_84] : k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(D_80,E_84)) = k2_enumset1(A_41,B_42,D_80,E_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_1735,plain,(
    ! [B_197,A_196,D_198,E_199] : k2_enumset1(B_197,A_196,D_198,E_199) = k2_enumset1(A_196,B_197,D_198,E_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_1726,c_140])).

tff(c_288,plain,(
    ! [E_108,B_107,A_109,D_110,C_112,F_111] : k2_xboole_0(k1_enumset1(A_109,B_107,C_112),k1_enumset1(D_110,E_108,F_111)) = k4_enumset1(A_109,B_107,C_112,D_110,E_108,F_111) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_312,plain,(
    ! [B_107,A_109,A_41,B_42,C_112] : k4_enumset1(A_109,B_107,C_112,A_41,A_41,B_42) = k2_xboole_0(k1_enumset1(A_109,B_107,C_112),k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_288])).

tff(c_1704,plain,(
    ! [A_191,B_194,A_193,B_195,C_192] : k4_enumset1(A_193,B_194,C_192,A_191,A_191,B_195) = k3_enumset1(A_193,B_194,C_192,A_191,B_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_312])).

tff(c_1718,plain,(
    ! [A_50,B_51,D_53,E_54] : k3_enumset1(A_50,B_51,D_53,D_53,E_54) = k3_enumset1(A_50,A_50,B_51,D_53,E_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1704])).

tff(c_2122,plain,(
    ! [A_218,B_219,D_220,E_221] : k3_enumset1(A_218,B_219,D_220,D_220,E_221) = k2_enumset1(A_218,B_219,D_220,E_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1718])).

tff(c_1080,plain,(
    ! [A_162,A_41,B_42] : k3_enumset1(A_162,A_41,A_41,A_41,B_42) = k1_enumset1(A_162,A_41,B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_1066])).

tff(c_2220,plain,(
    ! [A_222,D_223,E_224] : k2_enumset1(A_222,D_223,D_223,E_224) = k1_enumset1(A_222,D_223,E_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_2122,c_1080])).

tff(c_2283,plain,(
    ! [D_198,A_196,E_199] : k2_enumset1(D_198,A_196,D_198,E_199) = k1_enumset1(A_196,D_198,E_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_1735,c_2220])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_30])).

tff(c_153,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_31])).

tff(c_343,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_153])).

tff(c_2833,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2283,c_343])).

tff(c_4553,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4268,c_2833])).

tff(c_4556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_4553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:59:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.30  
% 5.56/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.30  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 5.56/2.30  
% 5.56/2.30  %Foreground sorts:
% 5.56/2.30  
% 5.56/2.30  
% 5.56/2.30  %Background operators:
% 5.56/2.30  
% 5.56/2.30  
% 5.56/2.30  %Foreground operators:
% 5.56/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.56/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.56/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.56/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.56/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.56/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.56/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.56/2.30  tff('#skF_2', type, '#skF_2': $i).
% 5.56/2.30  tff('#skF_3', type, '#skF_3': $i).
% 5.56/2.30  tff('#skF_1', type, '#skF_1': $i).
% 5.56/2.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.56/2.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.30  
% 5.88/2.32  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.88/2.32  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.88/2.32  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.88/2.32  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.88/2.32  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.88/2.32  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 5.88/2.32  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 5.88/2.32  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 5.88/2.32  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 5.88/2.32  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 5.88/2.32  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 5.88/2.32  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.88/2.32  tff(c_22, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.88/2.32  tff(c_18, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.88/2.32  tff(c_24, plain, (![A_46, B_47, C_48, D_49]: (k3_enumset1(A_46, A_46, B_47, C_48, D_49)=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.88/2.32  tff(c_20, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.88/2.32  tff(c_119, plain, (![D_80, E_84, B_81, A_83, C_82]: (k2_xboole_0(k1_enumset1(A_83, B_81, C_82), k2_tarski(D_80, E_84))=k3_enumset1(A_83, B_81, C_82, D_80, E_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.32  tff(c_128, plain, (![A_41, B_42, D_80, E_84]: (k3_enumset1(A_41, A_41, B_42, D_80, E_84)=k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_80, E_84)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 5.88/2.32  tff(c_154, plain, (![A_90, B_91, D_92, E_93]: (k2_xboole_0(k2_tarski(A_90, B_91), k2_tarski(D_92, E_93))=k2_enumset1(A_90, B_91, D_92, E_93))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_128])).
% 5.88/2.32  tff(c_175, plain, (![A_40, D_92, E_93]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(D_92, E_93))=k2_enumset1(A_40, A_40, D_92, E_93))), inference(superposition, [status(thm), theory('equality')], [c_18, c_154])).
% 5.88/2.32  tff(c_182, plain, (![A_94, D_95, E_96]: (k2_xboole_0(k1_tarski(A_94), k2_tarski(D_95, E_96))=k1_enumset1(A_94, D_95, E_96))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_175])).
% 5.88/2.32  tff(c_317, plain, (![A_113, A_114, B_115]: (k2_xboole_0(k1_tarski(A_113), k2_tarski(A_114, B_115))=k1_enumset1(A_113, B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_4, c_182])).
% 5.88/2.32  tff(c_181, plain, (![A_40, D_92, E_93]: (k2_xboole_0(k1_tarski(A_40), k2_tarski(D_92, E_93))=k1_enumset1(A_40, D_92, E_93))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_175])).
% 5.88/2.32  tff(c_323, plain, (![A_113, B_115, A_114]: (k1_enumset1(A_113, B_115, A_114)=k1_enumset1(A_113, A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_317, c_181])).
% 5.88/2.32  tff(c_200, plain, (![A_97, A_98]: (k2_xboole_0(k1_tarski(A_97), k1_tarski(A_98))=k1_enumset1(A_97, A_98, A_98))), inference(superposition, [status(thm), theory('equality')], [c_18, c_182])).
% 5.88/2.32  tff(c_213, plain, (![A_98]: (k2_xboole_0(k1_tarski(A_98), k1_tarski(A_98))=k2_tarski(A_98, A_98))), inference(superposition, [status(thm), theory('equality')], [c_200, c_20])).
% 5.88/2.32  tff(c_230, plain, (![A_99]: (k2_xboole_0(k1_tarski(A_99), k1_tarski(A_99))=k1_tarski(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_213])).
% 5.88/2.32  tff(c_197, plain, (![A_94, A_40]: (k2_xboole_0(k1_tarski(A_94), k1_tarski(A_40))=k1_enumset1(A_94, A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_18, c_182])).
% 5.88/2.32  tff(c_255, plain, (![A_106]: (k1_enumset1(A_106, A_106, A_106)=k1_tarski(A_106))), inference(superposition, [status(thm), theory('equality')], [c_230, c_197])).
% 5.88/2.32  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k2_tarski(D_8, E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.32  tff(c_264, plain, (![A_106, D_8, E_9]: (k3_enumset1(A_106, A_106, A_106, D_8, E_9)=k2_xboole_0(k1_tarski(A_106), k2_tarski(D_8, E_9)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_6])).
% 5.88/2.32  tff(c_281, plain, (![A_106, D_8, E_9]: (k3_enumset1(A_106, A_106, A_106, D_8, E_9)=k1_enumset1(A_106, D_8, E_9))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_264])).
% 5.88/2.32  tff(c_141, plain, (![A_87, C_89, D_88, B_85, E_86]: (k2_xboole_0(k1_tarski(A_87), k2_enumset1(B_85, C_89, D_88, E_86))=k3_enumset1(A_87, B_85, C_89, D_88, E_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.88/2.32  tff(c_990, plain, (![A_162, A_163, B_164, C_165]: (k3_enumset1(A_162, A_163, A_163, B_164, C_165)=k2_xboole_0(k1_tarski(A_162), k1_enumset1(A_163, B_164, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_141])).
% 5.88/2.32  tff(c_1066, plain, (![A_162, A_41, B_42]: (k3_enumset1(A_162, A_41, A_41, A_41, B_42)=k2_xboole_0(k1_tarski(A_162), k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_990])).
% 5.88/2.32  tff(c_1081, plain, (![A_166, A_167, B_168]: (k3_enumset1(A_166, A_167, A_167, A_167, B_168)=k1_enumset1(A_166, A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_1066])).
% 5.88/2.32  tff(c_1116, plain, (![A_167, B_168]: (k2_enumset1(A_167, A_167, A_167, B_168)=k1_enumset1(A_167, A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_24])).
% 5.88/2.32  tff(c_1148, plain, (![A_167, B_168]: (k2_enumset1(A_167, A_167, A_167, B_168)=k2_tarski(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1116])).
% 5.88/2.32  tff(c_26, plain, (![A_50, B_51, E_54, C_52, D_53]: (k4_enumset1(A_50, A_50, B_51, C_52, D_53, E_54)=k3_enumset1(A_50, B_51, C_52, D_53, E_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.88/2.32  tff(c_492, plain, (![C_128, F_127, A_132, E_130, B_131, D_129]: (k2_xboole_0(k3_enumset1(A_132, B_131, C_128, D_129, E_130), k1_tarski(F_127))=k4_enumset1(A_132, B_131, C_128, D_129, E_130, F_127))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.88/2.32  tff(c_501, plain, (![A_46, F_127, B_47, C_48, D_49]: (k4_enumset1(A_46, A_46, B_47, C_48, D_49, F_127)=k2_xboole_0(k2_enumset1(A_46, B_47, C_48, D_49), k1_tarski(F_127)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_492])).
% 5.88/2.32  tff(c_3161, plain, (![F_247, D_245, B_244, C_246, A_248]: (k2_xboole_0(k2_enumset1(A_248, B_244, C_246, D_245), k1_tarski(F_247))=k3_enumset1(A_248, B_244, C_246, D_245, F_247))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_501])).
% 5.88/2.32  tff(c_3206, plain, (![A_167, B_168, F_247]: (k3_enumset1(A_167, A_167, A_167, B_168, F_247)=k2_xboole_0(k2_tarski(A_167, B_168), k1_tarski(F_247)))), inference(superposition, [status(thm), theory('equality')], [c_1148, c_3161])).
% 5.88/2.32  tff(c_3226, plain, (![A_167, B_168, F_247]: (k2_xboole_0(k2_tarski(A_167, B_168), k1_tarski(F_247))=k1_enumset1(A_167, B_168, F_247))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_3206])).
% 5.88/2.32  tff(c_4158, plain, (![A_285, B_286, F_287]: (k2_xboole_0(k2_tarski(A_285, B_286), k1_tarski(F_287))=k1_enumset1(A_285, B_286, F_287))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_3206])).
% 5.88/2.32  tff(c_4256, plain, (![B_290, A_291, F_292]: (k2_xboole_0(k2_tarski(B_290, A_291), k1_tarski(F_292))=k1_enumset1(A_291, B_290, F_292))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4158])).
% 5.88/2.32  tff(c_4268, plain, (![B_168, A_167, F_247]: (k1_enumset1(B_168, A_167, F_247)=k1_enumset1(A_167, B_168, F_247))), inference(superposition, [status(thm), theory('equality')], [c_3226, c_4256])).
% 5.88/2.32  tff(c_1726, plain, (![A_196, B_197, D_198, E_199]: (k2_xboole_0(k2_tarski(A_196, B_197), k2_tarski(D_198, E_199))=k2_enumset1(B_197, A_196, D_198, E_199))), inference(superposition, [status(thm), theory('equality')], [c_4, c_154])).
% 5.88/2.32  tff(c_140, plain, (![A_41, B_42, D_80, E_84]: (k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(D_80, E_84))=k2_enumset1(A_41, B_42, D_80, E_84))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_128])).
% 5.88/2.32  tff(c_1735, plain, (![B_197, A_196, D_198, E_199]: (k2_enumset1(B_197, A_196, D_198, E_199)=k2_enumset1(A_196, B_197, D_198, E_199))), inference(superposition, [status(thm), theory('equality')], [c_1726, c_140])).
% 5.88/2.32  tff(c_288, plain, (![E_108, B_107, A_109, D_110, C_112, F_111]: (k2_xboole_0(k1_enumset1(A_109, B_107, C_112), k1_enumset1(D_110, E_108, F_111))=k4_enumset1(A_109, B_107, C_112, D_110, E_108, F_111))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.88/2.32  tff(c_312, plain, (![B_107, A_109, A_41, B_42, C_112]: (k4_enumset1(A_109, B_107, C_112, A_41, A_41, B_42)=k2_xboole_0(k1_enumset1(A_109, B_107, C_112), k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_288])).
% 5.88/2.32  tff(c_1704, plain, (![A_191, B_194, A_193, B_195, C_192]: (k4_enumset1(A_193, B_194, C_192, A_191, A_191, B_195)=k3_enumset1(A_193, B_194, C_192, A_191, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_312])).
% 5.88/2.32  tff(c_1718, plain, (![A_50, B_51, D_53, E_54]: (k3_enumset1(A_50, B_51, D_53, D_53, E_54)=k3_enumset1(A_50, A_50, B_51, D_53, E_54))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1704])).
% 5.88/2.32  tff(c_2122, plain, (![A_218, B_219, D_220, E_221]: (k3_enumset1(A_218, B_219, D_220, D_220, E_221)=k2_enumset1(A_218, B_219, D_220, E_221))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1718])).
% 5.88/2.32  tff(c_1080, plain, (![A_162, A_41, B_42]: (k3_enumset1(A_162, A_41, A_41, A_41, B_42)=k1_enumset1(A_162, A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_1066])).
% 5.88/2.32  tff(c_2220, plain, (![A_222, D_223, E_224]: (k2_enumset1(A_222, D_223, D_223, E_224)=k1_enumset1(A_222, D_223, E_224))), inference(superposition, [status(thm), theory('equality')], [c_2122, c_1080])).
% 5.88/2.32  tff(c_2283, plain, (![D_198, A_196, E_199]: (k2_enumset1(D_198, A_196, D_198, E_199)=k1_enumset1(A_196, D_198, E_199))), inference(superposition, [status(thm), theory('equality')], [c_1735, c_2220])).
% 5.88/2.32  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.32  tff(c_31, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_30])).
% 5.88/2.32  tff(c_153, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_31])).
% 5.88/2.32  tff(c_343, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_153])).
% 5.88/2.32  tff(c_2833, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2283, c_343])).
% 5.88/2.32  tff(c_4553, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4268, c_2833])).
% 5.88/2.32  tff(c_4556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_4553])).
% 5.88/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.32  
% 5.88/2.32  Inference rules
% 5.88/2.32  ----------------------
% 5.88/2.32  #Ref     : 0
% 5.88/2.32  #Sup     : 1083
% 5.88/2.32  #Fact    : 0
% 5.88/2.32  #Define  : 0
% 5.88/2.32  #Split   : 0
% 5.88/2.32  #Chain   : 0
% 5.88/2.32  #Close   : 0
% 5.88/2.32  
% 5.88/2.32  Ordering : KBO
% 5.88/2.32  
% 5.88/2.32  Simplification rules
% 5.88/2.32  ----------------------
% 5.88/2.32  #Subsume      : 136
% 5.88/2.32  #Demod        : 928
% 5.88/2.32  #Tautology    : 663
% 5.88/2.32  #SimpNegUnit  : 0
% 5.88/2.32  #BackRed      : 14
% 5.88/2.32  
% 5.88/2.32  #Partial instantiations: 0
% 5.88/2.32  #Strategies tried      : 1
% 5.88/2.32  
% 5.88/2.32  Timing (in seconds)
% 5.88/2.32  ----------------------
% 5.88/2.33  Preprocessing        : 0.40
% 5.88/2.33  Parsing              : 0.20
% 5.88/2.33  CNF conversion       : 0.02
% 5.88/2.33  Main loop            : 1.02
% 5.88/2.33  Inferencing          : 0.35
% 5.88/2.33  Reduction            : 0.45
% 5.88/2.33  Demodulation         : 0.38
% 5.88/2.33  BG Simplification    : 0.06
% 5.88/2.33  Subsumption          : 0.11
% 5.88/2.33  Abstraction          : 0.07
% 5.88/2.33  MUC search           : 0.00
% 5.88/2.33  Cooper               : 0.00
% 5.88/2.33  Total                : 1.47
% 5.88/2.33  Index Insertion      : 0.00
% 5.88/2.33  Index Deletion       : 0.00
% 5.88/2.33  Index Matching       : 0.00
% 5.88/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

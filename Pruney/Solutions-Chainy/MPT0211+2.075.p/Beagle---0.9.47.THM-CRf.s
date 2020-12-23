%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 162 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :   54 ( 145 expanded)
%              Number of equality atoms :   53 ( 144 expanded)
%              Maximal formula depth    :   10 (   5 average)
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

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_26,plain,(
    ! [A_50,C_52,B_51] : k1_enumset1(A_50,C_52,B_51) = k1_enumset1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_28,B_29,C_30,D_31] : k3_enumset1(A_28,A_28,B_29,C_30,D_31) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_573,plain,(
    ! [D_95,F_92,C_94,E_96,B_93,A_97] : k2_xboole_0(k3_enumset1(A_97,B_93,C_94,D_95,E_96),k1_tarski(F_92)) = k4_enumset1(A_97,B_93,C_94,D_95,E_96,F_92) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_582,plain,(
    ! [C_30,F_92,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,F_92) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),k1_tarski(F_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_573])).

tff(c_586,plain,(
    ! [C_99,A_98,B_101,F_100,D_102] : k2_xboole_0(k2_enumset1(A_98,B_101,C_99,D_102),k1_tarski(F_100)) = k3_enumset1(A_98,B_101,C_99,D_102,F_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_582])).

tff(c_595,plain,(
    ! [A_25,B_26,C_27,F_100] : k3_enumset1(A_25,A_25,B_26,C_27,F_100) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k1_tarski(F_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_586])).

tff(c_599,plain,(
    ! [A_103,B_104,C_105,F_106] : k2_xboole_0(k1_enumset1(A_103,B_104,C_105),k1_tarski(F_106)) = k2_enumset1(A_103,B_104,C_105,F_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_595])).

tff(c_638,plain,(
    ! [A_23,B_24,F_106] : k2_xboole_0(k2_tarski(A_23,B_24),k1_tarski(F_106)) = k2_enumset1(A_23,A_23,B_24,F_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_599])).

tff(c_641,plain,(
    ! [A_23,B_24,F_106] : k2_xboole_0(k2_tarski(A_23,B_24),k1_tarski(F_106)) = k1_enumset1(A_23,B_24,F_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_638])).

tff(c_48,plain,(
    ! [A_56,C_57,B_58] : k1_enumset1(A_56,C_57,B_58) = k1_enumset1(A_56,B_58,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [B_58,C_57] : k1_enumset1(B_58,C_57,B_58) = k2_tarski(B_58,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_629,plain,(
    ! [B_58,C_57,F_106] : k2_xboole_0(k2_tarski(B_58,C_57),k1_tarski(F_106)) = k2_enumset1(B_58,C_57,B_58,F_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_599])).

tff(c_697,plain,(
    ! [B_58,C_57,F_106] : k2_enumset1(B_58,C_57,B_58,F_106) = k1_enumset1(B_58,C_57,F_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_629])).

tff(c_22,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,F_42) = k4_enumset1(A_37,B_38,C_39,D_40,E_41,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_731,plain,(
    ! [F_129,C_125,D_126,E_130,A_131,G_127,B_128] : k2_xboole_0(k3_enumset1(A_131,B_128,C_125,D_126,E_130),k2_tarski(F_129,G_127)) = k5_enumset1(A_131,B_128,C_125,D_126,E_130,F_129,G_127) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_740,plain,(
    ! [C_30,F_129,D_31,G_127,B_29,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,F_129,G_127) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),k2_tarski(F_129,G_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_731])).

tff(c_1467,plain,(
    ! [C_176,B_177,A_175,D_178,G_174,F_179] : k2_xboole_0(k2_enumset1(A_175,B_177,C_176,D_178),k2_tarski(F_179,G_174)) = k4_enumset1(A_175,B_177,C_176,D_178,F_179,G_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_740])).

tff(c_1506,plain,(
    ! [A_25,C_27,G_174,B_26,F_179] : k4_enumset1(A_25,A_25,B_26,C_27,F_179,G_174) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k2_tarski(F_179,G_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1467])).

tff(c_2604,plain,(
    ! [G_221,A_217,B_220,F_218,C_219] : k2_xboole_0(k1_enumset1(A_217,B_220,C_219),k2_tarski(F_218,G_221)) = k3_enumset1(A_217,B_220,C_219,F_218,G_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1506])).

tff(c_2649,plain,(
    ! [A_23,B_24,F_218,G_221] : k3_enumset1(A_23,A_23,B_24,F_218,G_221) = k2_xboole_0(k2_tarski(A_23,B_24),k2_tarski(F_218,G_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2604])).

tff(c_2657,plain,(
    ! [A_23,B_24,F_218,G_221] : k2_xboole_0(k2_tarski(A_23,B_24),k2_tarski(F_218,G_221)) = k2_enumset1(A_23,B_24,F_218,G_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2649])).

tff(c_133,plain,(
    ! [B_61,C_62,A_63] : k1_enumset1(B_61,C_62,A_63) = k1_enumset1(A_63,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_173,plain,(
    ! [A_63,C_62] : k1_enumset1(A_63,C_62,C_62) = k2_tarski(C_62,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_14])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] : k2_xboole_0(k3_enumset1(A_9,B_10,C_11,D_12,E_13),k1_tarski(F_14)) = k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_743,plain,(
    ! [C_125,D_126,E_130,A_131,A_22,B_128] : k5_enumset1(A_131,B_128,C_125,D_126,E_130,A_22,A_22) = k2_xboole_0(k3_enumset1(A_131,B_128,C_125,D_126,E_130),k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_731])).

tff(c_951,plain,(
    ! [E_152,A_149,D_153,A_148,B_151,C_150] : k5_enumset1(A_148,B_151,C_150,D_153,E_152,A_149,A_149) = k4_enumset1(A_148,B_151,C_150,D_153,E_152,A_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_743])).

tff(c_965,plain,(
    ! [C_39,B_38,A_37,D_40,F_42] : k4_enumset1(A_37,B_38,C_39,D_40,F_42,F_42) = k4_enumset1(A_37,A_37,B_38,C_39,D_40,F_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_951])).

tff(c_1590,plain,(
    ! [B_185,C_188,D_187,A_184,F_186] : k4_enumset1(A_184,B_185,C_188,D_187,F_186,F_186) = k3_enumset1(A_184,B_185,C_188,D_187,F_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_965])).

tff(c_1597,plain,(
    ! [B_185,C_188,D_187,F_186] : k3_enumset1(B_185,C_188,D_187,F_186,F_186) = k3_enumset1(B_185,B_185,C_188,D_187,F_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_20])).

tff(c_1692,plain,(
    ! [B_193,C_194,D_195,F_196] : k3_enumset1(B_193,C_194,D_195,F_196,F_196) = k2_enumset1(B_193,C_194,D_195,F_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1597])).

tff(c_1713,plain,(
    ! [C_194,D_195,F_196] : k2_enumset1(C_194,D_195,F_196,F_196) = k2_enumset1(C_194,C_194,D_195,F_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_1692,c_18])).

tff(c_1739,plain,(
    ! [C_197,D_198,F_199] : k2_enumset1(C_197,D_198,F_199,F_199) = k1_enumset1(C_197,D_198,F_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1713])).

tff(c_1784,plain,(
    ! [D_198,F_199] : k1_enumset1(D_198,F_199,F_199) = k1_enumset1(D_198,D_198,F_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_16])).

tff(c_1836,plain,(
    ! [F_199,D_198] : k2_tarski(F_199,D_198) = k2_tarski(D_198,F_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_14,c_1784])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_1841,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_1836,c_29])).

tff(c_2688,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_1841])).

tff(c_2691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_697,c_2688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.72  
% 4.09/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.72  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 4.09/1.72  
% 4.09/1.72  %Foreground sorts:
% 4.09/1.72  
% 4.09/1.72  
% 4.09/1.72  %Background operators:
% 4.09/1.72  
% 4.09/1.72  
% 4.09/1.72  %Foreground operators:
% 4.09/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.09/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.09/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.09/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.09/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.09/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.09/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.72  
% 4.09/1.75  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 4.09/1.75  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.09/1.75  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.09/1.75  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.09/1.75  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.09/1.75  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 4.09/1.75  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.09/1.75  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 4.09/1.75  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 4.09/1.75  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.09/1.75  tff(f_54, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 4.09/1.75  tff(c_26, plain, (![A_50, C_52, B_51]: (k1_enumset1(A_50, C_52, B_51)=k1_enumset1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.75  tff(c_16, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.09/1.75  tff(c_14, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.75  tff(c_18, plain, (![A_28, B_29, C_30, D_31]: (k3_enumset1(A_28, A_28, B_29, C_30, D_31)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.75  tff(c_20, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.09/1.75  tff(c_573, plain, (![D_95, F_92, C_94, E_96, B_93, A_97]: (k2_xboole_0(k3_enumset1(A_97, B_93, C_94, D_95, E_96), k1_tarski(F_92))=k4_enumset1(A_97, B_93, C_94, D_95, E_96, F_92))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.75  tff(c_582, plain, (![C_30, F_92, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, F_92)=k2_xboole_0(k2_enumset1(A_28, B_29, C_30, D_31), k1_tarski(F_92)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_573])).
% 4.09/1.75  tff(c_586, plain, (![C_99, A_98, B_101, F_100, D_102]: (k2_xboole_0(k2_enumset1(A_98, B_101, C_99, D_102), k1_tarski(F_100))=k3_enumset1(A_98, B_101, C_99, D_102, F_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_582])).
% 4.09/1.75  tff(c_595, plain, (![A_25, B_26, C_27, F_100]: (k3_enumset1(A_25, A_25, B_26, C_27, F_100)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k1_tarski(F_100)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_586])).
% 4.09/1.75  tff(c_599, plain, (![A_103, B_104, C_105, F_106]: (k2_xboole_0(k1_enumset1(A_103, B_104, C_105), k1_tarski(F_106))=k2_enumset1(A_103, B_104, C_105, F_106))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_595])).
% 4.09/1.75  tff(c_638, plain, (![A_23, B_24, F_106]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_tarski(F_106))=k2_enumset1(A_23, A_23, B_24, F_106))), inference(superposition, [status(thm), theory('equality')], [c_14, c_599])).
% 4.09/1.75  tff(c_641, plain, (![A_23, B_24, F_106]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_tarski(F_106))=k1_enumset1(A_23, B_24, F_106))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_638])).
% 4.09/1.75  tff(c_48, plain, (![A_56, C_57, B_58]: (k1_enumset1(A_56, C_57, B_58)=k1_enumset1(A_56, B_58, C_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.75  tff(c_64, plain, (![B_58, C_57]: (k1_enumset1(B_58, C_57, B_58)=k2_tarski(B_58, C_57))), inference(superposition, [status(thm), theory('equality')], [c_48, c_14])).
% 4.09/1.75  tff(c_629, plain, (![B_58, C_57, F_106]: (k2_xboole_0(k2_tarski(B_58, C_57), k1_tarski(F_106))=k2_enumset1(B_58, C_57, B_58, F_106))), inference(superposition, [status(thm), theory('equality')], [c_64, c_599])).
% 4.09/1.75  tff(c_697, plain, (![B_58, C_57, F_106]: (k2_enumset1(B_58, C_57, B_58, F_106)=k1_enumset1(B_58, C_57, F_106))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_629])).
% 4.09/1.75  tff(c_22, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, F_42)=k4_enumset1(A_37, B_38, C_39, D_40, E_41, F_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.75  tff(c_731, plain, (![F_129, C_125, D_126, E_130, A_131, G_127, B_128]: (k2_xboole_0(k3_enumset1(A_131, B_128, C_125, D_126, E_130), k2_tarski(F_129, G_127))=k5_enumset1(A_131, B_128, C_125, D_126, E_130, F_129, G_127))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.75  tff(c_740, plain, (![C_30, F_129, D_31, G_127, B_29, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, F_129, G_127)=k2_xboole_0(k2_enumset1(A_28, B_29, C_30, D_31), k2_tarski(F_129, G_127)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_731])).
% 4.09/1.75  tff(c_1467, plain, (![C_176, B_177, A_175, D_178, G_174, F_179]: (k2_xboole_0(k2_enumset1(A_175, B_177, C_176, D_178), k2_tarski(F_179, G_174))=k4_enumset1(A_175, B_177, C_176, D_178, F_179, G_174))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_740])).
% 4.09/1.75  tff(c_1506, plain, (![A_25, C_27, G_174, B_26, F_179]: (k4_enumset1(A_25, A_25, B_26, C_27, F_179, G_174)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k2_tarski(F_179, G_174)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1467])).
% 4.09/1.75  tff(c_2604, plain, (![G_221, A_217, B_220, F_218, C_219]: (k2_xboole_0(k1_enumset1(A_217, B_220, C_219), k2_tarski(F_218, G_221))=k3_enumset1(A_217, B_220, C_219, F_218, G_221))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1506])).
% 4.09/1.75  tff(c_2649, plain, (![A_23, B_24, F_218, G_221]: (k3_enumset1(A_23, A_23, B_24, F_218, G_221)=k2_xboole_0(k2_tarski(A_23, B_24), k2_tarski(F_218, G_221)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2604])).
% 4.09/1.75  tff(c_2657, plain, (![A_23, B_24, F_218, G_221]: (k2_xboole_0(k2_tarski(A_23, B_24), k2_tarski(F_218, G_221))=k2_enumset1(A_23, B_24, F_218, G_221))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2649])).
% 4.09/1.75  tff(c_133, plain, (![B_61, C_62, A_63]: (k1_enumset1(B_61, C_62, A_63)=k1_enumset1(A_63, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.75  tff(c_173, plain, (![A_63, C_62]: (k1_enumset1(A_63, C_62, C_62)=k2_tarski(C_62, A_63))), inference(superposition, [status(thm), theory('equality')], [c_133, c_14])).
% 4.09/1.75  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (k2_xboole_0(k3_enumset1(A_9, B_10, C_11, D_12, E_13), k1_tarski(F_14))=k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.75  tff(c_12, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.75  tff(c_743, plain, (![C_125, D_126, E_130, A_131, A_22, B_128]: (k5_enumset1(A_131, B_128, C_125, D_126, E_130, A_22, A_22)=k2_xboole_0(k3_enumset1(A_131, B_128, C_125, D_126, E_130), k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_731])).
% 4.09/1.75  tff(c_951, plain, (![E_152, A_149, D_153, A_148, B_151, C_150]: (k5_enumset1(A_148, B_151, C_150, D_153, E_152, A_149, A_149)=k4_enumset1(A_148, B_151, C_150, D_153, E_152, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_743])).
% 4.09/1.75  tff(c_965, plain, (![C_39, B_38, A_37, D_40, F_42]: (k4_enumset1(A_37, B_38, C_39, D_40, F_42, F_42)=k4_enumset1(A_37, A_37, B_38, C_39, D_40, F_42))), inference(superposition, [status(thm), theory('equality')], [c_22, c_951])).
% 4.09/1.75  tff(c_1590, plain, (![B_185, C_188, D_187, A_184, F_186]: (k4_enumset1(A_184, B_185, C_188, D_187, F_186, F_186)=k3_enumset1(A_184, B_185, C_188, D_187, F_186))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_965])).
% 4.09/1.75  tff(c_1597, plain, (![B_185, C_188, D_187, F_186]: (k3_enumset1(B_185, C_188, D_187, F_186, F_186)=k3_enumset1(B_185, B_185, C_188, D_187, F_186))), inference(superposition, [status(thm), theory('equality')], [c_1590, c_20])).
% 4.09/1.75  tff(c_1692, plain, (![B_193, C_194, D_195, F_196]: (k3_enumset1(B_193, C_194, D_195, F_196, F_196)=k2_enumset1(B_193, C_194, D_195, F_196))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1597])).
% 4.09/1.75  tff(c_1713, plain, (![C_194, D_195, F_196]: (k2_enumset1(C_194, D_195, F_196, F_196)=k2_enumset1(C_194, C_194, D_195, F_196))), inference(superposition, [status(thm), theory('equality')], [c_1692, c_18])).
% 4.09/1.75  tff(c_1739, plain, (![C_197, D_198, F_199]: (k2_enumset1(C_197, D_198, F_199, F_199)=k1_enumset1(C_197, D_198, F_199))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1713])).
% 4.09/1.75  tff(c_1784, plain, (![D_198, F_199]: (k1_enumset1(D_198, F_199, F_199)=k1_enumset1(D_198, D_198, F_199))), inference(superposition, [status(thm), theory('equality')], [c_1739, c_16])).
% 4.09/1.75  tff(c_1836, plain, (![F_199, D_198]: (k2_tarski(F_199, D_198)=k2_tarski(D_198, F_199))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_14, c_1784])).
% 4.09/1.75  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.75  tff(c_29, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 4.09/1.75  tff(c_1841, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1836, c_1836, c_29])).
% 4.09/1.75  tff(c_2688, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_1841])).
% 4.09/1.75  tff(c_2691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_697, c_2688])).
% 4.09/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.75  
% 4.09/1.75  Inference rules
% 4.09/1.75  ----------------------
% 4.09/1.75  #Ref     : 0
% 4.09/1.75  #Sup     : 663
% 4.09/1.75  #Fact    : 0
% 4.09/1.75  #Define  : 0
% 4.09/1.75  #Split   : 0
% 4.09/1.75  #Chain   : 0
% 4.09/1.75  #Close   : 0
% 4.09/1.75  
% 4.09/1.75  Ordering : KBO
% 4.09/1.75  
% 4.09/1.75  Simplification rules
% 4.09/1.75  ----------------------
% 4.09/1.75  #Subsume      : 146
% 4.09/1.75  #Demod        : 415
% 4.09/1.75  #Tautology    : 404
% 4.09/1.75  #SimpNegUnit  : 0
% 4.09/1.75  #BackRed      : 2
% 4.09/1.75  
% 4.09/1.75  #Partial instantiations: 0
% 4.09/1.75  #Strategies tried      : 1
% 4.09/1.75  
% 4.09/1.75  Timing (in seconds)
% 4.09/1.75  ----------------------
% 4.09/1.75  Preprocessing        : 0.31
% 4.09/1.75  Parsing              : 0.16
% 4.09/1.75  CNF conversion       : 0.02
% 4.09/1.75  Main loop            : 0.66
% 4.09/1.75  Inferencing          : 0.21
% 4.09/1.75  Reduction            : 0.31
% 4.09/1.75  Demodulation         : 0.27
% 4.09/1.75  BG Simplification    : 0.03
% 4.09/1.75  Subsumption          : 0.08
% 4.09/1.75  Abstraction          : 0.04
% 4.09/1.75  MUC search           : 0.00
% 4.09/1.75  Cooper               : 0.00
% 4.09/1.75  Total                : 1.01
% 4.09/1.75  Index Insertion      : 0.00
% 4.09/1.75  Index Deletion       : 0.00
% 4.09/1.75  Index Matching       : 0.00
% 4.09/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

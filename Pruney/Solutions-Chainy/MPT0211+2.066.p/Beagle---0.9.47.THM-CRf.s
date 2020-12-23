%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 6.36s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 205 expanded)
%              Number of leaves         :   28 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 188 expanded)
%              Number of equality atoms :   50 ( 187 expanded)
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

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_26,plain,(
    ! [A_48,C_50,B_49] : k1_enumset1(A_48,C_50,B_49) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_9,C_10,A_8] : k1_enumset1(B_9,C_10,A_8) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_776,plain,(
    ! [D_115,A_118,C_116,E_113,F_114,B_117] : k2_xboole_0(k3_enumset1(A_118,B_117,C_116,D_115,E_113),k1_tarski(F_114)) = k4_enumset1(A_118,B_117,C_116,D_115,E_113,F_114) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_788,plain,(
    ! [B_27,D_29,A_26,F_114,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,F_114) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(F_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_776])).

tff(c_3848,plain,(
    ! [B_220,D_219,A_221,C_223,F_222] : k2_xboole_0(k2_enumset1(A_221,B_220,C_223,D_219),k1_tarski(F_222)) = k3_enumset1(A_221,B_220,C_223,D_219,F_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_788])).

tff(c_3863,plain,(
    ! [A_23,B_24,C_25,F_222] : k3_enumset1(A_23,A_23,B_24,C_25,F_222) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(F_222)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3848])).

tff(c_3872,plain,(
    ! [A_224,B_225,C_226,F_227] : k2_xboole_0(k1_enumset1(A_224,B_225,C_226),k1_tarski(F_227)) = k2_enumset1(A_224,B_225,C_226,F_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3863])).

tff(c_3911,plain,(
    ! [A_21,B_22,F_227] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(F_227)) = k2_enumset1(A_21,A_21,B_22,F_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3872])).

tff(c_3914,plain,(
    ! [A_21,B_22,F_227] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(F_227)) = k1_enumset1(A_21,B_22,F_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3911])).

tff(c_12,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_564,plain,(
    ! [D_85,E_84,B_88,C_87,A_86] : k2_xboole_0(k1_enumset1(A_86,B_88,C_87),k2_tarski(D_85,E_84)) = k3_enumset1(A_86,B_88,C_87,D_85,E_84) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_603,plain,(
    ! [A_21,B_22,D_85,E_84] : k3_enumset1(A_21,A_21,B_22,D_85,E_84) = k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(D_85,E_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_564])).

tff(c_611,plain,(
    ! [A_89,B_90,D_91,E_92] : k2_xboole_0(k2_tarski(A_89,B_90),k2_tarski(D_91,E_92)) = k2_enumset1(A_89,B_90,D_91,E_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_603])).

tff(c_623,plain,(
    ! [A_89,B_90,A_20] : k2_xboole_0(k2_tarski(A_89,B_90),k1_tarski(A_20)) = k2_enumset1(A_89,B_90,A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_611])).

tff(c_3918,plain,(
    ! [A_89,B_90,A_20] : k2_enumset1(A_89,B_90,A_20,A_20) = k1_enumset1(A_89,B_90,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3914,c_623])).

tff(c_3866,plain,(
    ! [A_23,B_24,C_25,F_222] : k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(F_222)) = k2_enumset1(A_23,B_24,C_25,F_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3863])).

tff(c_8,plain,(
    ! [C_13,B_12,A_11] : k1_enumset1(C_13,B_12,A_11) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_716,plain,(
    ! [A_109,B_110,C_111,A_112] : k3_enumset1(A_109,B_110,C_111,A_112,A_112) = k2_xboole_0(k1_enumset1(A_109,B_110,C_111),k1_tarski(A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_564])).

tff(c_745,plain,(
    ! [A_11,B_12,C_13,A_112] : k3_enumset1(A_11,B_12,C_13,A_112,A_112) = k2_xboole_0(k1_enumset1(C_13,B_12,A_11),k1_tarski(A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_716])).

tff(c_3870,plain,(
    ! [A_11,B_12,C_13,A_112] : k3_enumset1(A_11,B_12,C_13,A_112,A_112) = k2_enumset1(C_13,B_12,A_11,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_745])).

tff(c_606,plain,(
    ! [A_86,B_88,C_87,A_20] : k3_enumset1(A_86,B_88,C_87,A_20,A_20) = k2_xboole_0(k1_enumset1(A_86,B_88,C_87),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_564])).

tff(c_5254,plain,(
    ! [A_275,B_276,C_277,A_278] : k3_enumset1(A_275,B_276,C_277,A_278,A_278) = k2_enumset1(A_275,B_276,C_277,A_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_606])).

tff(c_5689,plain,(
    ! [C_289,B_290,A_291,A_292] : k2_enumset1(C_289,B_290,A_291,A_292) = k2_enumset1(A_291,B_290,C_289,A_292) ),
    inference(superposition,[status(thm),theory(equality)],[c_3870,c_5254])).

tff(c_5777,plain,(
    ! [A_20,B_90,A_89] : k2_enumset1(A_20,B_90,A_89,A_20) = k1_enumset1(A_89,B_90,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_3918,c_5689])).

tff(c_3871,plain,(
    ! [A_86,B_88,C_87,A_20] : k3_enumset1(A_86,B_88,C_87,A_20,A_20) = k2_enumset1(A_86,B_88,C_87,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_606])).

tff(c_757,plain,(
    ! [B_9,C_10,A_8,A_112] : k3_enumset1(B_9,C_10,A_8,A_112,A_112) = k2_xboole_0(k1_enumset1(A_8,B_9,C_10),k1_tarski(A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_716])).

tff(c_5543,plain,(
    ! [B_285,C_286,A_287,A_288] : k3_enumset1(B_285,C_286,A_287,A_288,A_288) = k2_enumset1(A_287,B_285,C_286,A_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_757])).

tff(c_5607,plain,(
    ! [C_87,A_86,B_88,A_20] : k2_enumset1(C_87,A_86,B_88,A_20) = k2_enumset1(A_86,B_88,C_87,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_3871,c_5543])).

tff(c_5318,plain,(
    ! [C_13,B_12,A_11,A_112] : k2_enumset1(C_13,B_12,A_11,A_112) = k2_enumset1(A_11,B_12,C_13,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_3870,c_5254])).

tff(c_609,plain,(
    ! [A_21,B_22,D_85,E_84] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(D_85,E_84)) = k2_enumset1(A_21,B_22,D_85,E_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_603])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_610,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_29])).

tff(c_5688,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5318,c_610])).

tff(c_6261,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5607,c_5688])).

tff(c_6264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_26,c_5777,c_6261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.36/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.37  
% 6.68/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.37  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.68/2.37  
% 6.68/2.37  %Foreground sorts:
% 6.68/2.37  
% 6.68/2.37  
% 6.68/2.37  %Background operators:
% 6.68/2.37  
% 6.68/2.37  
% 6.68/2.37  %Foreground operators:
% 6.68/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.68/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.68/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.68/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.68/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.68/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.68/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.68/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.68/2.37  tff('#skF_2', type, '#skF_2': $i).
% 6.68/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.68/2.37  tff('#skF_1', type, '#skF_1': $i).
% 6.68/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.68/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.68/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.68/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.68/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.68/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.68/2.37  
% 6.78/2.39  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 6.78/2.39  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 6.78/2.39  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.78/2.39  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.78/2.39  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.78/2.39  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.78/2.39  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 6.78/2.39  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.78/2.39  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 6.78/2.39  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 6.78/2.39  tff(f_54, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 6.78/2.39  tff(c_26, plain, (![A_48, C_50, B_49]: (k1_enumset1(A_48, C_50, B_49)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.78/2.39  tff(c_6, plain, (![B_9, C_10, A_8]: (k1_enumset1(B_9, C_10, A_8)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.78/2.39  tff(c_16, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.78/2.39  tff(c_14, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.78/2.39  tff(c_18, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.78/2.39  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.78/2.39  tff(c_776, plain, (![D_115, A_118, C_116, E_113, F_114, B_117]: (k2_xboole_0(k3_enumset1(A_118, B_117, C_116, D_115, E_113), k1_tarski(F_114))=k4_enumset1(A_118, B_117, C_116, D_115, E_113, F_114))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.78/2.39  tff(c_788, plain, (![B_27, D_29, A_26, F_114, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, F_114)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(F_114)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_776])).
% 6.78/2.39  tff(c_3848, plain, (![B_220, D_219, A_221, C_223, F_222]: (k2_xboole_0(k2_enumset1(A_221, B_220, C_223, D_219), k1_tarski(F_222))=k3_enumset1(A_221, B_220, C_223, D_219, F_222))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_788])).
% 6.78/2.39  tff(c_3863, plain, (![A_23, B_24, C_25, F_222]: (k3_enumset1(A_23, A_23, B_24, C_25, F_222)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(F_222)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3848])).
% 6.78/2.39  tff(c_3872, plain, (![A_224, B_225, C_226, F_227]: (k2_xboole_0(k1_enumset1(A_224, B_225, C_226), k1_tarski(F_227))=k2_enumset1(A_224, B_225, C_226, F_227))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3863])).
% 6.78/2.39  tff(c_3911, plain, (![A_21, B_22, F_227]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(F_227))=k2_enumset1(A_21, A_21, B_22, F_227))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3872])).
% 6.78/2.39  tff(c_3914, plain, (![A_21, B_22, F_227]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(F_227))=k1_enumset1(A_21, B_22, F_227))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3911])).
% 6.78/2.39  tff(c_12, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.78/2.39  tff(c_564, plain, (![D_85, E_84, B_88, C_87, A_86]: (k2_xboole_0(k1_enumset1(A_86, B_88, C_87), k2_tarski(D_85, E_84))=k3_enumset1(A_86, B_88, C_87, D_85, E_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.78/2.39  tff(c_603, plain, (![A_21, B_22, D_85, E_84]: (k3_enumset1(A_21, A_21, B_22, D_85, E_84)=k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(D_85, E_84)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_564])).
% 6.78/2.39  tff(c_611, plain, (![A_89, B_90, D_91, E_92]: (k2_xboole_0(k2_tarski(A_89, B_90), k2_tarski(D_91, E_92))=k2_enumset1(A_89, B_90, D_91, E_92))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_603])).
% 6.78/2.39  tff(c_623, plain, (![A_89, B_90, A_20]: (k2_xboole_0(k2_tarski(A_89, B_90), k1_tarski(A_20))=k2_enumset1(A_89, B_90, A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_12, c_611])).
% 6.78/2.39  tff(c_3918, plain, (![A_89, B_90, A_20]: (k2_enumset1(A_89, B_90, A_20, A_20)=k1_enumset1(A_89, B_90, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_3914, c_623])).
% 6.78/2.39  tff(c_3866, plain, (![A_23, B_24, C_25, F_222]: (k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(F_222))=k2_enumset1(A_23, B_24, C_25, F_222))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3863])).
% 6.78/2.39  tff(c_8, plain, (![C_13, B_12, A_11]: (k1_enumset1(C_13, B_12, A_11)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.78/2.39  tff(c_716, plain, (![A_109, B_110, C_111, A_112]: (k3_enumset1(A_109, B_110, C_111, A_112, A_112)=k2_xboole_0(k1_enumset1(A_109, B_110, C_111), k1_tarski(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_564])).
% 6.78/2.39  tff(c_745, plain, (![A_11, B_12, C_13, A_112]: (k3_enumset1(A_11, B_12, C_13, A_112, A_112)=k2_xboole_0(k1_enumset1(C_13, B_12, A_11), k1_tarski(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_716])).
% 6.78/2.39  tff(c_3870, plain, (![A_11, B_12, C_13, A_112]: (k3_enumset1(A_11, B_12, C_13, A_112, A_112)=k2_enumset1(C_13, B_12, A_11, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_745])).
% 6.78/2.39  tff(c_606, plain, (![A_86, B_88, C_87, A_20]: (k3_enumset1(A_86, B_88, C_87, A_20, A_20)=k2_xboole_0(k1_enumset1(A_86, B_88, C_87), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_564])).
% 6.78/2.39  tff(c_5254, plain, (![A_275, B_276, C_277, A_278]: (k3_enumset1(A_275, B_276, C_277, A_278, A_278)=k2_enumset1(A_275, B_276, C_277, A_278))), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_606])).
% 6.78/2.39  tff(c_5689, plain, (![C_289, B_290, A_291, A_292]: (k2_enumset1(C_289, B_290, A_291, A_292)=k2_enumset1(A_291, B_290, C_289, A_292))), inference(superposition, [status(thm), theory('equality')], [c_3870, c_5254])).
% 6.78/2.39  tff(c_5777, plain, (![A_20, B_90, A_89]: (k2_enumset1(A_20, B_90, A_89, A_20)=k1_enumset1(A_89, B_90, A_20))), inference(superposition, [status(thm), theory('equality')], [c_3918, c_5689])).
% 6.78/2.39  tff(c_3871, plain, (![A_86, B_88, C_87, A_20]: (k3_enumset1(A_86, B_88, C_87, A_20, A_20)=k2_enumset1(A_86, B_88, C_87, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_606])).
% 6.78/2.39  tff(c_757, plain, (![B_9, C_10, A_8, A_112]: (k3_enumset1(B_9, C_10, A_8, A_112, A_112)=k2_xboole_0(k1_enumset1(A_8, B_9, C_10), k1_tarski(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_716])).
% 6.78/2.39  tff(c_5543, plain, (![B_285, C_286, A_287, A_288]: (k3_enumset1(B_285, C_286, A_287, A_288, A_288)=k2_enumset1(A_287, B_285, C_286, A_288))), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_757])).
% 6.78/2.39  tff(c_5607, plain, (![C_87, A_86, B_88, A_20]: (k2_enumset1(C_87, A_86, B_88, A_20)=k2_enumset1(A_86, B_88, C_87, A_20))), inference(superposition, [status(thm), theory('equality')], [c_3871, c_5543])).
% 6.78/2.39  tff(c_5318, plain, (![C_13, B_12, A_11, A_112]: (k2_enumset1(C_13, B_12, A_11, A_112)=k2_enumset1(A_11, B_12, C_13, A_112))), inference(superposition, [status(thm), theory('equality')], [c_3870, c_5254])).
% 6.78/2.39  tff(c_609, plain, (![A_21, B_22, D_85, E_84]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(D_85, E_84))=k2_enumset1(A_21, B_22, D_85, E_84))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_603])).
% 6.78/2.39  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.78/2.39  tff(c_29, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 6.78/2.39  tff(c_610, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_609, c_29])).
% 6.78/2.39  tff(c_5688, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5318, c_610])).
% 6.78/2.39  tff(c_6261, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5607, c_5688])).
% 6.78/2.39  tff(c_6264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_26, c_5777, c_6261])).
% 6.78/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.39  
% 6.78/2.39  Inference rules
% 6.78/2.39  ----------------------
% 6.78/2.39  #Ref     : 0
% 6.78/2.39  #Sup     : 1583
% 6.78/2.39  #Fact    : 0
% 6.78/2.39  #Define  : 0
% 6.78/2.39  #Split   : 0
% 6.78/2.39  #Chain   : 0
% 6.78/2.39  #Close   : 0
% 6.78/2.39  
% 6.78/2.39  Ordering : KBO
% 6.78/2.39  
% 6.78/2.39  Simplification rules
% 6.78/2.39  ----------------------
% 6.78/2.39  #Subsume      : 455
% 6.78/2.39  #Demod        : 977
% 6.78/2.39  #Tautology    : 774
% 6.78/2.39  #SimpNegUnit  : 0
% 6.78/2.39  #BackRed      : 12
% 6.78/2.39  
% 6.78/2.39  #Partial instantiations: 0
% 6.78/2.39  #Strategies tried      : 1
% 6.78/2.39  
% 6.78/2.39  Timing (in seconds)
% 6.78/2.39  ----------------------
% 6.78/2.39  Preprocessing        : 0.36
% 6.78/2.39  Parsing              : 0.17
% 6.78/2.39  CNF conversion       : 0.03
% 6.78/2.39  Main loop            : 1.26
% 6.78/2.39  Inferencing          : 0.41
% 6.78/2.39  Reduction            : 0.61
% 6.78/2.39  Demodulation         : 0.55
% 6.78/2.39  BG Simplification    : 0.04
% 6.78/2.39  Subsumption          : 0.14
% 6.78/2.39  Abstraction          : 0.08
% 6.78/2.39  MUC search           : 0.00
% 6.78/2.39  Cooper               : 0.00
% 6.78/2.39  Total                : 1.66
% 6.78/2.39  Index Insertion      : 0.00
% 6.78/2.39  Index Deletion       : 0.00
% 6.78/2.40  Index Matching       : 0.00
% 6.78/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

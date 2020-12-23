%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 12.92s
% Output     : CNFRefutation 12.92s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 204 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :   43 ( 184 expanded)
%              Number of equality atoms :   42 ( 183 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_10,plain,(
    ! [C_11,E_13,B_10,D_12,A_9] : k2_xboole_0(k1_tarski(A_9),k2_enumset1(B_10,C_11,D_12,E_13)) = k3_enumset1(A_9,B_10,C_11,D_12,E_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_51,B_52,C_53,D_54] : k3_enumset1(A_51,A_51,B_52,C_53,D_54) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_48,B_49,C_50] : k2_enumset1(A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_480,plain,(
    ! [B_115,A_112,D_111,E_116,F_114,C_113] : k2_xboole_0(k2_enumset1(A_112,B_115,C_113,D_111),k2_tarski(E_116,F_114)) = k4_enumset1(A_112,B_115,C_113,D_111,E_116,F_114) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2215,plain,(
    ! [A_190,E_193,B_189,F_191,C_192] : k4_enumset1(A_190,A_190,B_189,C_192,E_193,F_191) = k2_xboole_0(k1_enumset1(A_190,B_189,C_192),k2_tarski(E_193,F_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_480])).

tff(c_323,plain,(
    ! [F_102,E_99,D_103,A_101,B_100,C_98] : k2_xboole_0(k1_tarski(A_101),k3_enumset1(B_100,C_98,D_103,E_99,F_102)) = k4_enumset1(A_101,B_100,C_98,D_103,E_99,F_102) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_338,plain,(
    ! [B_52,A_101,C_53,D_54,A_51] : k4_enumset1(A_101,A_51,A_51,B_52,C_53,D_54) = k2_xboole_0(k1_tarski(A_101),k2_enumset1(A_51,B_52,C_53,D_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_323])).

tff(c_341,plain,(
    ! [B_52,A_101,C_53,D_54,A_51] : k4_enumset1(A_101,A_51,A_51,B_52,C_53,D_54) = k3_enumset1(A_101,A_51,B_52,C_53,D_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_338])).

tff(c_2225,plain,(
    ! [B_189,C_192,E_193,F_191] : k2_xboole_0(k1_enumset1(B_189,B_189,C_192),k2_tarski(E_193,F_191)) = k3_enumset1(B_189,B_189,C_192,E_193,F_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_2215,c_341])).

tff(c_2250,plain,(
    ! [B_189,C_192,E_193,F_191] : k2_xboole_0(k2_tarski(B_189,C_192),k2_tarski(E_193,F_191)) = k2_enumset1(B_189,C_192,E_193,F_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_2225])).

tff(c_276,plain,(
    ! [C_92,E_90,D_91,B_93,A_94] : k2_xboole_0(k2_tarski(A_94,B_93),k1_enumset1(C_92,D_91,E_90)) = k3_enumset1(A_94,B_93,C_92,D_91,E_90) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_285,plain,(
    ! [A_94,B_93,A_46,B_47] : k3_enumset1(A_94,B_93,A_46,A_46,B_47) = k2_xboole_0(k2_tarski(A_94,B_93),k2_tarski(A_46,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_276])).

tff(c_3695,plain,(
    ! [A_247,B_248,A_249,B_250] : k3_enumset1(A_247,B_248,A_249,A_249,B_250) = k2_enumset1(A_247,B_248,A_249,B_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_285])).

tff(c_12,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k2_xboole_0(k2_tarski(A_14,B_15),k1_enumset1(C_16,D_17,E_18)) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1489,plain,(
    ! [C_169,D_166,E_170,B_167,A_168] : k2_xboole_0(k2_tarski(A_168,B_167),k1_enumset1(C_169,D_166,E_170)) = k3_enumset1(B_167,A_168,C_169,D_166,E_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_276])).

tff(c_1501,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k3_enumset1(B_15,A_14,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1489])).

tff(c_5456,plain,(
    ! [B_298,A_299,A_300,B_301] : k3_enumset1(B_298,A_299,A_300,A_300,B_301) = k2_enumset1(A_299,B_298,A_300,B_301) ),
    inference(superposition,[status(thm),theory(equality)],[c_3695,c_1501])).

tff(c_2637,plain,(
    ! [A_94,B_93,A_46,B_47] : k3_enumset1(A_94,B_93,A_46,A_46,B_47) = k2_enumset1(A_94,B_93,A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_285])).

tff(c_5638,plain,(
    ! [B_302,A_303,A_304,B_305] : k2_enumset1(B_302,A_303,A_304,B_305) = k2_enumset1(A_303,B_302,A_304,B_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_5456,c_2637])).

tff(c_37245,plain,(
    ! [A_737,A_733,B_735,B_734,A_736] : k2_xboole_0(k1_tarski(A_737),k2_enumset1(A_733,B_734,A_736,B_735)) = k3_enumset1(A_737,B_734,A_733,A_736,B_735) ),
    inference(superposition,[status(thm),theory(equality)],[c_5638,c_10])).

tff(c_37332,plain,(
    ! [C_11,E_13,B_10,D_12,A_9] : k3_enumset1(A_9,C_11,B_10,D_12,E_13) = k3_enumset1(A_9,B_10,C_11,D_12,E_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_37245])).

tff(c_989,plain,(
    ! [A_143,B_144,A_145,B_146] : k3_enumset1(A_143,B_144,A_145,A_145,B_146) = k2_xboole_0(k2_tarski(A_143,B_144),k2_tarski(A_145,B_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_276])).

tff(c_2961,plain,(
    ! [A_224,C_225,D_226] : k2_xboole_0(k2_tarski(A_224,A_224),k2_tarski(C_225,D_226)) = k2_enumset1(A_224,C_225,C_225,D_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_989])).

tff(c_16,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] : k2_xboole_0(k2_enumset1(A_25,B_26,C_27,D_28),k2_tarski(E_29,F_30)) = k4_enumset1(A_25,B_26,C_27,D_28,E_29,F_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3022,plain,(
    ! [C_225,D_226,A_224,F_30,E_29] : k4_enumset1(A_224,C_225,C_225,D_226,E_29,F_30) = k2_xboole_0(k2_xboole_0(k2_tarski(A_224,A_224),k2_tarski(C_225,D_226)),k2_tarski(E_29,F_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2961,c_16])).

tff(c_3092,plain,(
    ! [C_225,D_226,A_224,F_30,E_29] : k2_xboole_0(k1_enumset1(A_224,C_225,D_226),k2_tarski(E_29,F_30)) = k3_enumset1(A_224,C_225,D_226,E_29,F_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2250,c_341,c_3022])).

tff(c_492,plain,(
    ! [B_49,A_48,E_116,C_50,F_114] : k4_enumset1(A_48,A_48,B_49,C_50,E_116,F_114) = k2_xboole_0(k1_enumset1(A_48,B_49,C_50),k2_tarski(E_116,F_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_480])).

tff(c_45862,plain,(
    ! [B_49,A_48,E_116,C_50,F_114] : k4_enumset1(A_48,A_48,B_49,C_50,E_116,F_114) = k3_enumset1(A_48,B_49,C_50,E_116,F_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_492])).

tff(c_28,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39953,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_3','#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37332,c_28])).

tff(c_46721,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_3','#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45862,c_39953])).

tff(c_46724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37332,c_46721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.92/5.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.92/5.32  
% 12.92/5.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.92/5.32  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.92/5.32  
% 12.92/5.32  %Foreground sorts:
% 12.92/5.32  
% 12.92/5.32  
% 12.92/5.32  %Background operators:
% 12.92/5.32  
% 12.92/5.32  
% 12.92/5.32  %Foreground operators:
% 12.92/5.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.92/5.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.92/5.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.92/5.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.92/5.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.92/5.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.92/5.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.92/5.32  tff('#skF_5', type, '#skF_5': $i).
% 12.92/5.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.92/5.32  tff('#skF_2', type, '#skF_2': $i).
% 12.92/5.32  tff('#skF_3', type, '#skF_3': $i).
% 12.92/5.32  tff('#skF_1', type, '#skF_1': $i).
% 12.92/5.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.92/5.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.92/5.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.92/5.32  tff('#skF_4', type, '#skF_4': $i).
% 12.92/5.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.92/5.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.92/5.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.92/5.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.92/5.32  
% 12.92/5.33  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 12.92/5.33  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 12.92/5.33  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 12.92/5.33  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 12.92/5.33  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 12.92/5.33  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 12.92/5.33  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 12.92/5.33  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.92/5.33  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 12.92/5.33  tff(c_10, plain, (![C_11, E_13, B_10, D_12, A_9]: (k2_xboole_0(k1_tarski(A_9), k2_enumset1(B_10, C_11, D_12, E_13))=k3_enumset1(A_9, B_10, C_11, D_12, E_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.92/5.33  tff(c_26, plain, (![A_51, B_52, C_53, D_54]: (k3_enumset1(A_51, A_51, B_52, C_53, D_54)=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.92/5.33  tff(c_22, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.92/5.33  tff(c_24, plain, (![A_48, B_49, C_50]: (k2_enumset1(A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.92/5.33  tff(c_480, plain, (![B_115, A_112, D_111, E_116, F_114, C_113]: (k2_xboole_0(k2_enumset1(A_112, B_115, C_113, D_111), k2_tarski(E_116, F_114))=k4_enumset1(A_112, B_115, C_113, D_111, E_116, F_114))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.92/5.33  tff(c_2215, plain, (![A_190, E_193, B_189, F_191, C_192]: (k4_enumset1(A_190, A_190, B_189, C_192, E_193, F_191)=k2_xboole_0(k1_enumset1(A_190, B_189, C_192), k2_tarski(E_193, F_191)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_480])).
% 12.92/5.33  tff(c_323, plain, (![F_102, E_99, D_103, A_101, B_100, C_98]: (k2_xboole_0(k1_tarski(A_101), k3_enumset1(B_100, C_98, D_103, E_99, F_102))=k4_enumset1(A_101, B_100, C_98, D_103, E_99, F_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.92/5.33  tff(c_338, plain, (![B_52, A_101, C_53, D_54, A_51]: (k4_enumset1(A_101, A_51, A_51, B_52, C_53, D_54)=k2_xboole_0(k1_tarski(A_101), k2_enumset1(A_51, B_52, C_53, D_54)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_323])).
% 12.92/5.33  tff(c_341, plain, (![B_52, A_101, C_53, D_54, A_51]: (k4_enumset1(A_101, A_51, A_51, B_52, C_53, D_54)=k3_enumset1(A_101, A_51, B_52, C_53, D_54))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_338])).
% 12.92/5.33  tff(c_2225, plain, (![B_189, C_192, E_193, F_191]: (k2_xboole_0(k1_enumset1(B_189, B_189, C_192), k2_tarski(E_193, F_191))=k3_enumset1(B_189, B_189, C_192, E_193, F_191))), inference(superposition, [status(thm), theory('equality')], [c_2215, c_341])).
% 12.92/5.33  tff(c_2250, plain, (![B_189, C_192, E_193, F_191]: (k2_xboole_0(k2_tarski(B_189, C_192), k2_tarski(E_193, F_191))=k2_enumset1(B_189, C_192, E_193, F_191))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_2225])).
% 12.92/5.33  tff(c_276, plain, (![C_92, E_90, D_91, B_93, A_94]: (k2_xboole_0(k2_tarski(A_94, B_93), k1_enumset1(C_92, D_91, E_90))=k3_enumset1(A_94, B_93, C_92, D_91, E_90))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.92/5.33  tff(c_285, plain, (![A_94, B_93, A_46, B_47]: (k3_enumset1(A_94, B_93, A_46, A_46, B_47)=k2_xboole_0(k2_tarski(A_94, B_93), k2_tarski(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_276])).
% 12.92/5.33  tff(c_3695, plain, (![A_247, B_248, A_249, B_250]: (k3_enumset1(A_247, B_248, A_249, A_249, B_250)=k2_enumset1(A_247, B_248, A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_285])).
% 12.92/5.33  tff(c_12, plain, (![E_18, C_16, D_17, A_14, B_15]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_enumset1(C_16, D_17, E_18))=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.92/5.33  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.92/5.33  tff(c_1489, plain, (![C_169, D_166, E_170, B_167, A_168]: (k2_xboole_0(k2_tarski(A_168, B_167), k1_enumset1(C_169, D_166, E_170))=k3_enumset1(B_167, A_168, C_169, D_166, E_170))), inference(superposition, [status(thm), theory('equality')], [c_8, c_276])).
% 12.92/5.33  tff(c_1501, plain, (![E_18, C_16, D_17, A_14, B_15]: (k3_enumset1(B_15, A_14, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1489])).
% 12.92/5.33  tff(c_5456, plain, (![B_298, A_299, A_300, B_301]: (k3_enumset1(B_298, A_299, A_300, A_300, B_301)=k2_enumset1(A_299, B_298, A_300, B_301))), inference(superposition, [status(thm), theory('equality')], [c_3695, c_1501])).
% 12.92/5.33  tff(c_2637, plain, (![A_94, B_93, A_46, B_47]: (k3_enumset1(A_94, B_93, A_46, A_46, B_47)=k2_enumset1(A_94, B_93, A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_285])).
% 12.92/5.33  tff(c_5638, plain, (![B_302, A_303, A_304, B_305]: (k2_enumset1(B_302, A_303, A_304, B_305)=k2_enumset1(A_303, B_302, A_304, B_305))), inference(superposition, [status(thm), theory('equality')], [c_5456, c_2637])).
% 12.92/5.33  tff(c_37245, plain, (![A_737, A_733, B_735, B_734, A_736]: (k2_xboole_0(k1_tarski(A_737), k2_enumset1(A_733, B_734, A_736, B_735))=k3_enumset1(A_737, B_734, A_733, A_736, B_735))), inference(superposition, [status(thm), theory('equality')], [c_5638, c_10])).
% 12.92/5.33  tff(c_37332, plain, (![C_11, E_13, B_10, D_12, A_9]: (k3_enumset1(A_9, C_11, B_10, D_12, E_13)=k3_enumset1(A_9, B_10, C_11, D_12, E_13))), inference(superposition, [status(thm), theory('equality')], [c_10, c_37245])).
% 12.92/5.33  tff(c_989, plain, (![A_143, B_144, A_145, B_146]: (k3_enumset1(A_143, B_144, A_145, A_145, B_146)=k2_xboole_0(k2_tarski(A_143, B_144), k2_tarski(A_145, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_276])).
% 12.92/5.33  tff(c_2961, plain, (![A_224, C_225, D_226]: (k2_xboole_0(k2_tarski(A_224, A_224), k2_tarski(C_225, D_226))=k2_enumset1(A_224, C_225, C_225, D_226))), inference(superposition, [status(thm), theory('equality')], [c_26, c_989])).
% 12.92/5.33  tff(c_16, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (k2_xboole_0(k2_enumset1(A_25, B_26, C_27, D_28), k2_tarski(E_29, F_30))=k4_enumset1(A_25, B_26, C_27, D_28, E_29, F_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.92/5.33  tff(c_3022, plain, (![C_225, D_226, A_224, F_30, E_29]: (k4_enumset1(A_224, C_225, C_225, D_226, E_29, F_30)=k2_xboole_0(k2_xboole_0(k2_tarski(A_224, A_224), k2_tarski(C_225, D_226)), k2_tarski(E_29, F_30)))), inference(superposition, [status(thm), theory('equality')], [c_2961, c_16])).
% 12.92/5.33  tff(c_3092, plain, (![C_225, D_226, A_224, F_30, E_29]: (k2_xboole_0(k1_enumset1(A_224, C_225, D_226), k2_tarski(E_29, F_30))=k3_enumset1(A_224, C_225, D_226, E_29, F_30))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2250, c_341, c_3022])).
% 12.92/5.33  tff(c_492, plain, (![B_49, A_48, E_116, C_50, F_114]: (k4_enumset1(A_48, A_48, B_49, C_50, E_116, F_114)=k2_xboole_0(k1_enumset1(A_48, B_49, C_50), k2_tarski(E_116, F_114)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_480])).
% 12.92/5.33  tff(c_45862, plain, (![B_49, A_48, E_116, C_50, F_114]: (k4_enumset1(A_48, A_48, B_49, C_50, E_116, F_114)=k3_enumset1(A_48, B_49, C_50, E_116, F_114))), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_492])).
% 12.92/5.33  tff(c_28, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.92/5.33  tff(c_39953, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_37332, c_28])).
% 12.92/5.33  tff(c_46721, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_45862, c_39953])).
% 12.92/5.33  tff(c_46724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37332, c_46721])).
% 12.92/5.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.92/5.33  
% 12.92/5.33  Inference rules
% 12.92/5.33  ----------------------
% 12.92/5.33  #Ref     : 0
% 12.92/5.33  #Sup     : 10278
% 12.92/5.33  #Fact    : 0
% 12.92/5.33  #Define  : 0
% 12.92/5.33  #Split   : 0
% 12.92/5.33  #Chain   : 0
% 12.92/5.33  #Close   : 0
% 12.92/5.33  
% 12.92/5.33  Ordering : KBO
% 12.92/5.33  
% 12.92/5.33  Simplification rules
% 12.92/5.33  ----------------------
% 12.92/5.33  #Subsume      : 1698
% 12.92/5.33  #Demod        : 11014
% 12.92/5.33  #Tautology    : 7602
% 12.92/5.33  #SimpNegUnit  : 0
% 12.92/5.33  #BackRed      : 12
% 12.92/5.33  
% 12.92/5.33  #Partial instantiations: 0
% 12.92/5.33  #Strategies tried      : 1
% 12.92/5.33  
% 12.92/5.33  Timing (in seconds)
% 12.92/5.33  ----------------------
% 12.92/5.34  Preprocessing        : 0.30
% 12.92/5.34  Parsing              : 0.16
% 12.92/5.34  CNF conversion       : 0.02
% 12.92/5.34  Main loop            : 4.28
% 12.92/5.34  Inferencing          : 1.16
% 12.92/5.34  Reduction            : 2.32
% 12.92/5.34  Demodulation         : 2.09
% 12.92/5.34  BG Simplification    : 0.09
% 12.92/5.34  Subsumption          : 0.56
% 12.92/5.34  Abstraction          : 0.20
% 12.92/5.34  MUC search           : 0.00
% 12.92/5.34  Cooper               : 0.00
% 12.92/5.34  Total                : 4.61
% 12.92/5.34  Index Insertion      : 0.00
% 13.11/5.34  Index Deletion       : 0.00
% 13.11/5.34  Index Matching       : 0.00
% 13.11/5.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

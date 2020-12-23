%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_24,plain,(
    ! [A_53,D_56,H_60,E_57,G_59,C_55,F_58,B_54] : k2_xboole_0(k1_tarski(A_53),k5_enumset1(B_54,C_55,D_56,E_57,F_58,G_59,H_60)) = k6_enumset1(A_53,B_54,C_55,D_56,E_57,F_58,G_59,H_60) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_46,E_50,B_47,C_48,D_49,G_52,F_51] : k2_xboole_0(k1_enumset1(A_46,B_47,C_48),k2_enumset1(D_49,E_50,F_51,G_52)) = k5_enumset1(A_46,B_47,C_48,D_49,E_50,F_51,G_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k2_tarski(A_20,B_21),k2_tarski(C_22,D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [C_85,A_88,D_89,E_87,B_86] : k2_xboole_0(k1_enumset1(A_88,B_86,C_85),k2_tarski(D_89,E_87)) = k3_enumset1(A_88,B_86,C_85,D_89,E_87) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_463,plain,(
    ! [C_181,C_177,D_178,E_180,A_179,B_176] : k2_xboole_0(k1_enumset1(A_179,B_176,C_177),k2_xboole_0(k2_tarski(D_178,E_180),C_181)) = k2_xboole_0(k3_enumset1(A_179,B_176,C_177,D_178,E_180),C_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_493,plain,(
    ! [C_22,D_23,C_177,A_20,B_21,A_179,B_176] : k2_xboole_0(k3_enumset1(A_179,B_176,C_177,A_20,B_21),k2_tarski(C_22,D_23)) = k2_xboole_0(k1_enumset1(A_179,B_176,C_177),k2_enumset1(A_20,B_21,C_22,D_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_463])).

tff(c_498,plain,(
    ! [C_22,D_23,C_177,A_20,B_21,A_179,B_176] : k2_xboole_0(k3_enumset1(A_179,B_176,C_177,A_20,B_21),k2_tarski(C_22,D_23)) = k5_enumset1(A_179,B_176,C_177,A_20,B_21,C_22,D_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_493])).

tff(c_14,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k2_tarski(D_27,E_28)) = k3_enumset1(A_24,B_25,C_26,D_27,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_74,B_75,C_76] : k2_xboole_0(k2_xboole_0(A_74,B_75),C_76) = k2_xboole_0(A_74,k2_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k1_tarski(A_90),k2_xboole_0(k1_tarski(B_91),C_92)) = k2_xboole_0(k2_tarski(A_90,B_91),C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_47])).

tff(c_130,plain,(
    ! [A_90,A_11,B_12] : k2_xboole_0(k2_tarski(A_90,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_90),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_136,plain,(
    ! [A_93,A_94,B_95] : k2_xboole_0(k2_tarski(A_93,A_94),k1_tarski(B_95)) = k1_enumset1(A_93,A_94,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_130])).

tff(c_211,plain,(
    ! [A_114,A_115,B_116,C_117] : k2_xboole_0(k2_tarski(A_114,A_115),k2_xboole_0(k1_tarski(B_116),C_117)) = k2_xboole_0(k1_enumset1(A_114,A_115,B_116),C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_238,plain,(
    ! [A_13,B_14,A_115,C_15,A_114] : k2_xboole_0(k1_enumset1(A_114,A_115,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k2_tarski(A_114,A_115),k1_enumset1(A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_211])).

tff(c_247,plain,(
    ! [C_121,B_118,A_119,A_122,A_120] : k2_xboole_0(k2_tarski(A_120,A_122),k1_enumset1(A_119,B_118,C_121)) = k3_enumset1(A_120,A_122,A_119,B_118,C_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_238])).

tff(c_679,plain,(
    ! [A_230,C_234,B_233,A_232,C_235,A_231] : k2_xboole_0(k2_tarski(A_230,A_232),k2_xboole_0(k1_enumset1(A_231,B_233,C_235),C_234)) = k2_xboole_0(k3_enumset1(A_230,A_232,A_231,B_233,C_235),C_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_715,plain,(
    ! [A_230,A_24,B_25,D_27,C_26,A_232,E_28] : k2_xboole_0(k3_enumset1(A_230,A_232,A_24,B_25,C_26),k2_tarski(D_27,E_28)) = k2_xboole_0(k2_tarski(A_230,A_232),k3_enumset1(A_24,B_25,C_26,D_27,E_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_679])).

tff(c_758,plain,(
    ! [A_246,E_245,D_249,B_244,A_248,C_243,A_247] : k2_xboole_0(k2_tarski(A_248,A_246),k3_enumset1(A_247,B_244,C_243,D_249,E_245)) = k5_enumset1(A_248,A_246,A_247,B_244,C_243,D_249,E_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_715])).

tff(c_62,plain,(
    ! [A_13,B_14,C_15,C_76] : k2_xboole_0(k1_tarski(A_13),k2_xboole_0(k2_tarski(B_14,C_15),C_76)) = k2_xboole_0(k1_enumset1(A_13,B_14,C_15),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_770,plain,(
    ! [A_246,E_245,D_249,A_13,B_244,A_248,C_243,A_247] : k2_xboole_0(k1_enumset1(A_13,A_248,A_246),k3_enumset1(A_247,B_244,C_243,D_249,E_245)) = k2_xboole_0(k1_tarski(A_13),k5_enumset1(A_248,A_246,A_247,B_244,C_243,D_249,E_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_62])).

tff(c_778,plain,(
    ! [A_246,E_245,D_249,A_13,B_244,A_248,C_243,A_247] : k2_xboole_0(k1_enumset1(A_13,A_248,A_246),k3_enumset1(A_247,B_244,C_243,D_249,E_245)) = k6_enumset1(A_13,A_248,A_246,A_247,B_244,C_243,D_249,E_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_770])).

tff(c_28,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.70  
% 3.80/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.70  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.80/1.70  
% 3.80/1.70  %Foreground sorts:
% 3.80/1.70  
% 3.80/1.70  
% 3.80/1.70  %Background operators:
% 3.80/1.70  
% 3.80/1.70  
% 3.80/1.70  %Foreground operators:
% 3.80/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.80/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.80/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.80/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.80/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.70  
% 3.80/1.72  tff(f_49, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.80/1.72  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 3.80/1.72  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 3.80/1.72  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 3.80/1.72  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.80/1.72  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.80/1.72  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.80/1.72  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 3.80/1.72  tff(c_24, plain, (![A_53, D_56, H_60, E_57, G_59, C_55, F_58, B_54]: (k2_xboole_0(k1_tarski(A_53), k5_enumset1(B_54, C_55, D_56, E_57, F_58, G_59, H_60))=k6_enumset1(A_53, B_54, C_55, D_56, E_57, F_58, G_59, H_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.80/1.72  tff(c_22, plain, (![A_46, E_50, B_47, C_48, D_49, G_52, F_51]: (k2_xboole_0(k1_enumset1(A_46, B_47, C_48), k2_enumset1(D_49, E_50, F_51, G_52))=k5_enumset1(A_46, B_47, C_48, D_49, E_50, F_51, G_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.72  tff(c_12, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k2_tarski(A_20, B_21), k2_tarski(C_22, D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.72  tff(c_94, plain, (![C_85, A_88, D_89, E_87, B_86]: (k2_xboole_0(k1_enumset1(A_88, B_86, C_85), k2_tarski(D_89, E_87))=k3_enumset1(A_88, B_86, C_85, D_89, E_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.72  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.72  tff(c_463, plain, (![C_181, C_177, D_178, E_180, A_179, B_176]: (k2_xboole_0(k1_enumset1(A_179, B_176, C_177), k2_xboole_0(k2_tarski(D_178, E_180), C_181))=k2_xboole_0(k3_enumset1(A_179, B_176, C_177, D_178, E_180), C_181))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2])).
% 3.80/1.72  tff(c_493, plain, (![C_22, D_23, C_177, A_20, B_21, A_179, B_176]: (k2_xboole_0(k3_enumset1(A_179, B_176, C_177, A_20, B_21), k2_tarski(C_22, D_23))=k2_xboole_0(k1_enumset1(A_179, B_176, C_177), k2_enumset1(A_20, B_21, C_22, D_23)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_463])).
% 3.80/1.72  tff(c_498, plain, (![C_22, D_23, C_177, A_20, B_21, A_179, B_176]: (k2_xboole_0(k3_enumset1(A_179, B_176, C_177, A_20, B_21), k2_tarski(C_22, D_23))=k5_enumset1(A_179, B_176, C_177, A_20, B_21, C_22, D_23))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_493])).
% 3.80/1.72  tff(c_14, plain, (![A_24, B_25, D_27, C_26, E_28]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k2_tarski(D_27, E_28))=k3_enumset1(A_24, B_25, C_26, D_27, E_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.72  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.80/1.72  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.80/1.72  tff(c_47, plain, (![A_74, B_75, C_76]: (k2_xboole_0(k2_xboole_0(A_74, B_75), C_76)=k2_xboole_0(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.72  tff(c_106, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k1_tarski(A_90), k2_xboole_0(k1_tarski(B_91), C_92))=k2_xboole_0(k2_tarski(A_90, B_91), C_92))), inference(superposition, [status(thm), theory('equality')], [c_6, c_47])).
% 3.80/1.72  tff(c_130, plain, (![A_90, A_11, B_12]: (k2_xboole_0(k2_tarski(A_90, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_90), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_106])).
% 3.80/1.72  tff(c_136, plain, (![A_93, A_94, B_95]: (k2_xboole_0(k2_tarski(A_93, A_94), k1_tarski(B_95))=k1_enumset1(A_93, A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_130])).
% 3.80/1.72  tff(c_211, plain, (![A_114, A_115, B_116, C_117]: (k2_xboole_0(k2_tarski(A_114, A_115), k2_xboole_0(k1_tarski(B_116), C_117))=k2_xboole_0(k1_enumset1(A_114, A_115, B_116), C_117))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 3.80/1.72  tff(c_238, plain, (![A_13, B_14, A_115, C_15, A_114]: (k2_xboole_0(k1_enumset1(A_114, A_115, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k2_tarski(A_114, A_115), k1_enumset1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_211])).
% 3.80/1.72  tff(c_247, plain, (![C_121, B_118, A_119, A_122, A_120]: (k2_xboole_0(k2_tarski(A_120, A_122), k1_enumset1(A_119, B_118, C_121))=k3_enumset1(A_120, A_122, A_119, B_118, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_238])).
% 3.80/1.72  tff(c_679, plain, (![A_230, C_234, B_233, A_232, C_235, A_231]: (k2_xboole_0(k2_tarski(A_230, A_232), k2_xboole_0(k1_enumset1(A_231, B_233, C_235), C_234))=k2_xboole_0(k3_enumset1(A_230, A_232, A_231, B_233, C_235), C_234))), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 3.80/1.72  tff(c_715, plain, (![A_230, A_24, B_25, D_27, C_26, A_232, E_28]: (k2_xboole_0(k3_enumset1(A_230, A_232, A_24, B_25, C_26), k2_tarski(D_27, E_28))=k2_xboole_0(k2_tarski(A_230, A_232), k3_enumset1(A_24, B_25, C_26, D_27, E_28)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_679])).
% 3.80/1.72  tff(c_758, plain, (![A_246, E_245, D_249, B_244, A_248, C_243, A_247]: (k2_xboole_0(k2_tarski(A_248, A_246), k3_enumset1(A_247, B_244, C_243, D_249, E_245))=k5_enumset1(A_248, A_246, A_247, B_244, C_243, D_249, E_245))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_715])).
% 3.80/1.72  tff(c_62, plain, (![A_13, B_14, C_15, C_76]: (k2_xboole_0(k1_tarski(A_13), k2_xboole_0(k2_tarski(B_14, C_15), C_76))=k2_xboole_0(k1_enumset1(A_13, B_14, C_15), C_76))), inference(superposition, [status(thm), theory('equality')], [c_8, c_47])).
% 3.80/1.72  tff(c_770, plain, (![A_246, E_245, D_249, A_13, B_244, A_248, C_243, A_247]: (k2_xboole_0(k1_enumset1(A_13, A_248, A_246), k3_enumset1(A_247, B_244, C_243, D_249, E_245))=k2_xboole_0(k1_tarski(A_13), k5_enumset1(A_248, A_246, A_247, B_244, C_243, D_249, E_245)))), inference(superposition, [status(thm), theory('equality')], [c_758, c_62])).
% 3.80/1.72  tff(c_778, plain, (![A_246, E_245, D_249, A_13, B_244, A_248, C_243, A_247]: (k2_xboole_0(k1_enumset1(A_13, A_248, A_246), k3_enumset1(A_247, B_244, C_243, D_249, E_245))=k6_enumset1(A_13, A_248, A_246, A_247, B_244, C_243, D_249, E_245))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_770])).
% 3.80/1.72  tff(c_28, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.72  tff(c_1136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_778, c_28])).
% 3.80/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.72  
% 3.80/1.72  Inference rules
% 3.80/1.72  ----------------------
% 3.80/1.72  #Ref     : 0
% 3.80/1.72  #Sup     : 296
% 3.80/1.72  #Fact    : 0
% 3.80/1.72  #Define  : 0
% 3.80/1.72  #Split   : 0
% 3.80/1.72  #Chain   : 0
% 3.80/1.72  #Close   : 0
% 3.80/1.72  
% 3.80/1.72  Ordering : KBO
% 3.80/1.72  
% 3.80/1.72  Simplification rules
% 3.80/1.72  ----------------------
% 3.80/1.72  #Subsume      : 0
% 3.80/1.72  #Demod        : 155
% 3.80/1.72  #Tautology    : 148
% 3.80/1.72  #SimpNegUnit  : 0
% 3.80/1.72  #BackRed      : 1
% 3.80/1.72  
% 3.80/1.72  #Partial instantiations: 0
% 3.80/1.72  #Strategies tried      : 1
% 3.80/1.72  
% 3.80/1.72  Timing (in seconds)
% 3.80/1.72  ----------------------
% 3.80/1.72  Preprocessing        : 0.29
% 3.80/1.72  Parsing              : 0.16
% 3.80/1.72  CNF conversion       : 0.02
% 3.80/1.72  Main loop            : 0.61
% 3.80/1.72  Inferencing          : 0.27
% 3.80/1.72  Reduction            : 0.21
% 3.80/1.72  Demodulation         : 0.17
% 3.80/1.72  BG Simplification    : 0.05
% 3.80/1.72  Subsumption          : 0.06
% 3.80/1.72  Abstraction          : 0.05
% 3.80/1.72  MUC search           : 0.00
% 3.80/1.72  Cooper               : 0.00
% 3.80/1.72  Total                : 0.94
% 3.80/1.72  Index Insertion      : 0.00
% 3.80/1.72  Index Deletion       : 0.00
% 3.80/1.72  Index Matching       : 0.00
% 3.80/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

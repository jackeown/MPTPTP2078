%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:11 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  22 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

tff(c_210,plain,(
    ! [D_81,F_85,C_86,E_87,B_82,A_83,H_84,G_88] : k2_xboole_0(k1_tarski(A_83),k5_enumset1(B_82,C_86,D_81,E_87,F_85,G_88,H_84)) = k6_enumset1(A_83,B_82,C_86,D_81,E_87,F_85,G_88,H_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k2_xboole_0(A_36,B_37),C_38) = k2_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_13,B_14,C_38] : k2_xboole_0(k1_tarski(A_13),k2_xboole_0(k1_tarski(B_14),C_38)) = k2_xboole_0(k2_tarski(A_13,B_14),C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_219,plain,(
    ! [D_81,F_85,A_13,C_86,E_87,B_82,A_83,H_84,G_88] : k2_xboole_0(k2_tarski(A_13,A_83),k5_enumset1(B_82,C_86,D_81,E_87,F_85,G_88,H_84)) = k2_xboole_0(k1_tarski(A_13),k6_enumset1(A_83,B_82,C_86,D_81,E_87,F_85,G_88,H_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_39])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k3_enumset1(E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k2_tarski(A_19,B_20),k3_enumset1(C_21,D_22,E_23,F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_xboole_0(k2_tarski(A_39,B_40),k2_tarski(C_41,D_42)) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [D_59,A_56,B_57,C_58,C_60] : k2_xboole_0(k2_tarski(A_56,B_57),k2_xboole_0(k2_tarski(C_58,D_59),C_60)) = k2_xboole_0(k2_enumset1(A_56,B_57,C_58,D_59),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_121,plain,(
    ! [A_19,A_56,B_57,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k2_enumset1(A_56,B_57,A_19,B_20),k3_enumset1(C_21,D_22,E_23,F_24,G_25)) = k2_xboole_0(k2_tarski(A_56,B_57),k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_463,plain,(
    ! [A_19,A_56,B_57,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k1_tarski(A_56),k6_enumset1(B_57,A_19,B_20,C_21,D_22,E_23,F_24,G_25)) = k7_enumset1(A_56,B_57,A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_4,c_121])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k6_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:14:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.87  
% 3.32/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.88  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.32/1.88  
% 3.32/1.88  %Foreground sorts:
% 3.32/1.88  
% 3.32/1.88  
% 3.32/1.88  %Background operators:
% 3.32/1.88  
% 3.32/1.88  
% 3.32/1.88  %Foreground operators:
% 3.32/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.88  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.88  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.88  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.88  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.88  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.88  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.88  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.88  tff('#skF_9', type, '#skF_9': $i).
% 3.32/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.88  tff('#skF_8', type, '#skF_8': $i).
% 3.32/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.88  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.88  
% 3.32/1.89  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.32/1.89  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.32/1.89  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.32/1.89  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 3.32/1.89  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 3.32/1.89  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 3.32/1.89  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 3.32/1.89  tff(c_210, plain, (![D_81, F_85, C_86, E_87, B_82, A_83, H_84, G_88]: (k2_xboole_0(k1_tarski(A_83), k5_enumset1(B_82, C_86, D_81, E_87, F_85, G_88, H_84))=k6_enumset1(A_83, B_82, C_86, D_81, E_87, F_85, G_88, H_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.89  tff(c_6, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.89  tff(c_24, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k2_xboole_0(A_36, B_37), C_38)=k2_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.89  tff(c_39, plain, (![A_13, B_14, C_38]: (k2_xboole_0(k1_tarski(A_13), k2_xboole_0(k1_tarski(B_14), C_38))=k2_xboole_0(k2_tarski(A_13, B_14), C_38))), inference(superposition, [status(thm), theory('equality')], [c_6, c_24])).
% 3.32/1.89  tff(c_219, plain, (![D_81, F_85, A_13, C_86, E_87, B_82, A_83, H_84, G_88]: (k2_xboole_0(k2_tarski(A_13, A_83), k5_enumset1(B_82, C_86, D_81, E_87, F_85, G_88, H_84))=k2_xboole_0(k1_tarski(A_13), k6_enumset1(A_83, B_82, C_86, D_81, E_87, F_85, G_88, H_84)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_39])).
% 3.32/1.89  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k3_enumset1(E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.89  tff(c_10, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k2_tarski(A_19, B_20), k3_enumset1(C_21, D_22, E_23, F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.89  tff(c_44, plain, (![A_39, B_40, C_41, D_42]: (k2_xboole_0(k2_tarski(A_39, B_40), k2_tarski(C_41, D_42))=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.89  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.89  tff(c_103, plain, (![D_59, A_56, B_57, C_58, C_60]: (k2_xboole_0(k2_tarski(A_56, B_57), k2_xboole_0(k2_tarski(C_58, D_59), C_60))=k2_xboole_0(k2_enumset1(A_56, B_57, C_58, D_59), C_60))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2])).
% 3.32/1.89  tff(c_121, plain, (![A_19, A_56, B_57, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k2_enumset1(A_56, B_57, A_19, B_20), k3_enumset1(C_21, D_22, E_23, F_24, G_25))=k2_xboole_0(k2_tarski(A_56, B_57), k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 3.32/1.89  tff(c_463, plain, (![A_19, A_56, B_57, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k1_tarski(A_56), k6_enumset1(B_57, A_19, B_20, C_21, D_22, E_23, F_24, G_25))=k7_enumset1(A_56, B_57, A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_4, c_121])).
% 3.32/1.89  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k6_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.32/1.89  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_14])).
% 3.32/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.89  
% 3.32/1.89  Inference rules
% 3.32/1.89  ----------------------
% 3.32/1.89  #Ref     : 0
% 3.32/1.89  #Sup     : 110
% 3.32/1.89  #Fact    : 0
% 3.32/1.89  #Define  : 0
% 3.32/1.90  #Split   : 0
% 3.32/1.90  #Chain   : 0
% 3.32/1.90  #Close   : 0
% 3.32/1.90  
% 3.32/1.90  Ordering : KBO
% 3.32/1.90  
% 3.32/1.90  Simplification rules
% 3.32/1.90  ----------------------
% 3.32/1.90  #Subsume      : 0
% 3.32/1.90  #Demod        : 143
% 3.32/1.90  #Tautology    : 79
% 3.32/1.90  #SimpNegUnit  : 0
% 3.32/1.90  #BackRed      : 3
% 3.32/1.90  
% 3.32/1.90  #Partial instantiations: 0
% 3.32/1.90  #Strategies tried      : 1
% 3.32/1.90  
% 3.32/1.90  Timing (in seconds)
% 3.32/1.90  ----------------------
% 3.32/1.90  Preprocessing        : 0.45
% 3.32/1.90  Parsing              : 0.24
% 3.32/1.90  CNF conversion       : 0.03
% 3.32/1.90  Main loop            : 0.57
% 3.32/1.90  Inferencing          : 0.25
% 3.32/1.90  Reduction            : 0.21
% 3.32/1.90  Demodulation         : 0.18
% 3.32/1.90  BG Simplification    : 0.03
% 3.32/1.90  Subsumption          : 0.06
% 3.32/1.90  Abstraction          : 0.05
% 3.32/1.90  MUC search           : 0.00
% 3.32/1.90  Cooper               : 0.00
% 3.32/1.90  Total                : 1.06
% 3.32/1.90  Index Insertion      : 0.00
% 3.32/1.90  Index Deletion       : 0.00
% 3.32/1.90  Index Matching       : 0.00
% 3.32/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

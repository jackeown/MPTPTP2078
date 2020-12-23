%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  23 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_18,plain,(
    ! [A_35,F_40,H_42,B_36,C_37,D_38,E_39,G_41] : k2_xboole_0(k1_tarski(A_35),k5_enumset1(B_36,C_37,D_38,E_39,F_40,G_41,H_42)) = k6_enumset1(A_35,B_36,C_37,D_38,E_39,F_40,G_41,H_42) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [C_30,G_34,E_32,D_31,B_29,F_33,A_28] : k2_xboole_0(k3_enumset1(A_28,B_29,C_30,D_31,E_32),k2_tarski(F_33,G_34)) = k5_enumset1(A_28,B_29,C_30,D_31,E_32,F_33,G_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k2_tarski(E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [A_57,C_56,D_59,B_58,E_60] : k2_xboole_0(k1_tarski(A_57),k2_enumset1(B_58,C_56,D_59,E_60)) = k3_enumset1(A_57,B_58,C_56,D_59,E_60) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_542,plain,(
    ! [C_114,B_110,C_111,A_115,D_113,E_112] : k2_xboole_0(k1_tarski(A_115),k2_xboole_0(k2_enumset1(B_110,C_111,D_113,E_112),C_114)) = k2_xboole_0(k3_enumset1(A_115,B_110,C_111,D_113,E_112),C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_2])).

tff(c_572,plain,(
    ! [E_26,F_27,A_115,A_22,B_23,D_25,C_24] : k2_xboole_0(k3_enumset1(A_115,A_22,B_23,C_24,D_25),k2_tarski(E_26,F_27)) = k2_xboole_0(k1_tarski(A_115),k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_542])).

tff(c_762,plain,(
    ! [D_137,A_133,A_138,C_134,E_135,B_139,F_136] : k2_xboole_0(k1_tarski(A_138),k4_enumset1(A_133,B_139,C_134,D_137,E_135,F_136)) = k5_enumset1(A_138,A_133,B_139,C_134,D_137,E_135,F_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_572])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k2_xboole_0(A_50,B_51),C_52) = k2_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_9,B_10,C_52] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_52)) = k2_xboole_0(k2_tarski(A_9,B_10),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_783,plain,(
    ! [D_137,A_133,A_138,C_134,E_135,B_139,F_136,A_9] : k2_xboole_0(k2_tarski(A_9,A_138),k4_enumset1(A_133,B_139,C_134,D_137,E_135,F_136)) = k2_xboole_0(k1_tarski(A_9),k5_enumset1(A_138,A_133,B_139,C_134,D_137,E_135,F_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_82])).

tff(c_793,plain,(
    ! [D_137,A_133,A_138,C_134,E_135,B_139,F_136,A_9] : k2_xboole_0(k2_tarski(A_9,A_138),k4_enumset1(A_133,B_139,C_134,D_137,E_135,F_136)) = k6_enumset1(A_9,A_138,A_133,B_139,C_134,D_137,E_135,F_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_783])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:37:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.88  
% 4.48/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.88  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.48/1.88  
% 4.48/1.88  %Foreground sorts:
% 4.48/1.88  
% 4.48/1.88  
% 4.48/1.88  %Background operators:
% 4.48/1.88  
% 4.48/1.88  
% 4.48/1.88  %Foreground operators:
% 4.48/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.48/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.48/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.48/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.48/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.48/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.48/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.48/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.48/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.48/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.48/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.48/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.88  
% 4.48/1.89  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 4.48/1.89  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 4.48/1.89  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 4.48/1.89  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 4.48/1.89  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.48/1.89  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.48/1.89  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 4.48/1.89  tff(c_18, plain, (![A_35, F_40, H_42, B_36, C_37, D_38, E_39, G_41]: (k2_xboole_0(k1_tarski(A_35), k5_enumset1(B_36, C_37, D_38, E_39, F_40, G_41, H_42))=k6_enumset1(A_35, B_36, C_37, D_38, E_39, F_40, G_41, H_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.48/1.89  tff(c_16, plain, (![C_30, G_34, E_32, D_31, B_29, F_33, A_28]: (k2_xboole_0(k3_enumset1(A_28, B_29, C_30, D_31, E_32), k2_tarski(F_33, G_34))=k5_enumset1(A_28, B_29, C_30, D_31, E_32, F_33, G_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.89  tff(c_14, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k2_tarski(E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.89  tff(c_120, plain, (![A_57, C_56, D_59, B_58, E_60]: (k2_xboole_0(k1_tarski(A_57), k2_enumset1(B_58, C_56, D_59, E_60))=k3_enumset1(A_57, B_58, C_56, D_59, E_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.89  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.48/1.89  tff(c_542, plain, (![C_114, B_110, C_111, A_115, D_113, E_112]: (k2_xboole_0(k1_tarski(A_115), k2_xboole_0(k2_enumset1(B_110, C_111, D_113, E_112), C_114))=k2_xboole_0(k3_enumset1(A_115, B_110, C_111, D_113, E_112), C_114))), inference(superposition, [status(thm), theory('equality')], [c_120, c_2])).
% 4.48/1.89  tff(c_572, plain, (![E_26, F_27, A_115, A_22, B_23, D_25, C_24]: (k2_xboole_0(k3_enumset1(A_115, A_22, B_23, C_24, D_25), k2_tarski(E_26, F_27))=k2_xboole_0(k1_tarski(A_115), k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_542])).
% 4.48/1.89  tff(c_762, plain, (![D_137, A_133, A_138, C_134, E_135, B_139, F_136]: (k2_xboole_0(k1_tarski(A_138), k4_enumset1(A_133, B_139, C_134, D_137, E_135, F_136))=k5_enumset1(A_138, A_133, B_139, C_134, D_137, E_135, F_136))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_572])).
% 4.48/1.89  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.89  tff(c_67, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k2_xboole_0(A_50, B_51), C_52)=k2_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.48/1.89  tff(c_82, plain, (![A_9, B_10, C_52]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_52))=k2_xboole_0(k2_tarski(A_9, B_10), C_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 4.48/1.89  tff(c_783, plain, (![D_137, A_133, A_138, C_134, E_135, B_139, F_136, A_9]: (k2_xboole_0(k2_tarski(A_9, A_138), k4_enumset1(A_133, B_139, C_134, D_137, E_135, F_136))=k2_xboole_0(k1_tarski(A_9), k5_enumset1(A_138, A_133, B_139, C_134, D_137, E_135, F_136)))), inference(superposition, [status(thm), theory('equality')], [c_762, c_82])).
% 4.48/1.89  tff(c_793, plain, (![D_137, A_133, A_138, C_134, E_135, B_139, F_136, A_9]: (k2_xboole_0(k2_tarski(A_9, A_138), k4_enumset1(A_133, B_139, C_134, D_137, E_135, F_136))=k6_enumset1(A_9, A_138, A_133, B_139, C_134, D_137, E_135, F_136))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_783])).
% 4.48/1.89  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.48/1.89  tff(c_1735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_793, c_20])).
% 4.48/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.89  
% 4.48/1.89  Inference rules
% 4.48/1.89  ----------------------
% 4.48/1.89  #Ref     : 0
% 4.48/1.89  #Sup     : 427
% 4.48/1.89  #Fact    : 0
% 4.48/1.89  #Define  : 0
% 4.48/1.89  #Split   : 0
% 4.48/1.89  #Chain   : 0
% 4.48/1.89  #Close   : 0
% 4.48/1.89  
% 4.48/1.89  Ordering : KBO
% 4.48/1.89  
% 4.48/1.89  Simplification rules
% 4.48/1.89  ----------------------
% 4.48/1.89  #Subsume      : 0
% 4.48/1.89  #Demod        : 920
% 4.48/1.89  #Tautology    : 213
% 4.48/1.89  #SimpNegUnit  : 0
% 4.48/1.89  #BackRed      : 1
% 4.48/1.89  
% 4.48/1.89  #Partial instantiations: 0
% 4.48/1.89  #Strategies tried      : 1
% 4.48/1.89  
% 4.48/1.89  Timing (in seconds)
% 4.48/1.89  ----------------------
% 4.48/1.89  Preprocessing        : 0.31
% 4.48/1.89  Parsing              : 0.18
% 4.48/1.89  CNF conversion       : 0.02
% 4.48/1.89  Main loop            : 0.76
% 4.48/1.89  Inferencing          : 0.27
% 4.48/1.89  Reduction            : 0.36
% 4.48/1.89  Demodulation         : 0.31
% 4.48/1.89  BG Simplification    : 0.05
% 4.48/1.89  Subsumption          : 0.06
% 4.48/1.89  Abstraction          : 0.07
% 4.48/1.89  MUC search           : 0.00
% 4.48/1.89  Cooper               : 0.00
% 4.48/1.89  Total                : 1.10
% 4.48/1.89  Index Insertion      : 0.00
% 4.48/1.89  Index Deletion       : 0.00
% 4.48/1.90  Index Matching       : 0.00
% 4.48/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

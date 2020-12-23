%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:55 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_14,plain,(
    ! [C_30,H_35,G_34,E_32,D_31,B_29,F_33,A_28] : k2_xboole_0(k1_tarski(A_28),k5_enumset1(B_29,C_30,D_31,E_32,F_33,G_34,H_35)) = k6_enumset1(A_28,B_29,C_30,D_31,E_32,F_33,G_34,H_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,G_27,F_26,E_25] : k2_xboole_0(k2_tarski(A_21,B_22),k3_enumset1(C_23,D_24,E_25,F_26,G_27)) = k5_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_61,C_56,F_59,B_58,E_60,D_57] : k2_xboole_0(k1_tarski(A_61),k3_enumset1(B_58,C_56,D_57,E_60,F_59)) = k4_enumset1(A_61,B_58,C_56,D_57,E_60,F_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k2_xboole_0(A_38,B_39),C_40) = k2_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_8,B_9,C_40] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k1_tarski(B_9),C_40)) = k2_xboole_0(k2_tarski(A_8,B_9),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_26])).

tff(c_114,plain,(
    ! [A_61,A_8,C_56,F_59,B_58,E_60,D_57] : k2_xboole_0(k2_tarski(A_8,A_61),k3_enumset1(B_58,C_56,D_57,E_60,F_59)) = k2_xboole_0(k1_tarski(A_8),k4_enumset1(A_61,B_58,C_56,D_57,E_60,F_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_41])).

tff(c_443,plain,(
    ! [D_157,B_152,A_154,A_158,F_155,E_156,C_153] : k2_xboole_0(k1_tarski(A_154),k4_enumset1(A_158,B_152,C_153,D_157,E_156,F_155)) = k5_enumset1(A_154,A_158,B_152,C_153,D_157,E_156,F_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_455,plain,(
    ! [A_8,D_157,B_152,A_154,A_158,F_155,E_156,C_153] : k2_xboole_0(k2_tarski(A_8,A_154),k4_enumset1(A_158,B_152,C_153,D_157,E_156,F_155)) = k2_xboole_0(k1_tarski(A_8),k5_enumset1(A_154,A_158,B_152,C_153,D_157,E_156,F_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_41])).

tff(c_463,plain,(
    ! [A_8,D_157,B_152,A_154,A_158,F_155,E_156,C_153] : k2_xboole_0(k2_tarski(A_8,A_154),k4_enumset1(A_158,B_152,C_153,D_157,E_156,F_155)) = k6_enumset1(A_8,A_154,A_158,B_152,C_153,D_157,E_156,F_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_455])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.46  
% 2.98/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.98/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  
% 3.07/1.48  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.07/1.48  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 3.07/1.48  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.07/1.48  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.07/1.48  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.07/1.48  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 3.07/1.48  tff(c_14, plain, (![C_30, H_35, G_34, E_32, D_31, B_29, F_33, A_28]: (k2_xboole_0(k1_tarski(A_28), k5_enumset1(B_29, C_30, D_31, E_32, F_33, G_34, H_35))=k6_enumset1(A_28, B_29, C_30, D_31, E_32, F_33, G_34, H_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.48  tff(c_12, plain, (![A_21, B_22, D_24, C_23, G_27, F_26, E_25]: (k2_xboole_0(k2_tarski(A_21, B_22), k3_enumset1(C_23, D_24, E_25, F_26, G_27))=k5_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.48  tff(c_108, plain, (![A_61, C_56, F_59, B_58, E_60, D_57]: (k2_xboole_0(k1_tarski(A_61), k3_enumset1(B_58, C_56, D_57, E_60, F_59))=k4_enumset1(A_61, B_58, C_56, D_57, E_60, F_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.48  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.48  tff(c_26, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k2_xboole_0(A_38, B_39), C_40)=k2_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.48  tff(c_41, plain, (![A_8, B_9, C_40]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_40))=k2_xboole_0(k2_tarski(A_8, B_9), C_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_26])).
% 3.07/1.48  tff(c_114, plain, (![A_61, A_8, C_56, F_59, B_58, E_60, D_57]: (k2_xboole_0(k2_tarski(A_8, A_61), k3_enumset1(B_58, C_56, D_57, E_60, F_59))=k2_xboole_0(k1_tarski(A_8), k4_enumset1(A_61, B_58, C_56, D_57, E_60, F_59)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_41])).
% 3.07/1.48  tff(c_443, plain, (![D_157, B_152, A_154, A_158, F_155, E_156, C_153]: (k2_xboole_0(k1_tarski(A_154), k4_enumset1(A_158, B_152, C_153, D_157, E_156, F_155))=k5_enumset1(A_154, A_158, B_152, C_153, D_157, E_156, F_155))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_114])).
% 3.07/1.48  tff(c_455, plain, (![A_8, D_157, B_152, A_154, A_158, F_155, E_156, C_153]: (k2_xboole_0(k2_tarski(A_8, A_154), k4_enumset1(A_158, B_152, C_153, D_157, E_156, F_155))=k2_xboole_0(k1_tarski(A_8), k5_enumset1(A_154, A_158, B_152, C_153, D_157, E_156, F_155)))), inference(superposition, [status(thm), theory('equality')], [c_443, c_41])).
% 3.07/1.48  tff(c_463, plain, (![A_8, D_157, B_152, A_154, A_158, F_155, E_156, C_153]: (k2_xboole_0(k2_tarski(A_8, A_154), k4_enumset1(A_158, B_152, C_153, D_157, E_156, F_155))=k6_enumset1(A_8, A_154, A_158, B_152, C_153, D_157, E_156, F_155))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_455])).
% 3.07/1.48  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.48  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_16])).
% 3.07/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  Inference rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Ref     : 0
% 3.07/1.48  #Sup     : 144
% 3.07/1.48  #Fact    : 0
% 3.07/1.48  #Define  : 0
% 3.07/1.48  #Split   : 0
% 3.07/1.48  #Chain   : 0
% 3.07/1.48  #Close   : 0
% 3.07/1.48  
% 3.07/1.48  Ordering : KBO
% 3.07/1.48  
% 3.07/1.48  Simplification rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Subsume      : 0
% 3.07/1.48  #Demod        : 82
% 3.07/1.48  #Tautology    : 75
% 3.07/1.48  #SimpNegUnit  : 0
% 3.07/1.48  #BackRed      : 3
% 3.07/1.48  
% 3.07/1.48  #Partial instantiations: 0
% 3.07/1.48  #Strategies tried      : 1
% 3.07/1.48  
% 3.07/1.48  Timing (in seconds)
% 3.07/1.48  ----------------------
% 3.07/1.48  Preprocessing        : 0.26
% 3.07/1.48  Parsing              : 0.14
% 3.07/1.48  CNF conversion       : 0.02
% 3.07/1.48  Main loop            : 0.41
% 3.07/1.48  Inferencing          : 0.19
% 3.07/1.48  Reduction            : 0.13
% 3.07/1.48  Demodulation         : 0.11
% 3.07/1.48  BG Simplification    : 0.03
% 3.07/1.48  Subsumption          : 0.05
% 3.07/1.48  Abstraction          : 0.03
% 3.07/1.48  MUC search           : 0.00
% 3.07/1.48  Cooper               : 0.00
% 3.07/1.48  Total                : 0.70
% 3.07/1.48  Index Insertion      : 0.00
% 3.07/1.48  Index Deletion       : 0.00
% 3.07/1.48  Index Matching       : 0.00
% 3.07/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

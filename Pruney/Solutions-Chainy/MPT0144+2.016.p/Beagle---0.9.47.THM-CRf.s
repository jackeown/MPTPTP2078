%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:53 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_16,plain,(
    ! [C_30,G_34,E_32,D_31,B_29,F_33,A_28] : k2_xboole_0(k1_tarski(A_28),k4_enumset1(B_29,C_30,D_31,E_32,F_33,G_34)) = k5_enumset1(A_28,B_29,C_30,D_31,E_32,F_33,G_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k2_tarski(E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [D_51,C_48,E_52,B_50,A_49] : k2_xboole_0(k1_tarski(A_49),k2_enumset1(B_50,C_48,D_51,E_52)) = k3_enumset1(A_49,B_50,C_48,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_511,plain,(
    ! [C_99,A_98,B_95,C_97,E_96,D_94] : k2_xboole_0(k1_tarski(A_98),k2_xboole_0(k2_enumset1(B_95,C_97,D_94,E_96),C_99)) = k2_xboole_0(k3_enumset1(A_98,B_95,C_97,D_94,E_96),C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_541,plain,(
    ! [A_98,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k3_enumset1(A_98,A_22,B_23,C_24,D_25),k2_tarski(E_26,F_27)) = k2_xboole_0(k1_tarski(A_98),k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_511])).

tff(c_548,plain,(
    ! [A_98,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k3_enumset1(A_98,A_22,B_23,C_24,D_25),k2_tarski(E_26,F_27)) = k5_enumset1(A_98,A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_541])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.42  
% 2.71/1.42  %Foreground sorts:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Background operators:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Foreground operators:
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.42  
% 2.71/1.43  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.71/1.43  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 2.71/1.43  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.71/1.43  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.71/1.43  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.71/1.43  tff(c_16, plain, (![C_30, G_34, E_32, D_31, B_29, F_33, A_28]: (k2_xboole_0(k1_tarski(A_28), k4_enumset1(B_29, C_30, D_31, E_32, F_33, G_34))=k5_enumset1(A_28, B_29, C_30, D_31, E_32, F_33, G_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.43  tff(c_14, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k2_tarski(E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.71/1.43  tff(c_118, plain, (![D_51, C_48, E_52, B_50, A_49]: (k2_xboole_0(k1_tarski(A_49), k2_enumset1(B_50, C_48, D_51, E_52))=k3_enumset1(A_49, B_50, C_48, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.43  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.43  tff(c_511, plain, (![C_99, A_98, B_95, C_97, E_96, D_94]: (k2_xboole_0(k1_tarski(A_98), k2_xboole_0(k2_enumset1(B_95, C_97, D_94, E_96), C_99))=k2_xboole_0(k3_enumset1(A_98, B_95, C_97, D_94, E_96), C_99))), inference(superposition, [status(thm), theory('equality')], [c_118, c_2])).
% 2.71/1.43  tff(c_541, plain, (![A_98, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k3_enumset1(A_98, A_22, B_23, C_24, D_25), k2_tarski(E_26, F_27))=k2_xboole_0(k1_tarski(A_98), k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_511])).
% 2.71/1.43  tff(c_548, plain, (![A_98, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k3_enumset1(A_98, A_22, B_23, C_24, D_25), k2_tarski(E_26, F_27))=k5_enumset1(A_98, A_22, B_23, C_24, D_25, E_26, F_27))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_541])).
% 2.71/1.43  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.43  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_548, c_18])).
% 2.71/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  Inference rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Ref     : 0
% 2.71/1.43  #Sup     : 179
% 2.71/1.43  #Fact    : 0
% 2.71/1.43  #Define  : 0
% 2.71/1.43  #Split   : 0
% 2.71/1.43  #Chain   : 0
% 2.71/1.43  #Close   : 0
% 2.71/1.43  
% 2.71/1.43  Ordering : KBO
% 2.71/1.43  
% 2.71/1.43  Simplification rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Subsume      : 0
% 2.71/1.43  #Demod        : 247
% 2.71/1.43  #Tautology    : 85
% 2.71/1.43  #SimpNegUnit  : 0
% 2.71/1.43  #BackRed      : 1
% 2.71/1.43  
% 2.71/1.43  #Partial instantiations: 0
% 2.71/1.43  #Strategies tried      : 1
% 2.71/1.43  
% 2.71/1.43  Timing (in seconds)
% 2.71/1.43  ----------------------
% 2.71/1.43  Preprocessing        : 0.26
% 2.71/1.43  Parsing              : 0.15
% 2.71/1.43  CNF conversion       : 0.02
% 2.71/1.43  Main loop            : 0.38
% 2.71/1.43  Inferencing          : 0.15
% 2.71/1.43  Reduction            : 0.15
% 2.71/1.43  Demodulation         : 0.13
% 2.71/1.43  BG Simplification    : 0.03
% 2.71/1.43  Subsumption          : 0.04
% 2.71/1.43  Abstraction          : 0.03
% 2.71/1.43  MUC search           : 0.00
% 2.71/1.43  Cooper               : 0.00
% 2.71/1.43  Total                : 0.67
% 2.71/1.43  Index Insertion      : 0.00
% 2.71/1.43  Index Deletion       : 0.00
% 2.71/1.43  Index Matching       : 0.00
% 2.71/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

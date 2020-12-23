%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:12 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k3_enumset1(E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [D_29,A_26,E_28,C_27,B_30] : k2_xboole_0(k2_enumset1(A_26,B_30,C_27,D_29),k1_tarski(E_28)) = k3_enumset1(A_26,B_30,C_27,D_29,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [D_36,B_39,A_37,C_41,C_40,E_38] : k2_xboole_0(k2_enumset1(A_37,B_39,C_40,D_36),k2_xboole_0(k1_tarski(E_38),C_41)) = k2_xboole_0(k3_enumset1(A_37,B_39,C_40,D_36,E_38),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_64,plain,(
    ! [D_36,B_39,E_17,A_13,A_37,B_14,C_15,C_40,D_16] : k2_xboole_0(k3_enumset1(A_37,B_39,C_40,D_36,A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k2_xboole_0(k2_enumset1(A_37,B_39,C_40,D_36),k3_enumset1(A_13,B_14,C_15,D_16,E_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_137,plain,(
    ! [D_36,B_39,E_17,A_13,A_37,B_14,C_15,C_40,D_16] : k2_xboole_0(k3_enumset1(A_37,B_39,C_40,D_36,A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k7_enumset1(A_37,B_39,C_40,D_36,A_13,B_14,C_15,D_16,E_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_10,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_enumset1('#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.22  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.88/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.22  tff('#skF_9', type, '#skF_9': $i).
% 1.88/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.22  
% 2.00/1.23  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 2.00/1.23  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.00/1.23  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.00/1.23  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.00/1.23  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 2.00/1.23  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k3_enumset1(E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.23  tff(c_6, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.23  tff(c_28, plain, (![D_29, A_26, E_28, C_27, B_30]: (k2_xboole_0(k2_enumset1(A_26, B_30, C_27, D_29), k1_tarski(E_28))=k3_enumset1(A_26, B_30, C_27, D_29, E_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.23  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.23  tff(c_52, plain, (![D_36, B_39, A_37, C_41, C_40, E_38]: (k2_xboole_0(k2_enumset1(A_37, B_39, C_40, D_36), k2_xboole_0(k1_tarski(E_38), C_41))=k2_xboole_0(k3_enumset1(A_37, B_39, C_40, D_36, E_38), C_41))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 2.00/1.23  tff(c_64, plain, (![D_36, B_39, E_17, A_13, A_37, B_14, C_15, C_40, D_16]: (k2_xboole_0(k3_enumset1(A_37, B_39, C_40, D_36, A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k2_xboole_0(k2_enumset1(A_37, B_39, C_40, D_36), k3_enumset1(A_13, B_14, C_15, D_16, E_17)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 2.00/1.23  tff(c_137, plain, (![D_36, B_39, E_17, A_13, A_37, B_14, C_15, C_40, D_16]: (k2_xboole_0(k3_enumset1(A_37, B_39, C_40, D_36, A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k7_enumset1(A_37, B_39, C_40, D_36, A_13, B_14, C_15, D_16, E_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.00/1.23  tff(c_10, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_enumset1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.23  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_10])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 32
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 0
% 2.00/1.23  #Demod        : 19
% 2.00/1.23  #Tautology    : 21
% 2.00/1.23  #SimpNegUnit  : 0
% 2.00/1.23  #BackRed      : 1
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.25
% 2.00/1.23  Parsing              : 0.13
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.16
% 2.00/1.23  Inferencing          : 0.08
% 2.00/1.23  Reduction            : 0.05
% 2.00/1.23  Demodulation         : 0.04
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.02
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.43
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

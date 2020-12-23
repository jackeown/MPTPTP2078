%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_8,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k2_enumset1(B_13,C_14,D_15,E_16)) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k1_enumset1(A_8,B_9,C_10),k1_tarski(D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_tarski(A_20),k1_enumset1(B_21,C_22,D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_36,C_33,C_37,B_34,D_35] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k1_enumset1(B_34,C_33,D_35),C_37)) = k2_xboole_0(k2_enumset1(A_36,B_34,C_33,D_35),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_76,plain,(
    ! [D_11,A_8,A_36,C_10,B_9] : k2_xboole_0(k2_enumset1(A_36,A_8,B_9,C_10),k1_tarski(D_11)) = k2_xboole_0(k1_tarski(A_36),k2_enumset1(A_8,B_9,C_10,D_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_80,plain,(
    ! [D_11,A_8,A_36,C_10,B_9] : k2_xboole_0(k2_enumset1(A_36,A_8,B_9,C_10),k1_tarski(D_11)) = k3_enumset1(A_36,A_8,B_9,C_10,D_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_10,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  
% 1.88/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.26  
% 1.88/1.26  %Foreground sorts:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Background operators:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Foreground operators:
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.26  
% 1.88/1.28  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 1.88/1.28  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.88/1.28  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.88/1.28  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.88/1.28  tff(f_36, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.88/1.28  tff(c_8, plain, (![E_16, D_15, C_14, A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k2_enumset1(B_13, C_14, D_15, E_16))=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.28  tff(c_6, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k1_enumset1(A_8, B_9, C_10), k1_tarski(D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.28  tff(c_28, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_tarski(A_20), k1_enumset1(B_21, C_22, D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.28  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.28  tff(c_64, plain, (![A_36, C_33, C_37, B_34, D_35]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k1_enumset1(B_34, C_33, D_35), C_37))=k2_xboole_0(k2_enumset1(A_36, B_34, C_33, D_35), C_37))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 1.88/1.28  tff(c_76, plain, (![D_11, A_8, A_36, C_10, B_9]: (k2_xboole_0(k2_enumset1(A_36, A_8, B_9, C_10), k1_tarski(D_11))=k2_xboole_0(k1_tarski(A_36), k2_enumset1(A_8, B_9, C_10, D_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 1.88/1.28  tff(c_80, plain, (![D_11, A_8, A_36, C_10, B_9]: (k2_xboole_0(k2_enumset1(A_36, A_8, B_9, C_10), k1_tarski(D_11))=k3_enumset1(A_36, A_8, B_9, C_10, D_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 1.88/1.28  tff(c_10, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.28  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_10])).
% 1.88/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.28  
% 1.88/1.28  Inference rules
% 1.88/1.28  ----------------------
% 1.88/1.28  #Ref     : 0
% 1.88/1.28  #Sup     : 17
% 1.88/1.28  #Fact    : 0
% 1.88/1.28  #Define  : 0
% 1.88/1.28  #Split   : 0
% 1.88/1.28  #Chain   : 0
% 1.88/1.28  #Close   : 0
% 1.88/1.28  
% 1.88/1.28  Ordering : KBO
% 1.88/1.28  
% 1.88/1.28  Simplification rules
% 1.88/1.28  ----------------------
% 1.88/1.28  #Subsume      : 0
% 1.88/1.28  #Demod        : 11
% 1.88/1.28  #Tautology    : 13
% 1.88/1.28  #SimpNegUnit  : 0
% 1.88/1.28  #BackRed      : 1
% 1.88/1.28  
% 1.88/1.28  #Partial instantiations: 0
% 1.88/1.28  #Strategies tried      : 1
% 1.88/1.28  
% 1.88/1.28  Timing (in seconds)
% 1.88/1.28  ----------------------
% 1.88/1.28  Preprocessing        : 0.33
% 1.88/1.28  Parsing              : 0.18
% 1.88/1.28  CNF conversion       : 0.02
% 1.88/1.28  Main loop            : 0.12
% 1.88/1.28  Inferencing          : 0.06
% 1.88/1.28  Reduction            : 0.04
% 1.88/1.28  Demodulation         : 0.03
% 1.88/1.28  BG Simplification    : 0.01
% 1.88/1.28  Subsumption          : 0.01
% 1.88/1.28  Abstraction          : 0.01
% 1.88/1.28  MUC search           : 0.00
% 1.88/1.28  Cooper               : 0.00
% 1.88/1.28  Total                : 0.48
% 1.88/1.29  Index Insertion      : 0.00
% 1.88/1.29  Index Deletion       : 0.00
% 1.88/1.29  Index Matching       : 0.00
% 1.88/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

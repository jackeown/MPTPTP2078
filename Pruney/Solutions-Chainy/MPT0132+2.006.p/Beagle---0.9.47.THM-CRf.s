%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k1_tarski(A_30),k2_xboole_0(k1_tarski(B_31),C_32)) = k2_xboole_0(k2_tarski(A_30,B_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_84,plain,(
    ! [C_11,B_10,A_30,D_12,A_9] : k2_xboole_0(k2_tarski(A_30,A_9),k1_enumset1(B_10,C_11,D_12)) = k2_xboole_0(k1_tarski(A_30),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_278,plain,(
    ! [C_11,B_10,A_30,D_12,A_9] : k2_xboole_0(k2_tarski(A_30,A_9),k1_enumset1(B_10,C_11,D_12)) = k3_enumset1(A_30,A_9,B_10,C_11,D_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:45:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.56  
% 2.51/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.57  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.57  
% 2.51/1.57  %Foreground sorts:
% 2.51/1.57  
% 2.51/1.57  
% 2.51/1.57  %Background operators:
% 2.51/1.57  
% 2.51/1.57  
% 2.51/1.57  %Foreground operators:
% 2.51/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.57  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.57  
% 2.51/1.58  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.51/1.58  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.51/1.58  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.51/1.58  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.51/1.58  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.51/1.58  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.58  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.58  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.58  tff(c_31, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.58  tff(c_66, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k1_tarski(A_30), k2_xboole_0(k1_tarski(B_31), C_32))=k2_xboole_0(k2_tarski(A_30, B_31), C_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 2.51/1.58  tff(c_84, plain, (![C_11, B_10, A_30, D_12, A_9]: (k2_xboole_0(k2_tarski(A_30, A_9), k1_enumset1(B_10, C_11, D_12))=k2_xboole_0(k1_tarski(A_30), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 2.51/1.58  tff(c_278, plain, (![C_11, B_10, A_30, D_12, A_9]: (k2_xboole_0(k2_tarski(A_30, A_9), k1_enumset1(B_10, C_11, D_12))=k3_enumset1(A_30, A_9, B_10, C_11, D_12))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 2.51/1.58  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.58  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_12])).
% 2.51/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.58  
% 2.51/1.58  Inference rules
% 2.51/1.58  ----------------------
% 2.51/1.58  #Ref     : 0
% 2.51/1.58  #Sup     : 69
% 2.51/1.58  #Fact    : 0
% 2.51/1.58  #Define  : 0
% 2.51/1.58  #Split   : 0
% 2.51/1.58  #Chain   : 0
% 2.51/1.58  #Close   : 0
% 2.51/1.58  
% 2.51/1.58  Ordering : KBO
% 2.51/1.58  
% 2.51/1.58  Simplification rules
% 2.51/1.58  ----------------------
% 2.51/1.58  #Subsume      : 0
% 2.51/1.58  #Demod        : 30
% 2.51/1.58  #Tautology    : 38
% 2.51/1.58  #SimpNegUnit  : 0
% 2.51/1.58  #BackRed      : 1
% 2.51/1.58  
% 2.51/1.58  #Partial instantiations: 0
% 2.51/1.58  #Strategies tried      : 1
% 2.51/1.58  
% 2.51/1.58  Timing (in seconds)
% 2.51/1.58  ----------------------
% 2.51/1.58  Preprocessing        : 0.43
% 2.51/1.58  Parsing              : 0.23
% 2.51/1.58  CNF conversion       : 0.03
% 2.51/1.58  Main loop            : 0.35
% 2.51/1.58  Inferencing          : 0.17
% 2.51/1.58  Reduction            : 0.10
% 2.51/1.58  Demodulation         : 0.09
% 2.51/1.58  BG Simplification    : 0.03
% 2.51/1.58  Subsumption          : 0.04
% 2.51/1.58  Abstraction          : 0.03
% 2.51/1.58  MUC search           : 0.00
% 2.51/1.58  Cooper               : 0.00
% 2.51/1.58  Total                : 0.81
% 2.51/1.58  Index Insertion      : 0.00
% 2.51/1.58  Index Deletion       : 0.00
% 2.51/1.58  Index Matching       : 0.00
% 2.51/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k2_tarski(D_7,E_8)) = k3_enumset1(A_4,B_5,C_6,D_7,E_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k2_xboole_0(A_16,B_17),C_18) = k2_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_xboole_0(k1_tarski(B_23),C_24)) = k2_xboole_0(k2_tarski(A_22,B_23),C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_70,plain,(
    ! [A_22,A_9,B_10] : k2_xboole_0(k2_tarski(A_22,A_9),k1_tarski(B_10)) = k2_xboole_0(k1_tarski(A_22),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_74,plain,(
    ! [A_22,A_9,B_10] : k2_xboole_0(k1_tarski(A_22),k2_tarski(A_9,B_10)) = k1_enumset1(A_22,A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_40,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_33,B_34,C_35,C_36] : k2_xboole_0(k2_tarski(A_33,B_34),k2_xboole_0(k1_tarski(C_35),C_36)) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_114,plain,(
    ! [B_10,A_33,B_34,A_22,A_9] : k2_xboole_0(k1_enumset1(A_33,B_34,A_22),k2_tarski(A_9,B_10)) = k2_xboole_0(k2_tarski(A_33,B_34),k1_enumset1(A_22,A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_102])).

tff(c_124,plain,(
    ! [B_10,A_33,B_34,A_22,A_9] : k2_xboole_0(k2_tarski(A_33,B_34),k1_enumset1(A_22,A_9,B_10)) = k3_enumset1(A_33,B_34,A_22,A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.21  
% 1.95/1.22  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.95/1.22  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.95/1.22  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.95/1.22  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.95/1.22  tff(f_36, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.95/1.22  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k2_tarski(D_7, E_8))=k3_enumset1(A_4, B_5, C_6, D_7, E_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.22  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_11, B_12), k1_tarski(C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.22  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.22  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k2_xboole_0(A_16, B_17), C_18)=k2_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.22  tff(c_52, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_xboole_0(k1_tarski(B_23), C_24))=k2_xboole_0(k2_tarski(A_22, B_23), C_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20])).
% 1.95/1.22  tff(c_70, plain, (![A_22, A_9, B_10]: (k2_xboole_0(k2_tarski(A_22, A_9), k1_tarski(B_10))=k2_xboole_0(k1_tarski(A_22), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 1.95/1.22  tff(c_74, plain, (![A_22, A_9, B_10]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(A_9, B_10))=k1_enumset1(A_22, A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_70])).
% 1.95/1.22  tff(c_40, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k2_tarski(A_19, B_20), k1_tarski(C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.22  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.22  tff(c_102, plain, (![A_33, B_34, C_35, C_36]: (k2_xboole_0(k2_tarski(A_33, B_34), k2_xboole_0(k1_tarski(C_35), C_36))=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), C_36))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2])).
% 1.95/1.22  tff(c_114, plain, (![B_10, A_33, B_34, A_22, A_9]: (k2_xboole_0(k1_enumset1(A_33, B_34, A_22), k2_tarski(A_9, B_10))=k2_xboole_0(k2_tarski(A_33, B_34), k1_enumset1(A_22, A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_102])).
% 1.95/1.22  tff(c_124, plain, (![B_10, A_33, B_34, A_22, A_9]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_enumset1(A_22, A_9, B_10))=k3_enumset1(A_33, B_34, A_22, A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_114])).
% 1.95/1.22  tff(c_10, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.95/1.22  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_10])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 39
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 0
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 0
% 1.95/1.22  #Demod        : 19
% 1.95/1.22  #Tautology    : 23
% 1.95/1.22  #SimpNegUnit  : 0
% 1.95/1.22  #BackRed      : 1
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.27
% 1.95/1.22  Parsing              : 0.15
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.15
% 1.95/1.22  Inferencing          : 0.07
% 1.95/1.22  Reduction            : 0.05
% 1.95/1.22  Demodulation         : 0.04
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.02
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.45
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

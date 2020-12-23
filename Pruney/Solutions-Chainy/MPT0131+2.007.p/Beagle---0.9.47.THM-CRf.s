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
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k2_tarski(D_9,E_10)) = k3_enumset1(A_6,B_7,C_8,D_9,E_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_tarski(A_16),k1_enumset1(B_17,C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k1_tarski(A_34),k2_xboole_0(k1_tarski(B_35),C_36)) = k2_xboole_0(k2_tarski(A_34,B_35),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_42])).

tff(c_98,plain,(
    ! [A_34,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_34,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k1_tarski(A_34),k1_enumset1(A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_105,plain,(
    ! [A_34,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_34,A_13),k2_tarski(B_14,C_15)) = k2_enumset1(A_34,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_98])).

tff(c_143,plain,(
    ! [A_49,B_50,C_51,C_52] : k2_xboole_0(k1_tarski(A_49),k2_xboole_0(k2_tarski(B_50,C_51),C_52)) = k2_xboole_0(k1_enumset1(A_49,B_50,C_51),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_158,plain,(
    ! [A_13,A_34,B_14,C_15,A_49] : k2_xboole_0(k1_enumset1(A_49,A_34,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k1_tarski(A_49),k2_enumset1(A_34,A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_143])).

tff(c_165,plain,(
    ! [A_13,A_34,B_14,C_15,A_49] : k2_xboole_0(k1_tarski(A_49),k2_enumset1(A_34,A_13,B_14,C_15)) = k3_enumset1(A_49,A_34,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.30  
% 2.03/1.30  %Foreground sorts:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Background operators:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Foreground operators:
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.30  
% 2.03/1.31  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 2.03/1.31  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.03/1.31  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.03/1.31  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.03/1.31  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.03/1.31  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.03/1.31  tff(c_6, plain, (![B_7, D_9, C_8, E_10, A_6]: (k2_xboole_0(k1_enumset1(A_6, B_7, C_8), k2_tarski(D_9, E_10))=k3_enumset1(A_6, B_7, C_8, D_9, E_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.31  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_tarski(A_16), k1_enumset1(B_17, C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.31  tff(c_10, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.31  tff(c_8, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.31  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.31  tff(c_77, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k1_tarski(A_34), k2_xboole_0(k1_tarski(B_35), C_36))=k2_xboole_0(k2_tarski(A_34, B_35), C_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_42])).
% 2.03/1.31  tff(c_98, plain, (![A_34, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_34, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k1_tarski(A_34), k1_enumset1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_77])).
% 2.03/1.31  tff(c_105, plain, (![A_34, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_34, A_13), k2_tarski(B_14, C_15))=k2_enumset1(A_34, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_98])).
% 2.03/1.31  tff(c_143, plain, (![A_49, B_50, C_51, C_52]: (k2_xboole_0(k1_tarski(A_49), k2_xboole_0(k2_tarski(B_50, C_51), C_52))=k2_xboole_0(k1_enumset1(A_49, B_50, C_51), C_52))), inference(superposition, [status(thm), theory('equality')], [c_10, c_42])).
% 2.03/1.31  tff(c_158, plain, (![A_13, A_34, B_14, C_15, A_49]: (k2_xboole_0(k1_enumset1(A_49, A_34, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k1_tarski(A_49), k2_enumset1(A_34, A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_143])).
% 2.03/1.31  tff(c_165, plain, (![A_13, A_34, B_14, C_15, A_49]: (k2_xboole_0(k1_tarski(A_49), k2_enumset1(A_34, A_13, B_14, C_15))=k3_enumset1(A_49, A_34, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 2.03/1.31  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.31  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_14])).
% 2.03/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.31  
% 2.03/1.31  Inference rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Ref     : 0
% 2.03/1.31  #Sup     : 50
% 2.03/1.31  #Fact    : 0
% 2.03/1.31  #Define  : 0
% 2.03/1.31  #Split   : 0
% 2.03/1.31  #Chain   : 0
% 2.03/1.31  #Close   : 0
% 2.03/1.31  
% 2.03/1.31  Ordering : KBO
% 2.03/1.31  
% 2.03/1.31  Simplification rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Subsume      : 0
% 2.03/1.31  #Demod        : 23
% 2.03/1.31  #Tautology    : 30
% 2.03/1.31  #SimpNegUnit  : 0
% 2.03/1.31  #BackRed      : 1
% 2.03/1.31  
% 2.03/1.31  #Partial instantiations: 0
% 2.03/1.31  #Strategies tried      : 1
% 2.03/1.31  
% 2.03/1.31  Timing (in seconds)
% 2.03/1.31  ----------------------
% 2.03/1.31  Preprocessing        : 0.31
% 2.03/1.31  Parsing              : 0.17
% 2.03/1.31  CNF conversion       : 0.02
% 2.03/1.31  Main loop            : 0.19
% 2.03/1.31  Inferencing          : 0.08
% 2.03/1.31  Reduction            : 0.06
% 2.03/1.31  Demodulation         : 0.05
% 2.03/1.31  BG Simplification    : 0.02
% 2.03/1.31  Subsumption          : 0.02
% 2.03/1.31  Abstraction          : 0.01
% 2.03/1.31  MUC search           : 0.00
% 2.03/1.31  Cooper               : 0.00
% 2.03/1.32  Total                : 0.53
% 2.03/1.32  Index Insertion      : 0.00
% 2.03/1.32  Index Deletion       : 0.00
% 2.03/1.32  Index Matching       : 0.00
% 2.03/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

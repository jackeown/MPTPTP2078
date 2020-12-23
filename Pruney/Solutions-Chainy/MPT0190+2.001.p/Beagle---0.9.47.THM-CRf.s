%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  20 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_21,B_22,B_23,A_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(B_23,A_24)) = k2_enumset1(A_21,B_22,A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_21,B_22,B_23,A_24] : k2_enumset1(A_21,B_22,B_23,A_24) = k2_enumset1(A_21,B_22,A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_4])).

tff(c_61,plain,(
    ! [B_13,A_14,C_15,D_16] : k2_xboole_0(k2_tarski(B_13,A_14),k2_tarski(C_15,D_16)) = k2_enumset1(A_14,B_13,C_15,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_67,plain,(
    ! [B_13,A_14,C_15,D_16] : k2_enumset1(B_13,A_14,C_15,D_16) = k2_enumset1(A_14,B_13,C_15,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.19  
% 1.95/1.20  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.95/1.20  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.95/1.20  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_enumset1)).
% 1.95/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.20  tff(c_40, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_tarski(C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.20  tff(c_124, plain, (![A_21, B_22, B_23, A_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(B_23, A_24))=k2_enumset1(A_21, B_22, A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40])).
% 1.95/1.20  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.20  tff(c_133, plain, (![A_21, B_22, B_23, A_24]: (k2_enumset1(A_21, B_22, B_23, A_24)=k2_enumset1(A_21, B_22, A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_124, c_4])).
% 1.95/1.20  tff(c_61, plain, (![B_13, A_14, C_15, D_16]: (k2_xboole_0(k2_tarski(B_13, A_14), k2_tarski(C_15, D_16))=k2_enumset1(A_14, B_13, C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40])).
% 1.95/1.20  tff(c_67, plain, (![B_13, A_14, C_15, D_16]: (k2_enumset1(B_13, A_14, C_15, D_16)=k2_enumset1(A_14, B_13, C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 1.95/1.20  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.20  tff(c_90, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_6])).
% 1.95/1.20  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_90])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 80
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 0
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 1.95/1.20  
% 1.95/1.20  Ordering : KBO
% 1.95/1.20  
% 1.95/1.20  Simplification rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Subsume      : 17
% 1.95/1.20  #Demod        : 6
% 1.95/1.20  #Tautology    : 42
% 1.95/1.20  #SimpNegUnit  : 0
% 1.95/1.20  #BackRed      : 1
% 1.95/1.20  
% 1.95/1.20  #Partial instantiations: 0
% 1.95/1.20  #Strategies tried      : 1
% 1.95/1.20  
% 1.95/1.20  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.20  Preprocessing        : 0.25
% 1.95/1.20  Parsing              : 0.13
% 1.95/1.20  CNF conversion       : 0.01
% 1.95/1.20  Main loop            : 0.18
% 1.95/1.20  Inferencing          : 0.07
% 1.95/1.20  Reduction            : 0.07
% 1.95/1.20  Demodulation         : 0.06
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.02
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.45
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

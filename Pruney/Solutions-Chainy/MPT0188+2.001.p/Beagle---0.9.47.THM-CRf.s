%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:50 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   27 (  42 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  31 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1026,plain,(
    ! [A_57,B_58,A_59,B_60] : k2_xboole_0(k2_tarski(A_57,B_58),k2_tarski(A_59,B_60)) = k2_enumset1(A_57,B_58,B_60,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1035,plain,(
    ! [A_57,B_58,B_60,A_59] : k2_enumset1(A_57,B_58,B_60,A_59) = k2_enumset1(A_57,B_58,A_59,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_4])).

tff(c_104,plain,(
    ! [B_25,A_26,C_27,D_28] : k2_xboole_0(k2_tarski(B_25,A_26),k2_tarski(C_27,D_28)) = k2_enumset1(A_26,B_25,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_110,plain,(
    ! [B_25,A_26,C_27,D_28] : k2_enumset1(B_25,A_26,C_27,D_28) = k2_enumset1(A_26,B_25,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4])).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_133,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_11])).

tff(c_1288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:26:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.49  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.26/1.49  
% 3.26/1.49  %Foreground sorts:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Background operators:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Foreground operators:
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.49  
% 3.26/1.50  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.26/1.50  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.26/1.50  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 3.26/1.50  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 3.26/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.50  tff(c_83, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.50  tff(c_1026, plain, (![A_57, B_58, A_59, B_60]: (k2_xboole_0(k2_tarski(A_57, B_58), k2_tarski(A_59, B_60))=k2_enumset1(A_57, B_58, B_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 3.26/1.50  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.50  tff(c_1035, plain, (![A_57, B_58, B_60, A_59]: (k2_enumset1(A_57, B_58, B_60, A_59)=k2_enumset1(A_57, B_58, A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_4])).
% 3.26/1.50  tff(c_104, plain, (![B_25, A_26, C_27, D_28]: (k2_xboole_0(k2_tarski(B_25, A_26), k2_tarski(C_27, D_28))=k2_enumset1(A_26, B_25, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 3.26/1.50  tff(c_110, plain, (![B_25, A_26, C_27, D_28]: (k2_enumset1(B_25, A_26, C_27, D_28)=k2_enumset1(A_26, B_25, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_104, c_4])).
% 3.26/1.50  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.50  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.50  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.26/1.50  tff(c_133, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_11])).
% 3.26/1.50  tff(c_1288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1035, c_133])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 394
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 0
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 130
% 3.26/1.50  #Demod        : 9
% 3.26/1.50  #Tautology    : 77
% 3.26/1.50  #SimpNegUnit  : 0
% 3.26/1.50  #BackRed      : 2
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.26
% 3.26/1.50  Parsing              : 0.14
% 3.26/1.50  CNF conversion       : 0.01
% 3.26/1.50  Main loop            : 0.50
% 3.26/1.50  Inferencing          : 0.15
% 3.26/1.50  Reduction            : 0.23
% 3.26/1.50  Demodulation         : 0.21
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.07
% 3.26/1.50  Abstraction          : 0.03
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.78
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

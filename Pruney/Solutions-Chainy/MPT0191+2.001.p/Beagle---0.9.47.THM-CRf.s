%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   24 (  37 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  27 expanded)
%              Number of equality atoms :   13 (  26 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k2_tarski(A_17,B_18),k2_tarski(C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [B_21,A_22,C_23,D_24] : k2_xboole_0(k2_tarski(B_21,A_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_22,B_21,C_23,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [B_21,A_22,C_23,D_24] : k2_enumset1(B_21,A_22,C_23,D_24) = k2_enumset1(A_22,B_21,C_23,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_4])).

tff(c_8,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8])).

tff(c_157,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_9])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.64/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.12  
% 1.78/1.13  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 1.78/1.13  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.78/1.13  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.78/1.13  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_enumset1)).
% 1.78/1.13  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.13  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.13  tff(c_72, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k2_tarski(A_17, B_18), k2_tarski(C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.13  tff(c_93, plain, (![B_21, A_22, C_23, D_24]: (k2_xboole_0(k2_tarski(B_21, A_22), k2_tarski(C_23, D_24))=k2_enumset1(A_22, B_21, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 1.78/1.13  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.13  tff(c_99, plain, (![B_21, A_22, C_23, D_24]: (k2_enumset1(B_21, A_22, C_23, D_24)=k2_enumset1(A_22, B_21, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_93, c_4])).
% 1.78/1.13  tff(c_8, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.78/1.13  tff(c_9, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8])).
% 1.78/1.13  tff(c_157, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_9])).
% 1.78/1.13  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_157])).
% 1.78/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  Inference rules
% 1.78/1.13  ----------------------
% 1.78/1.13  #Ref     : 0
% 1.78/1.13  #Sup     : 40
% 1.78/1.13  #Fact    : 0
% 1.78/1.13  #Define  : 0
% 1.78/1.13  #Split   : 0
% 1.78/1.13  #Chain   : 0
% 1.78/1.13  #Close   : 0
% 1.78/1.13  
% 1.78/1.13  Ordering : KBO
% 1.78/1.13  
% 1.78/1.13  Simplification rules
% 1.78/1.13  ----------------------
% 1.78/1.13  #Subsume      : 4
% 1.78/1.13  #Demod        : 9
% 1.78/1.13  #Tautology    : 22
% 1.78/1.13  #SimpNegUnit  : 0
% 1.78/1.13  #BackRed      : 1
% 1.78/1.13  
% 1.78/1.13  #Partial instantiations: 0
% 1.78/1.13  #Strategies tried      : 1
% 1.78/1.13  
% 1.78/1.13  Timing (in seconds)
% 1.78/1.13  ----------------------
% 1.78/1.13  Preprocessing        : 0.24
% 1.78/1.13  Parsing              : 0.12
% 1.78/1.13  CNF conversion       : 0.01
% 1.78/1.13  Main loop            : 0.14
% 1.78/1.13  Inferencing          : 0.05
% 1.78/1.13  Reduction            : 0.05
% 1.78/1.13  Demodulation         : 0.05
% 1.78/1.13  BG Simplification    : 0.01
% 1.78/1.13  Subsumption          : 0.02
% 1.78/1.13  Abstraction          : 0.01
% 1.78/1.13  MUC search           : 0.00
% 1.78/1.13  Cooper               : 0.00
% 1.78/1.13  Total                : 0.40
% 1.78/1.13  Index Insertion      : 0.00
% 1.78/1.13  Index Deletion       : 0.00
% 1.78/1.13  Index Matching       : 0.00
% 1.78/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:46:57 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  50 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  39 expanded)
%              Number of equality atoms :   17 (  38 expanded)
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_4,plain,(
    ! [B_4,C_5,A_3,D_6] : k2_enumset1(B_4,C_5,A_3,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_377,plain,(
    ! [A_41,B_42,B_43,A_44] : k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(B_43,A_44)) = k2_enumset1(A_41,B_42,A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_386,plain,(
    ! [A_41,B_42,B_43,A_44] : k2_enumset1(A_41,B_42,B_43,A_44) = k2_enumset1(A_41,B_42,A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_6])).

tff(c_104,plain,(
    ! [B_25,A_26,C_27,D_28] : k2_xboole_0(k2_tarski(B_25,A_26),k2_tarski(C_27,D_28)) = k2_enumset1(A_26,B_25,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_133,plain,(
    ! [B_29,A_30,C_31,D_32] : k2_enumset1(B_29,A_30,C_31,D_32) = k2_enumset1(A_30,B_29,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_151,plain,(
    ! [B_29,C_31,A_30,D_32] : k2_enumset1(B_29,C_31,A_30,D_32) = k2_enumset1(B_29,A_30,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4])).

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_10])).

tff(c_190,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_11])).

tff(c_541,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_386,c_190])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.29  
% 2.23/1.29  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 2.23/1.29  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.23/1.29  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.23/1.29  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 2.23/1.29  tff(c_4, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.29  tff(c_83, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_377, plain, (![A_41, B_42, B_43, A_44]: (k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(B_43, A_44))=k2_enumset1(A_41, B_42, A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.23/1.29  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_386, plain, (![A_41, B_42, B_43, A_44]: (k2_enumset1(A_41, B_42, B_43, A_44)=k2_enumset1(A_41, B_42, A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_377, c_6])).
% 2.23/1.29  tff(c_104, plain, (![B_25, A_26, C_27, D_28]: (k2_xboole_0(k2_tarski(B_25, A_26), k2_tarski(C_27, D_28))=k2_enumset1(A_26, B_25, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.23/1.29  tff(c_133, plain, (![B_29, A_30, C_31, D_32]: (k2_enumset1(B_29, A_30, C_31, D_32)=k2_enumset1(A_30, B_29, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 2.23/1.29  tff(c_151, plain, (![B_29, C_31, A_30, D_32]: (k2_enumset1(B_29, C_31, A_30, D_32)=k2_enumset1(B_29, A_30, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_133, c_4])).
% 2.23/1.29  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.29  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_10])).
% 2.23/1.29  tff(c_190, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_11])).
% 2.23/1.29  tff(c_541, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_386, c_190])).
% 2.23/1.29  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_541])).
% 2.23/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  Inference rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Ref     : 0
% 2.23/1.29  #Sup     : 154
% 2.23/1.29  #Fact    : 0
% 2.23/1.29  #Define  : 0
% 2.23/1.29  #Split   : 0
% 2.23/1.29  #Chain   : 0
% 2.23/1.29  #Close   : 0
% 2.23/1.29  
% 2.23/1.29  Ordering : KBO
% 2.23/1.29  
% 2.23/1.29  Simplification rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Subsume      : 45
% 2.23/1.29  #Demod        : 10
% 2.23/1.29  #Tautology    : 56
% 2.23/1.29  #SimpNegUnit  : 0
% 2.23/1.29  #BackRed      : 2
% 2.23/1.29  
% 2.23/1.29  #Partial instantiations: 0
% 2.23/1.29  #Strategies tried      : 1
% 2.23/1.29  
% 2.23/1.29  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.26
% 2.23/1.30  Parsing              : 0.14
% 2.23/1.30  CNF conversion       : 0.01
% 2.23/1.30  Main loop            : 0.28
% 2.23/1.30  Inferencing          : 0.10
% 2.23/1.30  Reduction            : 0.12
% 2.23/1.30  Demodulation         : 0.11
% 2.23/1.30  BG Simplification    : 0.01
% 2.23/1.30  Subsumption          : 0.04
% 2.23/1.30  Abstraction          : 0.02
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.57
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:59 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  36 expanded)
%              Number of equality atoms :   19 (  35 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_25,B_26,C_27,D_28] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(C_27,D_28)) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_649,plain,(
    ! [A_49,B_50,A_51,B_52] : k2_xboole_0(k2_tarski(A_49,B_50),k2_tarski(A_51,B_52)) = k2_enumset1(A_49,B_50,B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_658,plain,(
    ! [A_49,B_50,B_52,A_51] : k2_enumset1(A_49,B_50,B_52,A_51) = k2_enumset1(A_49,B_50,A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_4])).

tff(c_6,plain,(
    ! [B_8,D_10,A_7,C_9] : k2_enumset1(B_8,D_10,A_7,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(C_31,D_32)) = k2_enumset1(B_30,A_29,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_191,plain,(
    ! [B_33,A_34,C_35,D_36] : k2_enumset1(B_33,A_34,C_35,D_36) = k2_enumset1(A_34,B_33,C_35,D_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4])).

tff(c_254,plain,(
    ! [B_8,D_10,A_7,C_9] : k2_enumset1(B_8,D_10,A_7,C_9) = k2_enumset1(B_8,A_7,C_9,D_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_191])).

tff(c_54,plain,(
    ! [B_17,D_18,A_19,C_20] : k2_enumset1(B_17,D_18,A_19,C_20) = k2_enumset1(A_19,B_17,C_20,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [D_10,C_9,B_8,A_7] : k2_enumset1(D_10,C_9,B_8,A_7) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_10])).

tff(c_83,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11])).

tff(c_499,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_83])).

tff(c_863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.39  
% 2.96/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.39  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.39  
% 2.96/1.39  %Foreground sorts:
% 2.96/1.39  
% 2.96/1.39  
% 2.96/1.39  %Background operators:
% 2.96/1.39  
% 2.96/1.39  
% 2.96/1.39  %Foreground operators:
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.39  
% 2.96/1.40  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.96/1.40  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.96/1.40  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 2.96/1.40  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.96/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.40  tff(c_141, plain, (![A_25, B_26, C_27, D_28]: (k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(C_27, D_28))=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.40  tff(c_649, plain, (![A_49, B_50, A_51, B_52]: (k2_xboole_0(k2_tarski(A_49, B_50), k2_tarski(A_51, B_52))=k2_enumset1(A_49, B_50, B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 2.96/1.40  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.40  tff(c_658, plain, (![A_49, B_50, B_52, A_51]: (k2_enumset1(A_49, B_50, B_52, A_51)=k2_enumset1(A_49, B_50, A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_649, c_4])).
% 2.96/1.40  tff(c_6, plain, (![B_8, D_10, A_7, C_9]: (k2_enumset1(B_8, D_10, A_7, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.40  tff(c_162, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(B_30, A_29, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 2.96/1.40  tff(c_191, plain, (![B_33, A_34, C_35, D_36]: (k2_enumset1(B_33, A_34, C_35, D_36)=k2_enumset1(A_34, B_33, C_35, D_36))), inference(superposition, [status(thm), theory('equality')], [c_162, c_4])).
% 2.96/1.40  tff(c_254, plain, (![B_8, D_10, A_7, C_9]: (k2_enumset1(B_8, D_10, A_7, C_9)=k2_enumset1(B_8, A_7, C_9, D_10))), inference(superposition, [status(thm), theory('equality')], [c_6, c_191])).
% 2.96/1.40  tff(c_54, plain, (![B_17, D_18, A_19, C_20]: (k2_enumset1(B_17, D_18, A_19, C_20)=k2_enumset1(A_19, B_17, C_20, D_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.40  tff(c_78, plain, (![D_10, C_9, B_8, A_7]: (k2_enumset1(D_10, C_9, B_8, A_7)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 2.96/1.40  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.96/1.40  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_6, c_10])).
% 2.96/1.40  tff(c_83, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11])).
% 2.96/1.40  tff(c_499, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_83])).
% 2.96/1.40  tff(c_863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_658, c_499])).
% 2.96/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.40  
% 2.96/1.40  Inference rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Ref     : 0
% 2.96/1.40  #Sup     : 258
% 2.96/1.40  #Fact    : 0
% 2.96/1.40  #Define  : 0
% 2.96/1.40  #Split   : 0
% 2.96/1.40  #Chain   : 0
% 2.96/1.40  #Close   : 0
% 2.96/1.40  
% 2.96/1.40  Ordering : KBO
% 2.96/1.40  
% 2.96/1.40  Simplification rules
% 2.96/1.40  ----------------------
% 2.96/1.40  #Subsume      : 69
% 2.96/1.40  #Demod        : 11
% 2.96/1.40  #Tautology    : 61
% 2.96/1.40  #SimpNegUnit  : 0
% 2.96/1.40  #BackRed      : 3
% 2.96/1.40  
% 2.96/1.40  #Partial instantiations: 0
% 2.96/1.40  #Strategies tried      : 1
% 2.96/1.40  
% 2.96/1.40  Timing (in seconds)
% 2.96/1.40  ----------------------
% 2.96/1.40  Preprocessing        : 0.26
% 2.96/1.40  Parsing              : 0.14
% 2.96/1.40  CNF conversion       : 0.01
% 2.96/1.40  Main loop            : 0.38
% 2.96/1.40  Inferencing          : 0.12
% 2.96/1.40  Reduction            : 0.17
% 2.96/1.40  Demodulation         : 0.15
% 2.96/1.40  BG Simplification    : 0.02
% 2.96/1.40  Subsumption          : 0.06
% 2.96/1.40  Abstraction          : 0.02
% 2.96/1.40  MUC search           : 0.00
% 2.96/1.40  Cooper               : 0.00
% 2.96/1.40  Total                : 0.67
% 2.96/1.40  Index Insertion      : 0.00
% 2.96/1.40  Index Deletion       : 0.00
% 2.96/1.40  Index Matching       : 0.00
% 2.96/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

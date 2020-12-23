%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  46 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k2_tarski(A_26,B_27),k2_tarski(C_28,D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_586,plain,(
    ! [A_49,B_50,A_51,B_52] : k2_xboole_0(k2_tarski(A_49,B_50),k2_tarski(A_51,B_52)) = k2_enumset1(A_49,B_50,B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_142,plain,(
    ! [B_2,A_1,C_28,D_29] : k2_xboole_0(k2_tarski(B_2,A_1),k2_tarski(C_28,D_29)) = k2_enumset1(A_1,B_2,C_28,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_621,plain,(
    ! [B_53,A_54,A_55,B_56] : k2_enumset1(B_53,A_54,A_55,B_56) = k2_enumset1(A_54,B_53,B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_142])).

tff(c_1078,plain,(
    ! [A_67,C_68,B_69] : k2_enumset1(A_67,A_67,C_68,B_69) = k1_enumset1(A_67,B_69,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_621])).

tff(c_1124,plain,(
    ! [A_67,C_68,B_69] : k1_enumset1(A_67,C_68,B_69) = k1_enumset1(A_67,B_69,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_8])).

tff(c_55,plain,(
    ! [B_19,C_20,A_21,D_22] : k2_enumset1(B_19,C_20,A_21,D_22) = k2_enumset1(A_21,B_19,C_20,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_21,C_20,D_22] : k2_enumset1(A_21,C_20,C_20,D_22) = k1_enumset1(C_20,A_21,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_673,plain,(
    ! [B_56,A_54,A_55] : k2_enumset1(B_56,A_54,A_55,B_56) = k1_enumset1(B_56,A_54,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_75])).

tff(c_4,plain,(
    ! [B_4,C_5,A_3,D_6] : k2_enumset1(B_4,C_5,A_3,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_11])).

tff(c_792,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_12])).

tff(c_1191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.49  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.02/1.49  
% 3.02/1.49  %Foreground sorts:
% 3.02/1.49  
% 3.02/1.49  
% 3.02/1.49  %Background operators:
% 3.02/1.49  
% 3.02/1.49  
% 3.02/1.49  %Foreground operators:
% 3.02/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.49  
% 3.02/1.50  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.02/1.50  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.02/1.50  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.02/1.50  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 3.02/1.50  tff(f_36, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.02/1.50  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.50  tff(c_133, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k2_tarski(A_26, B_27), k2_tarski(C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.50  tff(c_586, plain, (![A_49, B_50, A_51, B_52]: (k2_xboole_0(k2_tarski(A_49, B_50), k2_tarski(A_51, B_52))=k2_enumset1(A_49, B_50, B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 3.02/1.50  tff(c_142, plain, (![B_2, A_1, C_28, D_29]: (k2_xboole_0(k2_tarski(B_2, A_1), k2_tarski(C_28, D_29))=k2_enumset1(A_1, B_2, C_28, D_29))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 3.02/1.50  tff(c_621, plain, (![B_53, A_54, A_55, B_56]: (k2_enumset1(B_53, A_54, A_55, B_56)=k2_enumset1(A_54, B_53, B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_586, c_142])).
% 3.02/1.50  tff(c_1078, plain, (![A_67, C_68, B_69]: (k2_enumset1(A_67, A_67, C_68, B_69)=k1_enumset1(A_67, B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_8, c_621])).
% 3.02/1.50  tff(c_1124, plain, (![A_67, C_68, B_69]: (k1_enumset1(A_67, C_68, B_69)=k1_enumset1(A_67, B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_8])).
% 3.02/1.50  tff(c_55, plain, (![B_19, C_20, A_21, D_22]: (k2_enumset1(B_19, C_20, A_21, D_22)=k2_enumset1(A_21, B_19, C_20, D_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.50  tff(c_75, plain, (![A_21, C_20, D_22]: (k2_enumset1(A_21, C_20, C_20, D_22)=k1_enumset1(C_20, A_21, D_22))), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 3.02/1.50  tff(c_673, plain, (![B_56, A_54, A_55]: (k2_enumset1(B_56, A_54, A_55, B_56)=k1_enumset1(B_56, A_54, A_55))), inference(superposition, [status(thm), theory('equality')], [c_621, c_75])).
% 3.02/1.50  tff(c_4, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.50  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.50  tff(c_10, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.50  tff(c_11, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.02/1.50  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_11])).
% 3.02/1.50  tff(c_792, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_673, c_12])).
% 3.02/1.50  tff(c_1191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1124, c_792])).
% 3.02/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.50  
% 3.02/1.50  Inference rules
% 3.02/1.50  ----------------------
% 3.02/1.50  #Ref     : 0
% 3.02/1.50  #Sup     : 310
% 3.02/1.50  #Fact    : 0
% 3.02/1.50  #Define  : 0
% 3.02/1.50  #Split   : 0
% 3.02/1.50  #Chain   : 0
% 3.02/1.50  #Close   : 0
% 3.02/1.50  
% 3.02/1.50  Ordering : KBO
% 3.02/1.50  
% 3.02/1.50  Simplification rules
% 3.02/1.50  ----------------------
% 3.02/1.50  #Subsume      : 60
% 3.02/1.50  #Demod        : 63
% 3.02/1.50  #Tautology    : 148
% 3.02/1.50  #SimpNegUnit  : 0
% 3.02/1.50  #BackRed      : 2
% 3.02/1.50  
% 3.02/1.50  #Partial instantiations: 0
% 3.02/1.50  #Strategies tried      : 1
% 3.02/1.50  
% 3.02/1.50  Timing (in seconds)
% 3.02/1.50  ----------------------
% 3.02/1.50  Preprocessing        : 0.26
% 3.02/1.50  Parsing              : 0.14
% 3.02/1.50  CNF conversion       : 0.01
% 3.02/1.50  Main loop            : 0.40
% 3.02/1.50  Inferencing          : 0.14
% 3.02/1.50  Reduction            : 0.17
% 3.02/1.50  Demodulation         : 0.15
% 3.02/1.50  BG Simplification    : 0.02
% 3.02/1.50  Subsumption          : 0.05
% 3.02/1.51  Abstraction          : 0.02
% 3.02/1.51  MUC search           : 0.00
% 3.02/1.51  Cooper               : 0.00
% 3.02/1.51  Total                : 0.68
% 3.02/1.51  Index Insertion      : 0.00
% 3.02/1.51  Index Deletion       : 0.00
% 3.02/1.51  Index Matching       : 0.00
% 3.02/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

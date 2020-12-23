%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

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
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.77/1.44  
% 2.77/1.44  %Foreground sorts:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Background operators:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Foreground operators:
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.44  
% 2.77/1.45  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.77/1.45  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.77/1.45  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 2.77/1.45  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 2.77/1.45  tff(f_36, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 2.77/1.45  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.45  tff(c_133, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k2_tarski(A_26, B_27), k2_tarski(C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.45  tff(c_586, plain, (![A_49, B_50, A_51, B_52]: (k2_xboole_0(k2_tarski(A_49, B_50), k2_tarski(A_51, B_52))=k2_enumset1(A_49, B_50, B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 2.77/1.45  tff(c_142, plain, (![B_2, A_1, C_28, D_29]: (k2_xboole_0(k2_tarski(B_2, A_1), k2_tarski(C_28, D_29))=k2_enumset1(A_1, B_2, C_28, D_29))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 2.77/1.45  tff(c_621, plain, (![B_53, A_54, A_55, B_56]: (k2_enumset1(B_53, A_54, A_55, B_56)=k2_enumset1(A_54, B_53, B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_586, c_142])).
% 2.77/1.45  tff(c_1078, plain, (![A_67, C_68, B_69]: (k2_enumset1(A_67, A_67, C_68, B_69)=k1_enumset1(A_67, B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_8, c_621])).
% 2.77/1.45  tff(c_1124, plain, (![A_67, C_68, B_69]: (k1_enumset1(A_67, C_68, B_69)=k1_enumset1(A_67, B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_8])).
% 2.77/1.45  tff(c_55, plain, (![B_19, C_20, A_21, D_22]: (k2_enumset1(B_19, C_20, A_21, D_22)=k2_enumset1(A_21, B_19, C_20, D_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.45  tff(c_75, plain, (![A_21, C_20, D_22]: (k2_enumset1(A_21, C_20, C_20, D_22)=k1_enumset1(C_20, A_21, D_22))), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 2.77/1.45  tff(c_673, plain, (![B_56, A_54, A_55]: (k2_enumset1(B_56, A_54, A_55, B_56)=k1_enumset1(B_56, A_54, A_55))), inference(superposition, [status(thm), theory('equality')], [c_621, c_75])).
% 2.77/1.45  tff(c_4, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.45  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.45  tff(c_10, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.45  tff(c_11, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.77/1.45  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_11])).
% 2.77/1.45  tff(c_792, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_673, c_12])).
% 2.77/1.45  tff(c_1191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1124, c_792])).
% 2.77/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.45  
% 2.77/1.45  Inference rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Ref     : 0
% 2.77/1.45  #Sup     : 310
% 2.77/1.45  #Fact    : 0
% 2.77/1.45  #Define  : 0
% 2.77/1.45  #Split   : 0
% 2.77/1.45  #Chain   : 0
% 2.77/1.45  #Close   : 0
% 2.77/1.45  
% 2.77/1.45  Ordering : KBO
% 2.77/1.45  
% 2.77/1.45  Simplification rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Subsume      : 60
% 2.77/1.45  #Demod        : 63
% 2.77/1.45  #Tautology    : 148
% 2.77/1.45  #SimpNegUnit  : 0
% 2.77/1.45  #BackRed      : 2
% 2.77/1.45  
% 2.77/1.45  #Partial instantiations: 0
% 2.77/1.45  #Strategies tried      : 1
% 2.77/1.45  
% 2.77/1.45  Timing (in seconds)
% 2.77/1.45  ----------------------
% 2.77/1.45  Preprocessing        : 0.27
% 2.77/1.45  Parsing              : 0.14
% 2.77/1.45  CNF conversion       : 0.01
% 2.77/1.45  Main loop            : 0.43
% 2.77/1.45  Inferencing          : 0.15
% 2.77/1.45  Reduction            : 0.18
% 2.77/1.45  Demodulation         : 0.15
% 2.77/1.45  BG Simplification    : 0.02
% 2.77/1.45  Subsumption          : 0.06
% 2.77/1.45  Abstraction          : 0.03
% 2.77/1.45  MUC search           : 0.00
% 2.77/1.45  Cooper               : 0.00
% 2.77/1.45  Total                : 0.72
% 2.77/1.45  Index Insertion      : 0.00
% 2.77/1.45  Index Deletion       : 0.00
% 2.77/1.45  Index Matching       : 0.00
% 2.77/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

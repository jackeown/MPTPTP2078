%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:08 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  22 expanded)
%              Number of equality atoms :   16 (  21 expanded)
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_339,plain,(
    ! [B_37,A_38,C_39,D_40] : k2_xboole_0(k2_tarski(B_37,A_38),k2_tarski(C_39,D_40)) = k2_enumset1(A_38,B_37,C_39,D_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_351,plain,(
    ! [B_4,A_3,C_5,D_6] : k2_enumset1(B_4,A_3,C_5,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_339])).

tff(c_78,plain,(
    ! [A_21,C_22,D_23,B_24] : k2_enumset1(A_21,C_22,D_23,B_24) = k2_enumset1(A_21,B_24,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_21,B_24,D_23,C_22] : k2_enumset1(A_21,B_24,D_23,C_22) = k2_enumset1(A_21,B_24,C_22,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_233,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_11])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.37  
% 2.43/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.37  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.43/1.37  
% 2.43/1.37  %Foreground sorts:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Background operators:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Foreground operators:
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.37  
% 2.43/1.38  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.43/1.38  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.43/1.38  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.43/1.38  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.43/1.38  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.43/1.38  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.43/1.38  tff(c_212, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.38  tff(c_339, plain, (![B_37, A_38, C_39, D_40]: (k2_xboole_0(k2_tarski(B_37, A_38), k2_tarski(C_39, D_40))=k2_enumset1(A_38, B_37, C_39, D_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_212])).
% 2.43/1.38  tff(c_351, plain, (![B_4, A_3, C_5, D_6]: (k2_enumset1(B_4, A_3, C_5, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_339])).
% 2.43/1.38  tff(c_78, plain, (![A_21, C_22, D_23, B_24]: (k2_enumset1(A_21, C_22, D_23, B_24)=k2_enumset1(A_21, B_24, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.38  tff(c_8, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.38  tff(c_102, plain, (![A_21, B_24, D_23, C_22]: (k2_enumset1(A_21, B_24, D_23, C_22)=k2_enumset1(A_21, B_24, C_22, D_23))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 2.43/1.38  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.43/1.38  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 2.43/1.38  tff(c_233, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_11])).
% 2.43/1.38  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_351, c_233])).
% 2.43/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  Inference rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Ref     : 0
% 2.43/1.38  #Sup     : 102
% 2.43/1.38  #Fact    : 0
% 2.43/1.38  #Define  : 0
% 2.43/1.38  #Split   : 0
% 2.43/1.38  #Chain   : 0
% 2.43/1.38  #Close   : 0
% 2.43/1.38  
% 2.43/1.38  Ordering : KBO
% 2.43/1.38  
% 2.43/1.38  Simplification rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Subsume      : 49
% 2.43/1.38  #Demod        : 6
% 2.43/1.38  #Tautology    : 42
% 2.43/1.38  #SimpNegUnit  : 0
% 2.43/1.38  #BackRed      : 2
% 2.43/1.38  
% 2.43/1.38  #Partial instantiations: 0
% 2.43/1.38  #Strategies tried      : 1
% 2.43/1.38  
% 2.43/1.38  Timing (in seconds)
% 2.43/1.38  ----------------------
% 2.43/1.38  Preprocessing        : 0.29
% 2.43/1.38  Parsing              : 0.16
% 2.43/1.38  CNF conversion       : 0.02
% 2.43/1.38  Main loop            : 0.25
% 2.43/1.38  Inferencing          : 0.09
% 2.43/1.38  Reduction            : 0.11
% 2.43/1.38  Demodulation         : 0.09
% 2.43/1.38  BG Simplification    : 0.01
% 2.43/1.38  Subsumption          : 0.04
% 2.43/1.38  Abstraction          : 0.01
% 2.43/1.38  MUC search           : 0.00
% 2.43/1.38  Cooper               : 0.00
% 2.43/1.38  Total                : 0.57
% 2.43/1.38  Index Insertion      : 0.00
% 2.43/1.38  Index Deletion       : 0.00
% 2.43/1.38  Index Matching       : 0.00
% 2.43/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

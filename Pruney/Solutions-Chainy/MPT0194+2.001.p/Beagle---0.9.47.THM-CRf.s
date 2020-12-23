%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:58 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   29 (  48 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  38 expanded)
%              Number of equality atoms :   18 (  37 expanded)
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

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_78,plain,(
    ! [A_21,C_22,D_23,B_24] : k2_enumset1(A_21,C_22,D_23,B_24) = k2_enumset1(A_21,B_24,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_21,B_24,D_23,C_22] : k2_enumset1(A_21,B_24,D_23,C_22) = k2_enumset1(A_21,B_24,C_22,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

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

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_233,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_11])).

tff(c_368,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_351,c_233])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_6,c_8,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:52:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.26  
% 2.17/1.27  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.17/1.27  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.17/1.27  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.17/1.27  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.27  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.17/1.27  tff(c_78, plain, (![A_21, C_22, D_23, B_24]: (k2_enumset1(A_21, C_22, D_23, B_24)=k2_enumset1(A_21, B_24, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_8, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.27  tff(c_102, plain, (![A_21, B_24, D_23, C_22]: (k2_enumset1(A_21, B_24, D_23, C_22)=k2_enumset1(A_21, B_24, C_22, D_23))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 2.17/1.27  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.27  tff(c_212, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.27  tff(c_339, plain, (![B_37, A_38, C_39, D_40]: (k2_xboole_0(k2_tarski(B_37, A_38), k2_tarski(C_39, D_40))=k2_enumset1(A_38, B_37, C_39, D_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_212])).
% 2.17/1.27  tff(c_351, plain, (![B_4, A_3, C_5, D_6]: (k2_enumset1(B_4, A_3, C_5, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_339])).
% 2.17/1.27  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.27  tff(c_11, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.17/1.27  tff(c_233, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_11])).
% 2.17/1.27  tff(c_368, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_351, c_233])).
% 2.17/1.27  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_6, c_8, c_368])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 102
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 0
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 49
% 2.17/1.28  #Demod        : 9
% 2.17/1.28  #Tautology    : 42
% 2.17/1.28  #SimpNegUnit  : 0
% 2.17/1.28  #BackRed      : 2
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.26
% 2.17/1.28  Parsing              : 0.14
% 2.17/1.28  CNF conversion       : 0.01
% 2.17/1.28  Main loop            : 0.24
% 2.17/1.28  Inferencing          : 0.08
% 2.17/1.28  Reduction            : 0.10
% 2.17/1.28  Demodulation         : 0.09
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.03
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.52
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

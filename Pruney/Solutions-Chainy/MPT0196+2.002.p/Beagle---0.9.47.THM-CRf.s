%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:01 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  51 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  41 expanded)
%              Number of equality atoms :   19 (  40 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_21,D_22,C_23,B_24] : k2_enumset1(A_21,D_22,C_23,B_24) = k2_enumset1(A_21,B_24,C_23,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_7,B_8,D_10,C_9] : k2_enumset1(A_7,B_8,D_10,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_340,plain,(
    ! [A_37,B_38,C_39,D_40] : k2_xboole_0(k2_tarski(A_37,B_38),k2_tarski(C_39,D_40)) = k2_enumset1(B_38,A_37,C_39,D_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_352,plain,(
    ! [B_4,A_3,C_5,D_6] : k2_enumset1(B_4,A_3,C_5,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_340])).

tff(c_8,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_4','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_132,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_12])).

tff(c_369,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_132])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_6,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.24  
% 2.24/1.24  %Foreground sorts:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Background operators:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Foreground operators:
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.24  
% 2.24/1.25  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.24/1.25  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.24/1.25  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.24/1.25  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.25  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 2.24/1.25  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.25  tff(c_75, plain, (![A_21, D_22, C_23, B_24]: (k2_enumset1(A_21, D_22, C_23, B_24)=k2_enumset1(A_21, B_24, C_23, D_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.25  tff(c_123, plain, (![A_7, B_8, D_10, C_9]: (k2_enumset1(A_7, B_8, D_10, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 2.24/1.25  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.25  tff(c_214, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.25  tff(c_340, plain, (![A_37, B_38, C_39, D_40]: (k2_xboole_0(k2_tarski(A_37, B_38), k2_tarski(C_39, D_40))=k2_enumset1(B_38, A_37, C_39, D_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 2.24/1.25  tff(c_352, plain, (![B_4, A_3, C_5, D_6]: (k2_enumset1(B_4, A_3, C_5, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_340])).
% 2.24/1.25  tff(c_8, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.25  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.24/1.25  tff(c_11, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 2.24/1.25  tff(c_12, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11])).
% 2.24/1.25  tff(c_132, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_12])).
% 2.24/1.25  tff(c_369, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_352, c_132])).
% 2.24/1.25  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_6, c_369])).
% 2.24/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  Inference rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Ref     : 0
% 2.24/1.25  #Sup     : 102
% 2.24/1.25  #Fact    : 0
% 2.24/1.25  #Define  : 0
% 2.24/1.25  #Split   : 0
% 2.24/1.25  #Chain   : 0
% 2.24/1.25  #Close   : 0
% 2.24/1.25  
% 2.24/1.25  Ordering : KBO
% 2.24/1.25  
% 2.24/1.25  Simplification rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Subsume      : 49
% 2.24/1.25  #Demod        : 10
% 2.24/1.25  #Tautology    : 42
% 2.24/1.25  #SimpNegUnit  : 0
% 2.24/1.25  #BackRed      : 2
% 2.24/1.25  
% 2.24/1.25  #Partial instantiations: 0
% 2.24/1.25  #Strategies tried      : 1
% 2.24/1.25  
% 2.24/1.25  Timing (in seconds)
% 2.24/1.25  ----------------------
% 2.24/1.25  Preprocessing        : 0.26
% 2.24/1.25  Parsing              : 0.14
% 2.24/1.25  CNF conversion       : 0.01
% 2.24/1.25  Main loop            : 0.23
% 2.24/1.25  Inferencing          : 0.08
% 2.24/1.25  Reduction            : 0.10
% 2.24/1.25  Demodulation         : 0.09
% 2.24/1.25  BG Simplification    : 0.01
% 2.24/1.25  Subsumption          : 0.03
% 2.24/1.25  Abstraction          : 0.01
% 2.24/1.25  MUC search           : 0.00
% 2.24/1.25  Cooper               : 0.00
% 2.24/1.25  Total                : 0.51
% 2.24/1.25  Index Insertion      : 0.00
% 2.24/1.25  Index Deletion       : 0.00
% 2.24/1.25  Index Matching       : 0.00
% 2.24/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

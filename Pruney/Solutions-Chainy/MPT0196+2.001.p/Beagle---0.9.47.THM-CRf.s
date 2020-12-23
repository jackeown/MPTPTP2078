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
% DateTime   : Thu Dec  3 09:47:01 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   30 (  65 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   19 (  54 expanded)
%              Number of equality atoms :   18 (  53 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_4,plain,(
    ! [C_5,B_4,A_3,D_6] : k2_enumset1(C_5,B_4,A_3,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,(
    ! [A_41,B_42,B_43,A_44] : k2_xboole_0(k2_tarski(A_41,B_42),k2_tarski(B_43,A_44)) = k2_enumset1(A_41,B_42,A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_396,plain,(
    ! [A_7,B_8,D_10,C_9] : k2_enumset1(A_7,B_8,D_10,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_378])).

tff(c_108,plain,(
    ! [B_25,A_26,C_27,D_28] : k2_xboole_0(k2_tarski(B_25,A_26),k2_tarski(C_27,D_28)) = k2_enumset1(A_26,B_25,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_137,plain,(
    ! [B_29,A_30,C_31,D_32] : k2_enumset1(B_29,A_30,C_31,D_32) = k2_enumset1(A_30,B_29,C_31,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_194,plain,(
    ! [C_33,B_34,A_35,D_36] : k2_enumset1(C_33,B_34,A_35,D_36) = k2_enumset1(B_34,A_35,C_33,D_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_266,plain,(
    ! [A_3,C_5,B_4,D_6] : k2_enumset1(A_3,C_5,B_4,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_272,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_11])).

tff(c_542,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_396,c_272])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.70  
% 2.89/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.70  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.70  
% 2.89/1.70  %Foreground sorts:
% 2.89/1.70  
% 2.89/1.70  
% 2.89/1.70  %Background operators:
% 2.89/1.70  
% 2.89/1.70  
% 2.89/1.70  %Foreground operators:
% 2.89/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.70  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.70  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.70  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.70  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.70  
% 2.89/1.72  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l129_enumset1)).
% 2.89/1.72  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.89/1.72  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.89/1.72  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 2.89/1.72  tff(c_4, plain, (![C_5, B_4, A_3, D_6]: (k2_enumset1(C_5, B_4, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.72  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.72  tff(c_87, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.72  tff(c_378, plain, (![A_41, B_42, B_43, A_44]: (k2_xboole_0(k2_tarski(A_41, B_42), k2_tarski(B_43, A_44))=k2_enumset1(A_41, B_42, A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.89/1.72  tff(c_396, plain, (![A_7, B_8, D_10, C_9]: (k2_enumset1(A_7, B_8, D_10, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(superposition, [status(thm), theory('equality')], [c_6, c_378])).
% 2.89/1.72  tff(c_108, plain, (![B_25, A_26, C_27, D_28]: (k2_xboole_0(k2_tarski(B_25, A_26), k2_tarski(C_27, D_28))=k2_enumset1(A_26, B_25, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.89/1.72  tff(c_137, plain, (![B_29, A_30, C_31, D_32]: (k2_enumset1(B_29, A_30, C_31, D_32)=k2_enumset1(A_30, B_29, C_31, D_32))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6])).
% 2.89/1.72  tff(c_194, plain, (![C_33, B_34, A_35, D_36]: (k2_enumset1(C_33, B_34, A_35, D_36)=k2_enumset1(B_34, A_35, C_33, D_36))), inference(superposition, [status(thm), theory('equality')], [c_137, c_4])).
% 2.89/1.72  tff(c_266, plain, (![A_3, C_5, B_4, D_6]: (k2_enumset1(A_3, C_5, B_4, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_194])).
% 2.89/1.72  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.89/1.72  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 2.89/1.72  tff(c_272, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_11])).
% 2.89/1.72  tff(c_542, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_396, c_272])).
% 2.89/1.72  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_542])).
% 2.89/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.72  
% 2.89/1.72  Inference rules
% 2.89/1.72  ----------------------
% 2.89/1.72  #Ref     : 0
% 2.89/1.72  #Sup     : 154
% 2.89/1.72  #Fact    : 0
% 2.89/1.72  #Define  : 0
% 2.89/1.72  #Split   : 0
% 2.89/1.72  #Chain   : 0
% 2.89/1.72  #Close   : 0
% 2.89/1.72  
% 2.89/1.72  Ordering : KBO
% 2.89/1.72  
% 2.89/1.72  Simplification rules
% 2.89/1.72  ----------------------
% 2.89/1.72  #Subsume      : 50
% 2.89/1.72  #Demod        : 11
% 2.89/1.72  #Tautology    : 57
% 2.89/1.72  #SimpNegUnit  : 0
% 2.89/1.72  #BackRed      : 2
% 2.89/1.72  
% 2.89/1.72  #Partial instantiations: 0
% 2.89/1.72  #Strategies tried      : 1
% 2.89/1.72  
% 2.89/1.72  Timing (in seconds)
% 2.89/1.72  ----------------------
% 2.89/1.72  Preprocessing        : 0.43
% 2.89/1.72  Parsing              : 0.21
% 2.89/1.72  CNF conversion       : 0.02
% 2.89/1.72  Main loop            : 0.47
% 2.89/1.72  Inferencing          : 0.16
% 2.89/1.72  Reduction            : 0.20
% 2.89/1.72  Demodulation         : 0.18
% 2.89/1.72  BG Simplification    : 0.02
% 2.89/1.72  Subsumption          : 0.07
% 2.89/1.72  Abstraction          : 0.02
% 2.89/1.72  MUC search           : 0.00
% 2.89/1.72  Cooper               : 0.00
% 2.89/1.72  Total                : 0.94
% 2.89/1.72  Index Insertion      : 0.00
% 2.89/1.72  Index Deletion       : 0.00
% 2.89/1.72  Index Matching       : 0.00
% 2.89/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

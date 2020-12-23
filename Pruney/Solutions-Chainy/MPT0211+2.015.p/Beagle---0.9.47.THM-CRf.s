%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    3
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_32,plain,(
    ! [A_59,B_60,C_61] : k2_enumset1(A_59,A_59,B_60,C_61) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_16,C_18,D_19,B_17] : k2_enumset1(A_16,C_18,D_19,B_17) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_20,D_23,C_22,B_21] : k2_enumset1(A_20,D_23,C_22,B_21) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_25,D_27,C_26,A_24] : k2_enumset1(B_25,D_27,C_26,A_24) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [D_31,C_30,B_29,A_28] : k2_enumset1(D_31,C_30,B_29,A_28) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12,c_14,c_16,c_18,c_12,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.13  
% 1.90/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.13  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.90/1.13  
% 1.90/1.13  %Foreground sorts:
% 1.90/1.13  
% 1.90/1.13  
% 1.90/1.13  %Background operators:
% 1.90/1.13  
% 1.90/1.13  
% 1.90/1.13  %Foreground operators:
% 1.90/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.13  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.13  
% 1.90/1.14  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.90/1.14  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 1.90/1.14  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 1.90/1.14  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 1.90/1.14  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 1.90/1.14  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.90/1.14  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 1.90/1.14  tff(c_32, plain, (![A_59, B_60, C_61]: (k2_enumset1(A_59, A_59, B_60, C_61)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.14  tff(c_12, plain, (![A_16, C_18, D_19, B_17]: (k2_enumset1(A_16, C_18, D_19, B_17)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.14  tff(c_14, plain, (![A_20, D_23, C_22, B_21]: (k2_enumset1(A_20, D_23, C_22, B_21)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.14  tff(c_16, plain, (![B_25, D_27, C_26, A_24]: (k2_enumset1(B_25, D_27, C_26, A_24)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.14  tff(c_18, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.14  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.14  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.14  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 1.90/1.14  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_12, c_14, c_16, c_18, c_12, c_37])).
% 1.90/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.14  
% 1.90/1.14  Inference rules
% 1.90/1.14  ----------------------
% 1.90/1.14  #Ref     : 0
% 1.90/1.14  #Sup     : 0
% 1.90/1.14  #Fact    : 0
% 1.90/1.14  #Define  : 0
% 1.90/1.14  #Split   : 0
% 1.90/1.14  #Chain   : 0
% 1.90/1.14  #Close   : 0
% 1.90/1.14  
% 1.90/1.14  Ordering : KBO
% 1.90/1.14  
% 1.90/1.14  Simplification rules
% 1.90/1.14  ----------------------
% 1.90/1.14  #Subsume      : 17
% 1.90/1.14  #Demod        : 7
% 1.90/1.14  #Tautology    : 0
% 1.90/1.14  #SimpNegUnit  : 0
% 1.90/1.14  #BackRed      : 0
% 1.90/1.14  
% 1.90/1.14  #Partial instantiations: 0
% 1.90/1.14  #Strategies tried      : 1
% 1.90/1.14  
% 1.90/1.14  Timing (in seconds)
% 1.90/1.14  ----------------------
% 1.90/1.15  Preprocessing        : 0.32
% 1.90/1.15  Parsing              : 0.17
% 1.90/1.15  CNF conversion       : 0.02
% 1.90/1.15  Main loop            : 0.05
% 1.90/1.15  Inferencing          : 0.00
% 1.90/1.15  Reduction            : 0.03
% 1.90/1.15  Demodulation         : 0.03
% 1.90/1.15  BG Simplification    : 0.01
% 1.90/1.15  Subsumption          : 0.01
% 1.90/1.15  Abstraction          : 0.01
% 1.90/1.15  MUC search           : 0.00
% 1.90/1.15  Cooper               : 0.00
% 1.90/1.15  Total                : 0.39
% 1.90/1.15  Index Insertion      : 0.00
% 1.90/1.15  Index Deletion       : 0.00
% 1.90/1.15  Index Matching       : 0.00
% 1.90/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

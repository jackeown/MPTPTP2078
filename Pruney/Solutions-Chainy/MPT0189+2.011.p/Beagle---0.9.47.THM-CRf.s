%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [A_9,B_10,D_12,C_11] : k2_enumset1(A_9,B_10,D_12,C_11) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_13,D_16,C_15,B_14] : k2_enumset1(A_13,D_16,C_15,B_14) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_540,plain,(
    ! [A_97,B_98,C_99,D_100] : k2_xboole_0(k2_tarski(A_97,B_98),k2_tarski(C_99,D_100)) = k2_enumset1(A_97,B_98,C_99,D_100) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3153,plain,(
    ! [C_196,D_197,A_198,B_199] : k2_xboole_0(k2_tarski(C_196,D_197),k2_tarski(A_198,B_199)) = k2_enumset1(A_198,B_199,C_196,D_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_540])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3159,plain,(
    ! [C_196,D_197,A_198,B_199] : k2_enumset1(C_196,D_197,A_198,B_199) = k2_enumset1(A_198,B_199,C_196,D_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_3153,c_6])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_32])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_4390,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3159,c_34])).

tff(c_4393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_4390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.86  
% 4.66/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.86  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.66/1.86  
% 4.66/1.86  %Foreground sorts:
% 4.66/1.86  
% 4.66/1.86  
% 4.66/1.86  %Background operators:
% 4.66/1.86  
% 4.66/1.86  
% 4.66/1.86  %Foreground operators:
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.66/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.66/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.66/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.66/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.66/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.66/1.86  
% 4.85/1.87  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.85/1.87  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 4.85/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.85/1.87  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 4.85/1.87  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.85/1.87  tff(c_8, plain, (![A_9, B_10, D_12, C_11]: (k2_enumset1(A_9, B_10, D_12, C_11)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.85/1.87  tff(c_10, plain, (![A_13, D_16, C_15, B_14]: (k2_enumset1(A_13, D_16, C_15, B_14)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/1.87  tff(c_540, plain, (![A_97, B_98, C_99, D_100]: (k2_xboole_0(k2_tarski(A_97, B_98), k2_tarski(C_99, D_100))=k2_enumset1(A_97, B_98, C_99, D_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.87  tff(c_3153, plain, (![C_196, D_197, A_198, B_199]: (k2_xboole_0(k2_tarski(C_196, D_197), k2_tarski(A_198, B_199))=k2_enumset1(A_198, B_199, C_196, D_197))), inference(superposition, [status(thm), theory('equality')], [c_2, c_540])).
% 4.85/1.87  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.87  tff(c_3159, plain, (![C_196, D_197, A_198, B_199]: (k2_enumset1(C_196, D_197, A_198, B_199)=k2_enumset1(A_198, B_199, C_196, D_197))), inference(superposition, [status(thm), theory('equality')], [c_3153, c_6])).
% 4.85/1.87  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.85/1.87  tff(c_33, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_32])).
% 4.85/1.87  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_33])).
% 4.85/1.87  tff(c_4390, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3159, c_34])).
% 4.85/1.87  tff(c_4393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_4390])).
% 4.85/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.87  
% 4.85/1.87  Inference rules
% 4.85/1.87  ----------------------
% 4.85/1.87  #Ref     : 0
% 4.85/1.87  #Sup     : 1061
% 4.85/1.87  #Fact    : 0
% 4.85/1.87  #Define  : 0
% 4.85/1.87  #Split   : 0
% 4.85/1.87  #Chain   : 0
% 4.85/1.87  #Close   : 0
% 4.85/1.87  
% 4.85/1.87  Ordering : KBO
% 4.85/1.87  
% 4.85/1.87  Simplification rules
% 4.85/1.87  ----------------------
% 4.85/1.87  #Subsume      : 180
% 4.85/1.87  #Demod        : 856
% 4.85/1.87  #Tautology    : 693
% 4.85/1.87  #SimpNegUnit  : 0
% 4.85/1.87  #BackRed      : 6
% 4.85/1.87  
% 4.85/1.87  #Partial instantiations: 0
% 4.85/1.87  #Strategies tried      : 1
% 4.85/1.87  
% 4.85/1.87  Timing (in seconds)
% 4.85/1.87  ----------------------
% 4.85/1.87  Preprocessing        : 0.30
% 4.85/1.87  Parsing              : 0.16
% 4.85/1.87  CNF conversion       : 0.02
% 4.85/1.87  Main loop            : 0.81
% 4.85/1.87  Inferencing          : 0.26
% 4.85/1.87  Reduction            : 0.38
% 4.85/1.87  Demodulation         : 0.33
% 4.85/1.87  BG Simplification    : 0.03
% 4.85/1.87  Subsumption          : 0.10
% 4.85/1.87  Abstraction          : 0.04
% 4.85/1.87  MUC search           : 0.00
% 4.85/1.87  Cooper               : 0.00
% 4.85/1.87  Total                : 1.13
% 4.85/1.87  Index Insertion      : 0.00
% 4.85/1.87  Index Deletion       : 0.00
% 4.85/1.87  Index Matching       : 0.00
% 4.85/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

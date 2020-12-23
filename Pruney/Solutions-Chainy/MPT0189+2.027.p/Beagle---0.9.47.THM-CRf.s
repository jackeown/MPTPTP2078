%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:54 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   36 (  61 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  42 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [A_8,B_9,D_11,C_10] : k2_enumset1(A_8,B_9,D_11,C_10) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,C_14,D_15,B_13] : k2_enumset1(A_12,C_14,D_15,B_13) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_734,plain,(
    ! [A_120,B_121,C_122,D_123] : k2_xboole_0(k1_enumset1(A_120,B_121,C_122),k1_tarski(D_123)) = k2_enumset1(A_120,B_121,C_122,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1669,plain,(
    ! [B_198,C_199,A_200,D_201] : k2_xboole_0(k1_enumset1(B_198,C_199,A_200),k1_tarski(D_201)) = k2_enumset1(A_200,B_198,C_199,D_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_734])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1675,plain,(
    ! [B_198,C_199,A_200,D_201] : k2_enumset1(B_198,C_199,A_200,D_201) = k2_enumset1(A_200,B_198,C_199,D_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_12])).

tff(c_36,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_36])).

tff(c_38,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_37])).

tff(c_2235,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_1675,c_1675,c_38])).

tff(c_2238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_8,c_2235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.64  
% 3.81/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.64  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.81/1.64  
% 3.81/1.64  %Foreground sorts:
% 3.81/1.64  
% 3.81/1.64  
% 3.81/1.64  %Background operators:
% 3.81/1.64  
% 3.81/1.64  
% 3.81/1.64  %Foreground operators:
% 3.81/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.81/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.81/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.81/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.81/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.81/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.81/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.81/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.64  
% 3.81/1.65  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.81/1.65  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 3.81/1.65  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 3.81/1.65  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.81/1.65  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 3.81/1.65  tff(c_8, plain, (![A_8, B_9, D_11, C_10]: (k2_enumset1(A_8, B_9, D_11, C_10)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.65  tff(c_10, plain, (![A_12, C_14, D_15, B_13]: (k2_enumset1(A_12, C_14, D_15, B_13)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.65  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.65  tff(c_734, plain, (![A_120, B_121, C_122, D_123]: (k2_xboole_0(k1_enumset1(A_120, B_121, C_122), k1_tarski(D_123))=k2_enumset1(A_120, B_121, C_122, D_123))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.65  tff(c_1669, plain, (![B_198, C_199, A_200, D_201]: (k2_xboole_0(k1_enumset1(B_198, C_199, A_200), k1_tarski(D_201))=k2_enumset1(A_200, B_198, C_199, D_201))), inference(superposition, [status(thm), theory('equality')], [c_6, c_734])).
% 3.81/1.65  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.65  tff(c_1675, plain, (![B_198, C_199, A_200, D_201]: (k2_enumset1(B_198, C_199, A_200, D_201)=k2_enumset1(A_200, B_198, C_199, D_201))), inference(superposition, [status(thm), theory('equality')], [c_1669, c_12])).
% 3.81/1.65  tff(c_36, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.81/1.65  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_36])).
% 3.81/1.65  tff(c_38, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_37])).
% 3.81/1.65  tff(c_2235, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_1675, c_1675, c_38])).
% 3.81/1.65  tff(c_2238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_2235])).
% 3.81/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.65  
% 3.81/1.65  Inference rules
% 3.81/1.65  ----------------------
% 3.81/1.65  #Ref     : 0
% 3.81/1.65  #Sup     : 544
% 3.81/1.65  #Fact    : 0
% 3.81/1.65  #Define  : 0
% 3.81/1.65  #Split   : 0
% 3.81/1.65  #Chain   : 0
% 3.81/1.65  #Close   : 0
% 3.81/1.65  
% 3.81/1.65  Ordering : KBO
% 3.81/1.65  
% 3.81/1.65  Simplification rules
% 3.81/1.65  ----------------------
% 3.81/1.65  #Subsume      : 117
% 3.81/1.65  #Demod        : 334
% 3.81/1.65  #Tautology    : 347
% 3.81/1.65  #SimpNegUnit  : 0
% 3.81/1.65  #BackRed      : 1
% 3.81/1.65  
% 3.81/1.65  #Partial instantiations: 0
% 3.81/1.65  #Strategies tried      : 1
% 3.81/1.65  
% 3.81/1.65  Timing (in seconds)
% 3.81/1.65  ----------------------
% 3.81/1.65  Preprocessing        : 0.32
% 3.81/1.65  Parsing              : 0.17
% 3.81/1.65  CNF conversion       : 0.02
% 3.81/1.65  Main loop            : 0.56
% 3.81/1.65  Inferencing          : 0.19
% 3.81/1.65  Reduction            : 0.25
% 3.81/1.65  Demodulation         : 0.21
% 3.81/1.65  BG Simplification    : 0.03
% 3.81/1.65  Subsumption          : 0.07
% 3.81/1.65  Abstraction          : 0.03
% 3.81/1.65  MUC search           : 0.00
% 3.81/1.65  Cooper               : 0.00
% 3.81/1.65  Total                : 0.90
% 3.81/1.65  Index Insertion      : 0.00
% 3.81/1.65  Index Deletion       : 0.00
% 3.81/1.65  Index Matching       : 0.00
% 3.81/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

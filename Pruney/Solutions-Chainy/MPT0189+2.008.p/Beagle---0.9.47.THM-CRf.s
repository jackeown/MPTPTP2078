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
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  29 expanded)
%              Number of equality atoms :   17 (  28 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_15,C_17,B_16,D_18] : k2_enumset1(A_15,C_17,B_16,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,D_14,C_13] : k2_enumset1(A_11,B_12,D_14,C_13) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_515,plain,(
    ! [A_124,B_125,C_126,D_127] : k2_xboole_0(k2_tarski(A_124,B_125),k2_tarski(C_126,D_127)) = k2_enumset1(A_124,B_125,C_126,D_127) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1943,plain,(
    ! [C_222,D_223,A_224,B_225] : k2_xboole_0(k2_tarski(C_222,D_223),k2_tarski(A_224,B_225)) = k2_enumset1(A_224,B_225,C_222,D_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_2])).

tff(c_1961,plain,(
    ! [C_9,D_10,A_7,B_8] : k2_enumset1(C_9,D_10,A_7,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1943])).

tff(c_38,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_40,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_39])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_40])).

tff(c_1992,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1961,c_41])).

tff(c_1995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_1992])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:05:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.56  
% 3.49/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.56  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.56  
% 3.49/1.56  %Foreground sorts:
% 3.49/1.56  
% 3.49/1.56  
% 3.49/1.56  %Background operators:
% 3.49/1.56  
% 3.49/1.56  
% 3.49/1.56  %Foreground operators:
% 3.49/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.49/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.56  
% 3.64/1.57  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 3.64/1.57  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.64/1.57  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.64/1.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.64/1.57  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 3.64/1.57  tff(c_12, plain, (![A_15, C_17, B_16, D_18]: (k2_enumset1(A_15, C_17, B_16, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.57  tff(c_10, plain, (![A_11, B_12, D_14, C_13]: (k2_enumset1(A_11, B_12, D_14, C_13)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.57  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.57  tff(c_515, plain, (![A_124, B_125, C_126, D_127]: (k2_xboole_0(k2_tarski(A_124, B_125), k2_tarski(C_126, D_127))=k2_enumset1(A_124, B_125, C_126, D_127))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.64/1.57  tff(c_1943, plain, (![C_222, D_223, A_224, B_225]: (k2_xboole_0(k2_tarski(C_222, D_223), k2_tarski(A_224, B_225))=k2_enumset1(A_224, B_225, C_222, D_223))), inference(superposition, [status(thm), theory('equality')], [c_515, c_2])).
% 3.64/1.57  tff(c_1961, plain, (![C_9, D_10, A_7, B_8]: (k2_enumset1(C_9, D_10, A_7, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1943])).
% 3.64/1.57  tff(c_38, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.64/1.57  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 3.64/1.57  tff(c_40, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_39])).
% 3.64/1.57  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_40])).
% 3.64/1.57  tff(c_1992, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1961, c_41])).
% 3.64/1.57  tff(c_1995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_1992])).
% 3.64/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.57  
% 3.64/1.57  Inference rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Ref     : 0
% 3.64/1.57  #Sup     : 475
% 3.64/1.57  #Fact    : 0
% 3.64/1.57  #Define  : 0
% 3.64/1.57  #Split   : 0
% 3.64/1.57  #Chain   : 0
% 3.64/1.57  #Close   : 0
% 3.64/1.57  
% 3.64/1.57  Ordering : KBO
% 3.64/1.57  
% 3.64/1.57  Simplification rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Subsume      : 93
% 3.64/1.57  #Demod        : 300
% 3.64/1.57  #Tautology    : 325
% 3.64/1.57  #SimpNegUnit  : 0
% 3.64/1.57  #BackRed      : 1
% 3.64/1.57  
% 3.64/1.57  #Partial instantiations: 0
% 3.64/1.57  #Strategies tried      : 1
% 3.64/1.57  
% 3.64/1.57  Timing (in seconds)
% 3.64/1.57  ----------------------
% 3.64/1.57  Preprocessing        : 0.32
% 3.64/1.57  Parsing              : 0.17
% 3.64/1.57  CNF conversion       : 0.02
% 3.64/1.57  Main loop            : 0.50
% 3.64/1.57  Inferencing          : 0.18
% 3.64/1.57  Reduction            : 0.22
% 3.64/1.57  Demodulation         : 0.19
% 3.64/1.57  BG Simplification    : 0.03
% 3.64/1.57  Subsumption          : 0.06
% 3.64/1.57  Abstraction          : 0.03
% 3.64/1.57  MUC search           : 0.00
% 3.64/1.57  Cooper               : 0.00
% 3.64/1.57  Total                : 0.85
% 3.64/1.57  Index Insertion      : 0.00
% 3.64/1.57  Index Deletion       : 0.00
% 3.64/1.57  Index Matching       : 0.00
% 3.64/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

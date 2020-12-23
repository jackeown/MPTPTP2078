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
% DateTime   : Thu Dec  3 09:45:40 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k1_tarski(B_39),C_40)) = k2_xboole_0(k2_tarski(A_38,B_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_162,plain,(
    ! [A_38,A_9,B_10] : k2_xboole_0(k2_tarski(A_38,A_9),k1_tarski(B_10)) = k2_xboole_0(k1_tarski(A_38),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_167,plain,(
    ! [A_38,A_9,B_10] : k2_xboole_0(k2_tarski(A_38,A_9),k1_tarski(B_10)) = k1_enumset1(A_38,A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_162])).

tff(c_53,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k1_tarski(A_25),k2_tarski(B_26,C_27)) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_254,plain,(
    ! [A_51,B_52,C_53,C_54] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k2_tarski(B_52,C_53),C_54)) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_272,plain,(
    ! [A_51,A_38,A_9,B_10] : k2_xboole_0(k1_enumset1(A_51,A_38,A_9),k1_tarski(B_10)) = k2_xboole_0(k1_tarski(A_51),k1_enumset1(A_38,A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_254])).

tff(c_276,plain,(
    ! [A_51,A_38,A_9,B_10] : k2_xboole_0(k1_enumset1(A_51,A_38,A_9),k1_tarski(B_10)) = k2_enumset1(A_51,A_38,A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_272])).

tff(c_14,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.34  
% 2.21/1.35  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.21/1.35  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.21/1.35  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.21/1.35  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.21/1.35  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.21/1.35  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.35  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(B_12, C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.35  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.35  tff(c_33, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_xboole_0(A_22, B_23), C_24)=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.35  tff(c_138, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k1_tarski(B_39), C_40))=k2_xboole_0(k2_tarski(A_38, B_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.21/1.35  tff(c_162, plain, (![A_38, A_9, B_10]: (k2_xboole_0(k2_tarski(A_38, A_9), k1_tarski(B_10))=k2_xboole_0(k1_tarski(A_38), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 2.21/1.35  tff(c_167, plain, (![A_38, A_9, B_10]: (k2_xboole_0(k2_tarski(A_38, A_9), k1_tarski(B_10))=k1_enumset1(A_38, A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_162])).
% 2.21/1.35  tff(c_53, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k1_tarski(A_25), k2_tarski(B_26, C_27))=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.35  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.35  tff(c_254, plain, (![A_51, B_52, C_53, C_54]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k2_tarski(B_52, C_53), C_54))=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), C_54))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 2.21/1.35  tff(c_272, plain, (![A_51, A_38, A_9, B_10]: (k2_xboole_0(k1_enumset1(A_51, A_38, A_9), k1_tarski(B_10))=k2_xboole_0(k1_tarski(A_51), k1_enumset1(A_38, A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_254])).
% 2.21/1.35  tff(c_276, plain, (![A_51, A_38, A_9, B_10]: (k2_xboole_0(k1_enumset1(A_51, A_38, A_9), k1_tarski(B_10))=k2_enumset1(A_51, A_38, A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_272])).
% 2.21/1.35  tff(c_14, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.35  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_276, c_14])).
% 2.21/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  Inference rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Ref     : 0
% 2.21/1.35  #Sup     : 64
% 2.21/1.35  #Fact    : 0
% 2.21/1.35  #Define  : 0
% 2.21/1.35  #Split   : 0
% 2.21/1.35  #Chain   : 0
% 2.21/1.35  #Close   : 0
% 2.21/1.35  
% 2.21/1.35  Ordering : KBO
% 2.21/1.35  
% 2.21/1.35  Simplification rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Subsume      : 0
% 2.21/1.35  #Demod        : 50
% 2.21/1.35  #Tautology    : 35
% 2.21/1.35  #SimpNegUnit  : 0
% 2.21/1.35  #BackRed      : 1
% 2.21/1.35  
% 2.21/1.35  #Partial instantiations: 0
% 2.21/1.35  #Strategies tried      : 1
% 2.21/1.35  
% 2.21/1.35  Timing (in seconds)
% 2.21/1.35  ----------------------
% 2.21/1.35  Preprocessing        : 0.31
% 2.21/1.35  Parsing              : 0.17
% 2.21/1.35  CNF conversion       : 0.02
% 2.21/1.35  Main loop            : 0.24
% 2.21/1.35  Inferencing          : 0.10
% 2.21/1.35  Reduction            : 0.08
% 2.21/1.35  Demodulation         : 0.07
% 2.21/1.35  BG Simplification    : 0.01
% 2.21/1.36  Subsumption          : 0.03
% 2.21/1.36  Abstraction          : 0.02
% 2.21/1.36  MUC search           : 0.00
% 2.21/1.36  Cooper               : 0.00
% 2.21/1.36  Total                : 0.57
% 2.21/1.36  Index Insertion      : 0.00
% 2.21/1.36  Index Deletion       : 0.00
% 2.21/1.36  Index Matching       : 0.00
% 2.21/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------

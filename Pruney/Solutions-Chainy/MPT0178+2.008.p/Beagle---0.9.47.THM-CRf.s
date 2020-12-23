%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:37 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

tff(c_6,plain,(
    ! [A_10] : k1_enumset1(A_10,A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_enumset1(A_1,A_1,B_2,C_3) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_enumset1(A_11,A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k5_enumset1(A_4,A_4,B_5,C_6,D_7,E_8,F_9) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11])).

tff(c_13,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.35  
% 1.89/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.36  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1
% 1.89/1.36  
% 1.89/1.36  %Foreground sorts:
% 1.89/1.36  
% 1.89/1.36  
% 1.89/1.36  %Background operators:
% 1.89/1.36  
% 1.89/1.36  
% 1.89/1.36  %Foreground operators:
% 1.89/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.36  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.36  
% 1.89/1.38  tff(f_31, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 1.89/1.38  tff(f_27, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.89/1.38  tff(f_33, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.89/1.38  tff(f_29, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.89/1.38  tff(f_36, negated_conjecture, ~(![A]: (k5_enumset1(A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_enumset1)).
% 1.89/1.38  tff(c_6, plain, (![A_10]: (k1_enumset1(A_10, A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.38  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_enumset1(A_1, A_1, B_2, C_3)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.38  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k4_enumset1(A_11, A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.38  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k5_enumset1(A_4, A_4, B_5, C_6, D_7, E_8, F_9)=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.38  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.89/1.38  tff(c_11, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.89/1.38  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11])).
% 1.89/1.38  tff(c_13, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.89/1.38  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13])).
% 1.89/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.38  
% 1.89/1.38  Inference rules
% 1.89/1.38  ----------------------
% 1.89/1.38  #Ref     : 0
% 1.89/1.38  #Sup     : 0
% 1.89/1.38  #Fact    : 0
% 1.89/1.38  #Define  : 0
% 1.89/1.38  #Split   : 0
% 1.89/1.38  #Chain   : 0
% 1.89/1.38  #Close   : 0
% 1.89/1.38  
% 1.89/1.38  Ordering : KBO
% 1.89/1.38  
% 1.89/1.38  Simplification rules
% 1.89/1.38  ----------------------
% 1.89/1.38  #Subsume      : 4
% 1.89/1.38  #Demod        : 4
% 1.89/1.38  #Tautology    : 0
% 1.89/1.38  #SimpNegUnit  : 0
% 1.89/1.38  #BackRed      : 0
% 1.89/1.38  
% 1.89/1.38  #Partial instantiations: 0
% 1.89/1.38  #Strategies tried      : 1
% 1.89/1.38  
% 1.89/1.38  Timing (in seconds)
% 1.89/1.38  ----------------------
% 1.89/1.38  Preprocessing        : 0.41
% 1.89/1.38  Parsing              : 0.21
% 1.89/1.38  CNF conversion       : 0.02
% 1.89/1.38  Main loop            : 0.04
% 1.89/1.38  Inferencing          : 0.00
% 1.89/1.39  Reduction            : 0.03
% 1.89/1.39  Demodulation         : 0.02
% 1.89/1.39  BG Simplification    : 0.02
% 1.89/1.39  Subsumption          : 0.01
% 1.89/1.39  Abstraction          : 0.01
% 1.89/1.39  MUC search           : 0.00
% 1.89/1.39  Cooper               : 0.00
% 1.89/1.39  Total                : 0.50
% 1.89/1.39  Index Insertion      : 0.00
% 1.89/1.39  Index Deletion       : 0.00
% 1.89/1.39  Index Matching       : 0.00
% 1.89/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

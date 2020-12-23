%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:37 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
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
%$ k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k4_enumset1(A_10,A_10,A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k5_enumset1(A_4,A_4,B_5,C_6,D_7,E_8,F_9) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11])).

tff(c_13,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  %$ k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.61/1.08  
% 1.61/1.08  %Foreground sorts:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Background operators:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Foreground operators:
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.61/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.61/1.08  
% 1.61/1.09  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.61/1.09  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.61/1.09  tff(f_33, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 1.61/1.09  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.61/1.09  tff(f_36, negated_conjecture, ~(![A]: (k5_enumset1(A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_enumset1)).
% 1.61/1.09  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.09  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.09  tff(c_8, plain, (![A_10, B_11, C_12]: (k4_enumset1(A_10, A_10, A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.09  tff(c_6, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k5_enumset1(A_4, A_4, B_5, C_6, D_7, E_8, F_9)=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.09  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.09  tff(c_11, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.61/1.09  tff(c_12, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11])).
% 1.61/1.09  tff(c_13, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 1.61/1.09  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.61/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  Inference rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Ref     : 0
% 1.61/1.09  #Sup     : 0
% 1.61/1.09  #Fact    : 0
% 1.61/1.09  #Define  : 0
% 1.61/1.09  #Split   : 0
% 1.61/1.09  #Chain   : 0
% 1.61/1.09  #Close   : 0
% 1.61/1.09  
% 1.61/1.09  Ordering : KBO
% 1.61/1.09  
% 1.61/1.09  Simplification rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Subsume      : 4
% 1.61/1.09  #Demod        : 4
% 1.61/1.09  #Tautology    : 0
% 1.61/1.09  #SimpNegUnit  : 0
% 1.61/1.09  #BackRed      : 0
% 1.61/1.09  
% 1.61/1.09  #Partial instantiations: 0
% 1.61/1.09  #Strategies tried      : 1
% 1.61/1.09  
% 1.61/1.09  Timing (in seconds)
% 1.61/1.09  ----------------------
% 1.61/1.10  Preprocessing        : 0.31
% 1.61/1.10  Parsing              : 0.18
% 1.61/1.10  CNF conversion       : 0.01
% 1.61/1.10  Main loop            : 0.02
% 1.61/1.10  Inferencing          : 0.00
% 1.61/1.10  Reduction            : 0.02
% 1.61/1.10  Demodulation         : 0.01
% 1.61/1.10  BG Simplification    : 0.01
% 1.61/1.10  Subsumption          : 0.00
% 1.61/1.10  Abstraction          : 0.00
% 1.61/1.10  MUC search           : 0.00
% 1.61/1.10  Cooper               : 0.00
% 1.61/1.10  Total                : 0.36
% 1.61/1.10  Index Insertion      : 0.00
% 1.61/1.10  Index Deletion       : 0.00
% 1.61/1.10  Index Matching       : 0.00
% 1.61/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

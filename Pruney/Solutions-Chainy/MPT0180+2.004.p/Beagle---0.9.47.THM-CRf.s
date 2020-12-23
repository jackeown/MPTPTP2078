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
% DateTime   : Thu Dec  3 09:46:40 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,A_18,B_19,C_20,D_21,E_22) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k6_enumset1(A_11,A_11,B_12,C_13,D_14,E_15,F_16,G_17) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_16,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_15])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_18,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17])).

tff(c_19,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18])).

tff(c_21,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.40/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.11  
% 1.40/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.12  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.40/1.12  
% 1.40/1.12  %Foreground sorts:
% 1.40/1.12  
% 1.40/1.12  
% 1.40/1.12  %Background operators:
% 1.40/1.12  
% 1.40/1.12  
% 1.40/1.12  %Foreground operators:
% 1.40/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.40/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.40/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.40/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.40/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.40/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.40/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.40/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.40/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.40/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.40/1.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.40/1.12  
% 1.40/1.13  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.40/1.13  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.40/1.13  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.40/1.13  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.40/1.13  tff(f_37, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.40/1.13  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.40/1.13  tff(f_40, negated_conjecture, ~(![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_enumset1)).
% 1.40/1.13  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.40/1.13  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.40/1.13  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.40/1.13  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.40/1.13  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, A_18, B_19, C_20, D_21, E_22)=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.40/1.13  tff(c_10, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k6_enumset1(A_11, A_11, B_12, C_13, D_14, E_15, F_16, G_17)=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.40/1.13  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.40/1.13  tff(c_15, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 1.40/1.13  tff(c_16, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_15])).
% 1.40/1.13  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 1.40/1.13  tff(c_18, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_17])).
% 1.40/1.13  tff(c_19, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18])).
% 1.40/1.13  tff(c_21, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_19])).
% 1.40/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.13  
% 1.40/1.13  Inference rules
% 1.40/1.13  ----------------------
% 1.40/1.13  #Ref     : 0
% 1.40/1.13  #Sup     : 0
% 1.40/1.13  #Fact    : 0
% 1.40/1.13  #Define  : 0
% 1.40/1.13  #Split   : 0
% 1.40/1.13  #Chain   : 0
% 1.40/1.13  #Close   : 0
% 1.40/1.13  
% 1.40/1.13  Ordering : KBO
% 1.40/1.13  
% 1.40/1.13  Simplification rules
% 1.40/1.13  ----------------------
% 1.40/1.13  #Subsume      : 6
% 1.40/1.13  #Demod        : 6
% 1.40/1.13  #Tautology    : 0
% 1.40/1.13  #SimpNegUnit  : 0
% 1.40/1.13  #BackRed      : 0
% 1.40/1.13  
% 1.40/1.13  #Partial instantiations: 0
% 1.40/1.13  #Strategies tried      : 1
% 1.40/1.13  
% 1.40/1.13  Timing (in seconds)
% 1.40/1.13  ----------------------
% 1.40/1.13  Preprocessing        : 0.25
% 1.40/1.13  Parsing              : 0.13
% 1.40/1.13  CNF conversion       : 0.01
% 1.40/1.13  Main loop            : 0.03
% 1.40/1.13  Inferencing          : 0.00
% 1.40/1.13  Reduction            : 0.02
% 1.40/1.13  Demodulation         : 0.02
% 1.40/1.13  BG Simplification    : 0.01
% 1.40/1.13  Subsumption          : 0.01
% 1.40/1.13  Abstraction          : 0.00
% 1.40/1.13  MUC search           : 0.00
% 1.40/1.13  Cooper               : 0.00
% 1.40/1.13  Total                : 0.30
% 1.40/1.13  Index Insertion      : 0.00
% 1.40/1.13  Index Deletion       : 0.00
% 1.40/1.13  Index Matching       : 0.00
% 1.40/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

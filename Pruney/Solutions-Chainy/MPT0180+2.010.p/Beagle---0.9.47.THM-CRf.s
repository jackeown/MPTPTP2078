%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:41 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

tff(c_10,plain,(
    ! [A_21] : k1_enumset1(A_21,A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_enumset1(A_1,A_1,B_2,C_3) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24,D_25] : k4_enumset1(A_22,A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13] : k5_enumset1(A_8,A_8,B_9,C_10,D_11,E_12,F_13) = k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k6_enumset1(A_14,A_14,B_15,C_16,D_17,E_18,F_19,G_20) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_16,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_18,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17])).

tff(c_20,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:02:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  
% 1.69/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1
% 1.69/1.19  
% 1.69/1.19  %Foreground sorts:
% 1.69/1.19  
% 1.69/1.19  
% 1.69/1.19  %Background operators:
% 1.69/1.19  
% 1.69/1.19  
% 1.69/1.19  %Foreground operators:
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.19  
% 1.69/1.20  tff(f_35, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.69/1.20  tff(f_27, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.69/1.20  tff(f_37, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 1.69/1.20  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.69/1.20  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.69/1.20  tff(f_40, negated_conjecture, ~(![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 1.69/1.20  tff(c_10, plain, (![A_21]: (k1_enumset1(A_21, A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.20  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_enumset1(A_1, A_1, B_2, C_3)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.20  tff(c_12, plain, (![A_22, B_23, C_24, D_25]: (k4_enumset1(A_22, A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.20  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9, F_13]: (k5_enumset1(A_8, A_8, B_9, C_10, D_11, E_12, F_13)=k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.20  tff(c_8, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k6_enumset1(A_14, A_14, B_15, C_16, D_17, E_18, F_19, G_20)=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.20  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.69/1.20  tff(c_15, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.69/1.20  tff(c_16, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15])).
% 1.69/1.20  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 1.69/1.20  tff(c_18, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17])).
% 1.69/1.20  tff(c_20, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 1.69/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.20  
% 1.69/1.20  Inference rules
% 1.69/1.20  ----------------------
% 1.69/1.20  #Ref     : 0
% 1.69/1.20  #Sup     : 0
% 1.69/1.20  #Fact    : 0
% 1.69/1.20  #Define  : 0
% 1.69/1.20  #Split   : 0
% 1.69/1.20  #Chain   : 0
% 1.69/1.20  #Close   : 0
% 1.69/1.20  
% 1.69/1.20  Ordering : KBO
% 1.69/1.20  
% 1.69/1.20  Simplification rules
% 1.69/1.20  ----------------------
% 1.69/1.20  #Subsume      : 6
% 1.69/1.20  #Demod        : 5
% 1.69/1.20  #Tautology    : 0
% 1.69/1.20  #SimpNegUnit  : 0
% 1.69/1.20  #BackRed      : 0
% 1.69/1.20  
% 1.69/1.20  #Partial instantiations: 0
% 1.69/1.20  #Strategies tried      : 1
% 1.69/1.20  
% 1.69/1.20  Timing (in seconds)
% 1.69/1.20  ----------------------
% 1.69/1.20  Preprocessing        : 0.33
% 1.69/1.20  Parsing              : 0.18
% 1.69/1.20  CNF conversion       : 0.02
% 1.69/1.20  Main loop            : 0.03
% 1.69/1.20  Inferencing          : 0.00
% 1.69/1.20  Reduction            : 0.02
% 1.69/1.20  Demodulation         : 0.02
% 1.69/1.20  BG Simplification    : 0.01
% 1.69/1.20  Subsumption          : 0.01
% 1.69/1.20  Abstraction          : 0.00
% 1.69/1.20  MUC search           : 0.00
% 1.69/1.20  Cooper               : 0.00
% 1.69/1.20  Total                : 0.38
% 1.69/1.20  Index Insertion      : 0.00
% 1.69/1.20  Index Deletion       : 0.00
% 1.69/1.20  Index Matching       : 0.00
% 1.69/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:39 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
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
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23] : k3_enumset1(A_21,A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k4_enumset1(A_3,A_3,B_4,C_5,D_6,E_7) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13] : k5_enumset1(A_8,A_8,B_9,C_10,D_11,E_12,F_13) = k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k6_enumset1(A_14,A_14,B_15,C_16,D_17,E_18,F_19,G_20) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13])).

tff(c_15,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14])).

tff(c_16,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_15])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:37:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.64/1.09  
% 1.64/1.09  %Foreground sorts:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Background operators:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Foreground operators:
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.64/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.64/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.64/1.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.64/1.09  
% 1.64/1.10  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.64/1.10  tff(f_35, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.64/1.10  tff(f_29, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.64/1.10  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.64/1.10  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.64/1.10  tff(f_38, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_enumset1)).
% 1.64/1.10  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.10  tff(c_10, plain, (![A_21, B_22, C_23]: (k3_enumset1(A_21, A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.10  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k4_enumset1(A_3, A_3, B_4, C_5, D_6, E_7)=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.10  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9, F_13]: (k5_enumset1(A_8, A_8, B_9, C_10, D_11, E_12, F_13)=k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.10  tff(c_8, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k6_enumset1(A_14, A_14, B_15, C_16, D_17, E_18, F_19, G_20)=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.10  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.64/1.10  tff(c_13, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.64/1.10  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13])).
% 1.64/1.10  tff(c_15, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14])).
% 1.64/1.10  tff(c_16, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_15])).
% 1.64/1.10  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 0
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 0
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 5
% 1.64/1.10  #Demod        : 5
% 1.64/1.10  #Tautology    : 0
% 1.64/1.10  #SimpNegUnit  : 0
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.10  Preprocessing        : 0.27
% 1.64/1.10  Parsing              : 0.15
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.10  Main loop            : 0.03
% 1.64/1.10  Inferencing          : 0.00
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.02
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.01
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.33
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

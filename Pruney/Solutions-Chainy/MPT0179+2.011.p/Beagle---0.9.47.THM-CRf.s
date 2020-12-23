%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:39 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12] : k3_enumset1(A_10,A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k5_enumset1(A_13,A_13,A_13,B_14,C_15,D_16,E_17) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,G_9,E_7,B_4] : k6_enumset1(A_3,A_3,B_4,C_5,D_6,E_7,F_8,G_9) = k5_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_12,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_11])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.02  
% 1.54/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.02  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.54/1.02  
% 1.54/1.02  %Foreground sorts:
% 1.54/1.02  
% 1.54/1.02  
% 1.54/1.02  %Background operators:
% 1.54/1.02  
% 1.54/1.02  
% 1.54/1.02  %Foreground operators:
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.54/1.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.54/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.54/1.02  
% 1.54/1.03  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.54/1.03  tff(f_31, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.54/1.03  tff(f_33, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.54/1.03  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.54/1.03  tff(f_36, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_enumset1)).
% 1.54/1.03  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.03  tff(c_6, plain, (![A_10, B_11, C_12]: (k3_enumset1(A_10, A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.03  tff(c_8, plain, (![E_17, A_13, B_14, C_15, D_16]: (k5_enumset1(A_13, A_13, A_13, B_14, C_15, D_16, E_17)=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.54/1.03  tff(c_4, plain, (![A_3, F_8, D_6, C_5, G_9, E_7, B_4]: (k6_enumset1(A_3, A_3, B_4, C_5, D_6, E_7, F_8, G_9)=k5_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.03  tff(c_10, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.03  tff(c_11, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.54/1.03  tff(c_12, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_11])).
% 1.54/1.03  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.54/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.03  
% 1.54/1.03  Inference rules
% 1.54/1.03  ----------------------
% 1.54/1.03  #Ref     : 0
% 1.54/1.03  #Sup     : 0
% 1.54/1.03  #Fact    : 0
% 1.54/1.03  #Define  : 0
% 1.54/1.03  #Split   : 0
% 1.54/1.03  #Chain   : 0
% 1.54/1.03  #Close   : 0
% 1.54/1.03  
% 1.54/1.03  Ordering : KBO
% 1.54/1.03  
% 1.54/1.03  Simplification rules
% 1.54/1.03  ----------------------
% 1.54/1.03  #Subsume      : 4
% 1.54/1.03  #Demod        : 4
% 1.54/1.03  #Tautology    : 0
% 1.54/1.03  #SimpNegUnit  : 0
% 1.54/1.03  #BackRed      : 0
% 1.54/1.03  
% 1.54/1.03  #Partial instantiations: 0
% 1.54/1.03  #Strategies tried      : 1
% 1.54/1.03  
% 1.54/1.03  Timing (in seconds)
% 1.54/1.03  ----------------------
% 1.54/1.04  Preprocessing        : 0.25
% 1.54/1.04  Parsing              : 0.13
% 1.54/1.04  CNF conversion       : 0.01
% 1.54/1.04  Main loop            : 0.02
% 1.54/1.04  Inferencing          : 0.00
% 1.54/1.04  Reduction            : 0.02
% 1.54/1.04  Demodulation         : 0.01
% 1.54/1.04  BG Simplification    : 0.01
% 1.54/1.04  Subsumption          : 0.00
% 1.54/1.04  Abstraction          : 0.00
% 1.54/1.04  MUC search           : 0.00
% 1.54/1.04  Cooper               : 0.00
% 1.54/1.04  Total                : 0.30
% 1.54/1.04  Index Insertion      : 0.00
% 1.54/1.04  Index Deletion       : 0.00
% 1.54/1.04  Index Matching       : 0.00
% 1.54/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------

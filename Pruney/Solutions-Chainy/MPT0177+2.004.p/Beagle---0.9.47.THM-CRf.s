%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:36 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_enumset1(A_1,A_1,B_2,C_3) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k3_enumset1(A_4,A_4,B_5,C_6,D_7) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k4_enumset1(A_8,A_8,B_9,C_10,D_11,E_12) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k5_enumset1(A_13,A_13,B_14,C_15,D_16,E_17,F_18) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k6_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,F_24,G_25) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13])).

tff(c_15,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_15])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.06  
% 1.60/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.06  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.60/1.06  
% 1.60/1.06  %Foreground sorts:
% 1.60/1.06  
% 1.60/1.06  
% 1.60/1.06  %Background operators:
% 1.60/1.06  
% 1.60/1.06  
% 1.60/1.06  %Foreground operators:
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.60/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.60/1.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.60/1.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.60/1.06  
% 1.60/1.07  tff(f_27, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.60/1.07  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.60/1.07  tff(f_31, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.60/1.07  tff(f_33, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.60/1.07  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.60/1.07  tff(f_38, negated_conjecture, ~(![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_enumset1)).
% 1.60/1.07  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_enumset1(A_1, A_1, B_2, C_3)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.07  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k3_enumset1(A_4, A_4, B_5, C_6, D_7)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.07  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9]: (k4_enumset1(A_8, A_8, B_9, C_10, D_11, E_12)=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.07  tff(c_8, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k5_enumset1(A_13, A_13, B_14, C_15, D_16, E_17, F_18)=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.07  tff(c_10, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k6_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24, G_25)=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.07  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.07  tff(c_13, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.60/1.07  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13])).
% 1.60/1.07  tff(c_15, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.60/1.07  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_15])).
% 1.60/1.07  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.60/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  Inference rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Ref     : 0
% 1.60/1.07  #Sup     : 0
% 1.60/1.07  #Fact    : 0
% 1.60/1.07  #Define  : 0
% 1.60/1.07  #Split   : 0
% 1.60/1.07  #Chain   : 0
% 1.60/1.07  #Close   : 0
% 1.60/1.07  
% 1.60/1.07  Ordering : KBO
% 1.60/1.07  
% 1.60/1.07  Simplification rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Subsume      : 5
% 1.60/1.07  #Demod        : 5
% 1.60/1.07  #Tautology    : 0
% 1.60/1.07  #SimpNegUnit  : 0
% 1.60/1.07  #BackRed      : 0
% 1.60/1.07  
% 1.60/1.07  #Partial instantiations: 0
% 1.60/1.07  #Strategies tried      : 1
% 1.60/1.07  
% 1.60/1.07  Timing (in seconds)
% 1.60/1.07  ----------------------
% 1.60/1.08  Preprocessing        : 0.28
% 1.60/1.08  Parsing              : 0.14
% 1.60/1.08  CNF conversion       : 0.02
% 1.60/1.08  Main loop            : 0.03
% 1.60/1.08  Inferencing          : 0.00
% 1.60/1.08  Reduction            : 0.02
% 1.60/1.08  Demodulation         : 0.02
% 1.60/1.08  BG Simplification    : 0.01
% 1.60/1.08  Subsumption          : 0.01
% 1.60/1.08  Abstraction          : 0.00
% 1.60/1.08  MUC search           : 0.00
% 1.60/1.08  Cooper               : 0.00
% 1.60/1.08  Total                : 0.34
% 1.60/1.08  Index Insertion      : 0.00
% 1.60/1.08  Index Deletion       : 0.00
% 1.60/1.08  Index Matching       : 0.00
% 1.60/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

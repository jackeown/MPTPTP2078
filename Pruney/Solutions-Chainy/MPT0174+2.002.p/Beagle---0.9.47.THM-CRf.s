%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:32 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k6_enumset1(A,A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k3_enumset1(A_1,A_1,B_2,C_3,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k4_enumset1(A_5,A_5,B_6,C_7,D_8,E_9) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] : k5_enumset1(A_10,A_10,B_11,C_12,D_13,E_14,F_15) = k4_enumset1(A_10,B_11,C_12,D_13,E_14,F_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,G_22,E_20,F_21] : k6_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21,G_22) = k5_enumset1(A_16,B_17,C_18,D_19,E_20,F_21,G_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).

tff(c_13,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.73/1.19  
% 1.73/1.19  %Foreground sorts:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Background operators:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Foreground operators:
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.73/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.19  
% 1.73/1.20  tff(f_27, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.73/1.20  tff(f_29, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.73/1.20  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.73/1.20  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.73/1.20  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k6_enumset1(A, A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 1.73/1.20  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k3_enumset1(A_1, A_1, B_2, C_3, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.20  tff(c_4, plain, (![B_6, C_7, E_9, D_8, A_5]: (k4_enumset1(A_5, A_5, B_6, C_7, D_8, E_9)=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.20  tff(c_6, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (k5_enumset1(A_10, A_10, B_11, C_12, D_13, E_14, F_15)=k4_enumset1(A_10, B_11, C_12, D_13, E_14, F_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.20  tff(c_8, plain, (![C_18, B_17, A_16, D_19, G_22, E_20, F_21]: (k6_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21, G_22)=k5_enumset1(A_16, B_17, C_18, D_19, E_20, F_21, G_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.20  tff(c_10, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.20  tff(c_11, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.73/1.20  tff(c_12, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11])).
% 1.73/1.20  tff(c_13, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 1.73/1.20  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.73/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.20  
% 1.73/1.20  Inference rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Ref     : 0
% 1.73/1.20  #Sup     : 0
% 1.73/1.20  #Fact    : 0
% 1.73/1.20  #Define  : 0
% 1.73/1.20  #Split   : 0
% 1.73/1.20  #Chain   : 0
% 1.73/1.20  #Close   : 0
% 1.73/1.20  
% 1.73/1.20  Ordering : KBO
% 1.73/1.20  
% 1.73/1.20  Simplification rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Subsume      : 4
% 1.73/1.20  #Demod        : 4
% 1.73/1.20  #Tautology    : 0
% 1.73/1.20  #SimpNegUnit  : 0
% 1.73/1.20  #BackRed      : 0
% 1.73/1.20  
% 1.73/1.20  #Partial instantiations: 0
% 1.73/1.20  #Strategies tried      : 1
% 1.73/1.20  
% 1.73/1.20  Timing (in seconds)
% 1.73/1.20  ----------------------
% 1.73/1.20  Preprocessing        : 0.32
% 1.73/1.20  Parsing              : 0.15
% 1.73/1.20  CNF conversion       : 0.02
% 1.73/1.20  Main loop            : 0.03
% 1.73/1.20  Inferencing          : 0.00
% 1.73/1.20  Reduction            : 0.02
% 1.73/1.21  Demodulation         : 0.02
% 1.73/1.21  BG Simplification    : 0.01
% 1.73/1.21  Subsumption          : 0.01
% 1.73/1.21  Abstraction          : 0.00
% 1.73/1.21  MUC search           : 0.00
% 1.73/1.21  Cooper               : 0.00
% 1.73/1.21  Total                : 0.38
% 1.73/1.21  Index Insertion      : 0.00
% 1.73/1.21  Index Deletion       : 0.00
% 1.73/1.21  Index Matching       : 0.00
% 1.73/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:32 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k6_enumset1(A,A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k3_enumset1(A_1,A_1,B_2,C_3,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k5_enumset1(A_12,A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,G_11,F_10] : k6_enumset1(A_5,A_5,B_6,C_7,D_8,E_9,F_10,G_11) = k5_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_10,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:44:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.02  
% 1.57/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.03  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.57/1.03  
% 1.57/1.03  %Foreground sorts:
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  %Background operators:
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  %Foreground operators:
% 1.57/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.57/1.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.57/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.57/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.03  tff('#skF_4', type, '#skF_4': $i).
% 1.57/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.57/1.03  
% 1.57/1.04  tff(f_27, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.57/1.04  tff(f_31, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.57/1.04  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.57/1.04  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k6_enumset1(A, A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 1.57/1.04  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k3_enumset1(A_1, A_1, B_2, C_3, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.04  tff(c_6, plain, (![E_16, D_15, C_14, A_12, B_13]: (k5_enumset1(A_12, A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.04  tff(c_4, plain, (![B_6, C_7, E_9, D_8, A_5, G_11, F_10]: (k6_enumset1(A_5, A_5, B_6, C_7, D_8, E_9, F_10, G_11)=k5_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.04  tff(c_8, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.57/1.04  tff(c_9, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.57/1.04  tff(c_10, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.57/1.04  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.57/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.04  
% 1.57/1.04  Inference rules
% 1.57/1.04  ----------------------
% 1.57/1.04  #Ref     : 0
% 1.57/1.04  #Sup     : 0
% 1.57/1.04  #Fact    : 0
% 1.57/1.04  #Define  : 0
% 1.57/1.04  #Split   : 0
% 1.57/1.04  #Chain   : 0
% 1.57/1.04  #Close   : 0
% 1.57/1.04  
% 1.57/1.04  Ordering : KBO
% 1.57/1.04  
% 1.57/1.04  Simplification rules
% 1.57/1.04  ----------------------
% 1.57/1.04  #Subsume      : 3
% 1.57/1.04  #Demod        : 3
% 1.57/1.04  #Tautology    : 0
% 1.57/1.04  #SimpNegUnit  : 0
% 1.57/1.04  #BackRed      : 0
% 1.57/1.04  
% 1.57/1.04  #Partial instantiations: 0
% 1.57/1.04  #Strategies tried      : 1
% 1.57/1.04  
% 1.57/1.04  Timing (in seconds)
% 1.57/1.04  ----------------------
% 1.57/1.04  Preprocessing        : 0.26
% 1.57/1.04  Parsing              : 0.14
% 1.57/1.04  CNF conversion       : 0.01
% 1.57/1.04  Main loop            : 0.02
% 1.57/1.04  Inferencing          : 0.00
% 1.57/1.04  Reduction            : 0.02
% 1.57/1.04  Demodulation         : 0.01
% 1.57/1.04  BG Simplification    : 0.01
% 1.57/1.04  Subsumption          : 0.00
% 1.57/1.04  Abstraction          : 0.00
% 1.57/1.04  MUC search           : 0.00
% 1.57/1.04  Cooper               : 0.00
% 1.57/1.04  Total                : 0.31
% 1.57/1.04  Index Insertion      : 0.00
% 1.57/1.04  Index Deletion       : 0.00
% 1.57/1.04  Index Matching       : 0.00
% 1.57/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------

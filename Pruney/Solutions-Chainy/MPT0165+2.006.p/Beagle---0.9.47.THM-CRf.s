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
% DateTime   : Thu Dec  3 09:46:26 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k5_enumset1(A_1,A_1,B_2,C_3,D_4,E_5,F_6) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [G_13,D_10,A_7,F_12,B_8,E_11,C_9] : k6_enumset1(A_7,A_7,B_8,C_9,D_10,E_11,F_12,G_13) = k5_enumset1(A_7,B_8,C_9,D_10,E_11,F_12,G_13) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.01  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.48/1.01  
% 1.48/1.01  %Foreground sorts:
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  %Background operators:
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  %Foreground operators:
% 1.48/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.01  tff('#skF_5', type, '#skF_5': $i).
% 1.48/1.01  tff('#skF_6', type, '#skF_6': $i).
% 1.48/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.01  tff('#skF_3', type, '#skF_3': $i).
% 1.48/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.48/1.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.48/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.01  tff('#skF_4', type, '#skF_4': $i).
% 1.48/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.48/1.01  
% 1.48/1.02  tff(f_27, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.48/1.02  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.48/1.02  tff(f_32, negated_conjecture, ~(![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 1.48/1.02  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k5_enumset1(A_1, A_1, B_2, C_3, D_4, E_5, F_6)=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.02  tff(c_4, plain, (![G_13, D_10, A_7, F_12, B_8, E_11, C_9]: (k6_enumset1(A_7, A_7, B_8, C_9, D_10, E_11, F_12, G_13)=k5_enumset1(A_7, B_8, C_9, D_10, E_11, F_12, G_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.02  tff(c_6, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.48/1.02  tff(c_7, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.48/1.02  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.48/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.02  
% 1.48/1.02  Inference rules
% 1.48/1.02  ----------------------
% 1.48/1.02  #Ref     : 0
% 1.48/1.02  #Sup     : 0
% 1.48/1.02  #Fact    : 0
% 1.48/1.02  #Define  : 0
% 1.48/1.02  #Split   : 0
% 1.48/1.02  #Chain   : 0
% 1.48/1.02  #Close   : 0
% 1.48/1.02  
% 1.48/1.02  Ordering : KBO
% 1.48/1.02  
% 1.48/1.02  Simplification rules
% 1.48/1.02  ----------------------
% 1.48/1.02  #Subsume      : 2
% 1.48/1.02  #Demod        : 2
% 1.48/1.02  #Tautology    : 0
% 1.48/1.02  #SimpNegUnit  : 0
% 1.48/1.02  #BackRed      : 0
% 1.48/1.02  
% 1.48/1.02  #Partial instantiations: 0
% 1.48/1.02  #Strategies tried      : 1
% 1.48/1.02  
% 1.48/1.02  Timing (in seconds)
% 1.48/1.02  ----------------------
% 1.48/1.03  Preprocessing        : 0.25
% 1.48/1.03  Parsing              : 0.13
% 1.48/1.03  CNF conversion       : 0.01
% 1.48/1.03  Main loop            : 0.02
% 1.48/1.03  Inferencing          : 0.00
% 1.48/1.03  Reduction            : 0.01
% 1.48/1.03  Demodulation         : 0.01
% 1.48/1.03  BG Simplification    : 0.01
% 1.48/1.03  Subsumption          : 0.00
% 1.48/1.03  Abstraction          : 0.00
% 1.48/1.03  MUC search           : 0.00
% 1.48/1.03  Cooper               : 0.00
% 1.48/1.03  Total                : 0.30
% 1.48/1.03  Index Insertion      : 0.00
% 1.48/1.03  Index Deletion       : 0.00
% 1.48/1.03  Index Matching       : 0.00
% 1.48/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------

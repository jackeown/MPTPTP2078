%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:39 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k4_enumset1(A_9,A_9,A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] : k6_enumset1(A_3,A_3,A_3,B_4,C_5,D_6,E_7,F_8) = k4_enumset1(A_3,B_4,C_5,D_6,E_7,F_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_10,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  
% 1.48/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  %$ k6_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.48/1.08  
% 1.48/1.08  %Foreground sorts:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Background operators:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Foreground operators:
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.48/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.48/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.48/1.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.08  
% 1.48/1.09  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.48/1.09  tff(f_31, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 1.48/1.09  tff(f_29, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 1.48/1.09  tff(f_34, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 1.48/1.09  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.09  tff(c_6, plain, (![A_9, B_10, C_11]: (k4_enumset1(A_9, A_9, A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.48/1.09  tff(c_4, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (k6_enumset1(A_3, A_3, A_3, B_4, C_5, D_6, E_7, F_8)=k4_enumset1(A_3, B_4, C_5, D_6, E_7, F_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.09  tff(c_8, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.48/1.09  tff(c_9, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.48/1.09  tff(c_10, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.48/1.09  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.48/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.09  
% 1.48/1.09  Inference rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Ref     : 0
% 1.48/1.09  #Sup     : 0
% 1.48/1.09  #Fact    : 0
% 1.48/1.09  #Define  : 0
% 1.48/1.09  #Split   : 0
% 1.48/1.09  #Chain   : 0
% 1.48/1.09  #Close   : 0
% 1.48/1.09  
% 1.48/1.09  Ordering : KBO
% 1.48/1.09  
% 1.48/1.09  Simplification rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Subsume      : 3
% 1.48/1.09  #Demod        : 3
% 1.48/1.09  #Tautology    : 0
% 1.48/1.09  #SimpNegUnit  : 0
% 1.48/1.09  #BackRed      : 0
% 1.48/1.09  
% 1.48/1.09  #Partial instantiations: 0
% 1.48/1.09  #Strategies tried      : 1
% 1.48/1.09  
% 1.48/1.09  Timing (in seconds)
% 1.48/1.09  ----------------------
% 1.48/1.09  Preprocessing        : 0.24
% 1.48/1.09  Parsing              : 0.13
% 1.48/1.09  CNF conversion       : 0.01
% 1.48/1.09  Main loop            : 0.02
% 1.48/1.09  Inferencing          : 0.00
% 1.48/1.09  Reduction            : 0.01
% 1.48/1.09  Demodulation         : 0.01
% 1.48/1.09  BG Simplification    : 0.01
% 1.48/1.09  Subsumption          : 0.00
% 1.48/1.09  Abstraction          : 0.00
% 1.48/1.09  MUC search           : 0.00
% 1.48/1.09  Cooper               : 0.00
% 1.48/1.09  Total                : 0.29
% 1.48/1.09  Index Insertion      : 0.00
% 1.48/1.09  Index Deletion       : 0.00
% 1.48/1.09  Index Matching       : 0.00
% 1.48/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

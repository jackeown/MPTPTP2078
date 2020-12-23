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
% DateTime   : Thu Dec  3 09:46:31 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] : k3_enumset1(A_8,A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k4_enumset1(A_3,A_3,B_4,C_5,D_6,E_7) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_10,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n014.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 13:32:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  %$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.60/1.12  
% 1.60/1.12  %Foreground sorts:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Background operators:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Foreground operators:
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.60/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.12  
% 1.60/1.13  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.60/1.13  tff(f_31, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 1.60/1.13  tff(f_29, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.60/1.13  tff(f_34, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 1.60/1.13  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.13  tff(c_6, plain, (![A_8, B_9, C_10]: (k3_enumset1(A_8, A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.13  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k4_enumset1(A_3, A_3, B_4, C_5, D_6, E_7)=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.13  tff(c_8, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.13  tff(c_9, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.60/1.13  tff(c_10, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.60/1.13  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.60/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  Inference rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Ref     : 0
% 1.60/1.13  #Sup     : 0
% 1.60/1.13  #Fact    : 0
% 1.60/1.13  #Define  : 0
% 1.60/1.13  #Split   : 0
% 1.60/1.13  #Chain   : 0
% 1.60/1.13  #Close   : 0
% 1.60/1.13  
% 1.60/1.13  Ordering : KBO
% 1.60/1.13  
% 1.60/1.13  Simplification rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Subsume      : 3
% 1.60/1.13  #Demod        : 3
% 1.60/1.13  #Tautology    : 0
% 1.60/1.13  #SimpNegUnit  : 0
% 1.60/1.13  #BackRed      : 0
% 1.60/1.13  
% 1.60/1.13  #Partial instantiations: 0
% 1.60/1.13  #Strategies tried      : 1
% 1.60/1.13  
% 1.60/1.13  Timing (in seconds)
% 1.60/1.13  ----------------------
% 1.60/1.13  Preprocessing        : 0.28
% 1.60/1.13  Parsing              : 0.15
% 1.60/1.13  CNF conversion       : 0.02
% 1.60/1.13  Main loop            : 0.02
% 1.60/1.13  Inferencing          : 0.00
% 1.60/1.13  Reduction            : 0.02
% 1.60/1.13  Demodulation         : 0.01
% 1.60/1.13  BG Simplification    : 0.01
% 1.60/1.13  Subsumption          : 0.00
% 1.60/1.13  Abstraction          : 0.00
% 1.60/1.13  MUC search           : 0.00
% 1.60/1.13  Cooper               : 0.00
% 1.60/1.13  Total                : 0.33
% 1.60/1.13  Index Insertion      : 0.00
% 1.60/1.14  Index Deletion       : 0.00
% 1.60/1.14  Index Matching       : 0.00
% 1.60/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k3_mcart_1(A_4,B_5,C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_mcart_1(k4_tarski(A_8,B_9),C_10,C_3) = k4_tarski(k3_mcart_1(A_8,B_9,C_10),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7,c_2])).

tff(c_34,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_mcart_1(k4_tarski(A_8,B_9),C_10,C_3) = k4_mcart_1(A_8,B_9,C_10,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_6,plain,(
    k3_mcart_1(k4_tarski('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.59/1.13  
% 1.59/1.13  %Foreground sorts:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Background operators:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Foreground operators:
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.59/1.13  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.59/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.13  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.59/1.13  
% 1.69/1.14  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 1.69/1.14  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.69/1.14  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_mcart_1)).
% 1.69/1.14  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k4_tarski(k3_mcart_1(A_4, B_5, C_6), D_7)=k4_mcart_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.14  tff(c_7, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.14  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski(k4_tarski(A_1, B_2), C_3)=k3_mcart_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.14  tff(c_10, plain, (![A_8, B_9, C_10, C_3]: (k3_mcart_1(k4_tarski(A_8, B_9), C_10, C_3)=k4_tarski(k3_mcart_1(A_8, B_9, C_10), C_3))), inference(superposition, [status(thm), theory('equality')], [c_7, c_2])).
% 1.69/1.14  tff(c_34, plain, (![A_8, B_9, C_10, C_3]: (k3_mcart_1(k4_tarski(A_8, B_9), C_10, C_3)=k4_mcart_1(A_8, B_9, C_10, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.69/1.14  tff(c_6, plain, (k3_mcart_1(k4_tarski('#skF_1', '#skF_2'), '#skF_3', '#skF_4')!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.14  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 0
% 1.69/1.14  #Sup     : 7
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 0
% 1.69/1.14  #Demod        : 2
% 1.69/1.14  #Tautology    : 4
% 1.69/1.14  #SimpNegUnit  : 0
% 1.69/1.14  #BackRed      : 1
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.14  Preprocessing        : 0.26
% 1.69/1.14  Parsing              : 0.14
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.07
% 1.69/1.14  Inferencing          : 0.04
% 1.69/1.14  Reduction            : 0.02
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.01
% 1.69/1.14  Abstraction          : 0.00
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.35
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

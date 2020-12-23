%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  14 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

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

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k4_tarski(k4_tarski(A_4,B_5),C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7,plain,(
    ! [A_4,B_5,C_6,D_7] : k4_tarski(k3_mcart_1(A_4,B_5,C_6),D_7) = k4_mcart_1(A_4,B_5,C_6,D_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_17,plain,(
    ! [A_1,B_2,C_3,C_10] : k3_mcart_1(k4_tarski(A_1,B_2),C_3,C_10) = k4_tarski(k3_mcart_1(A_1,B_2,C_3),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_35,plain,(
    ! [A_1,B_2,C_3,C_10] : k3_mcart_1(k4_tarski(A_1,B_2),C_3,C_10) = k4_mcart_1(A_1,B_2,C_3,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7,c_17])).

tff(c_6,plain,(
    k3_mcart_1(k4_tarski('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.06  
% 1.53/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.06  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.53/1.06  
% 1.53/1.06  %Foreground sorts:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Background operators:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Foreground operators:
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.53/1.06  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.53/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.06  tff('#skF_4', type, '#skF_4': $i).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.06  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.53/1.06  
% 1.53/1.06  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.53/1.06  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 1.53/1.06  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_mcart_1)).
% 1.53/1.06  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski(k4_tarski(A_1, B_2), C_3)=k3_mcart_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.06  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k4_tarski(k4_tarski(k4_tarski(A_4, B_5), C_6), D_7)=k4_mcart_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.53/1.06  tff(c_7, plain, (![A_4, B_5, C_6, D_7]: (k4_tarski(k3_mcart_1(A_4, B_5, C_6), D_7)=k4_mcart_1(A_4, B_5, C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.53/1.06  tff(c_8, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.06  tff(c_17, plain, (![A_1, B_2, C_3, C_10]: (k3_mcart_1(k4_tarski(A_1, B_2), C_3, C_10)=k4_tarski(k3_mcart_1(A_1, B_2, C_3), C_10))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8])).
% 1.53/1.06  tff(c_35, plain, (![A_1, B_2, C_3, C_10]: (k3_mcart_1(k4_tarski(A_1, B_2), C_3, C_10)=k4_mcart_1(A_1, B_2, C_3, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_7, c_17])).
% 1.53/1.06  tff(c_6, plain, (k3_mcart_1(k4_tarski('#skF_1', '#skF_2'), '#skF_3', '#skF_4')!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.53/1.06  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_6])).
% 1.53/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.06  
% 1.53/1.06  Inference rules
% 1.53/1.06  ----------------------
% 1.53/1.06  #Ref     : 0
% 1.53/1.06  #Sup     : 7
% 1.53/1.06  #Fact    : 0
% 1.53/1.06  #Define  : 0
% 1.53/1.06  #Split   : 0
% 1.53/1.07  #Chain   : 0
% 1.53/1.07  #Close   : 0
% 1.53/1.07  
% 1.53/1.07  Ordering : KBO
% 1.53/1.07  
% 1.53/1.07  Simplification rules
% 1.53/1.07  ----------------------
% 1.53/1.07  #Subsume      : 0
% 1.53/1.07  #Demod        : 3
% 1.53/1.07  #Tautology    : 4
% 1.53/1.07  #SimpNegUnit  : 0
% 1.53/1.07  #BackRed      : 1
% 1.53/1.07  
% 1.53/1.07  #Partial instantiations: 0
% 1.53/1.07  #Strategies tried      : 1
% 1.53/1.07  
% 1.53/1.07  Timing (in seconds)
% 1.53/1.07  ----------------------
% 1.53/1.07  Preprocessing        : 0.23
% 1.53/1.07  Parsing              : 0.12
% 1.53/1.07  CNF conversion       : 0.01
% 1.53/1.07  Main loop            : 0.07
% 1.53/1.07  Inferencing          : 0.04
% 1.53/1.07  Reduction            : 0.02
% 1.53/1.07  Demodulation         : 0.02
% 1.53/1.07  BG Simplification    : 0.01
% 1.53/1.07  Subsumption          : 0.01
% 1.53/1.07  Abstraction          : 0.00
% 1.53/1.07  MUC search           : 0.00
% 1.53/1.07  Cooper               : 0.00
% 1.53/1.07  Total                : 0.32
% 1.53/1.07  Index Insertion      : 0.00
% 1.53/1.07  Index Deletion       : 0.00
% 1.53/1.07  Index Matching       : 0.00
% 1.53/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:30 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_enumset1(A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4,D_5] : k3_enumset1(A_2,A_2,B_3,C_4,D_5) = k2_enumset1(A_2,B_3,C_4,D_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_10,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.39/0.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/0.99  %$ k3_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.39/0.99  
% 1.39/0.99  %Foreground sorts:
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  %Background operators:
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  %Foreground operators:
% 1.39/0.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.39/0.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.39/0.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.39/0.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.39/0.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.39/0.99  tff('#skF_1', type, '#skF_1': $i).
% 1.39/0.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.39/0.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.39/0.99  
% 1.39/1.00  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.39/1.00  tff(f_31, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.39/1.00  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.39/1.00  tff(f_34, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 1.39/1.00  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.39/1.00  tff(c_6, plain, (![A_6, B_7]: (k2_enumset1(A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.39/1.00  tff(c_4, plain, (![A_2, B_3, C_4, D_5]: (k3_enumset1(A_2, A_2, B_3, C_4, D_5)=k2_enumset1(A_2, B_3, C_4, D_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.39/1.00  tff(c_8, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.39/1.00  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.39/1.00  tff(c_10, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.39/1.00  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.39/1.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.00  
% 1.39/1.00  Inference rules
% 1.39/1.00  ----------------------
% 1.39/1.00  #Ref     : 0
% 1.39/1.00  #Sup     : 0
% 1.39/1.00  #Fact    : 0
% 1.39/1.00  #Define  : 0
% 1.39/1.00  #Split   : 0
% 1.39/1.00  #Chain   : 0
% 1.39/1.00  #Close   : 0
% 1.39/1.00  
% 1.39/1.00  Ordering : KBO
% 1.39/1.00  
% 1.39/1.00  Simplification rules
% 1.39/1.00  ----------------------
% 1.39/1.00  #Subsume      : 3
% 1.39/1.00  #Demod        : 3
% 1.39/1.00  #Tautology    : 0
% 1.39/1.00  #SimpNegUnit  : 0
% 1.39/1.00  #BackRed      : 0
% 1.39/1.00  
% 1.39/1.00  #Partial instantiations: 0
% 1.39/1.00  #Strategies tried      : 1
% 1.39/1.00  
% 1.39/1.00  Timing (in seconds)
% 1.39/1.00  ----------------------
% 1.39/1.01  Preprocessing        : 0.24
% 1.39/1.01  Parsing              : 0.12
% 1.39/1.01  CNF conversion       : 0.01
% 1.39/1.01  Main loop            : 0.02
% 1.39/1.01  Inferencing          : 0.00
% 1.39/1.01  Reduction            : 0.01
% 1.39/1.01  Demodulation         : 0.01
% 1.39/1.01  BG Simplification    : 0.01
% 1.39/1.01  Subsumption          : 0.00
% 1.39/1.01  Abstraction          : 0.00
% 1.39/1.01  MUC search           : 0.00
% 1.39/1.01  Cooper               : 0.00
% 1.39/1.01  Total                : 0.28
% 1.39/1.01  Index Insertion      : 0.00
% 1.39/1.01  Index Deletion       : 0.00
% 1.39/1.01  Index Matching       : 0.00
% 1.39/1.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------

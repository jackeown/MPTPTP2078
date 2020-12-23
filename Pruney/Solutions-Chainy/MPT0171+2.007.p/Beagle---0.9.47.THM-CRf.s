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

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k3_enumset1(A_2,A_2,A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.03  
% 1.49/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.03  %$ k3_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.49/1.03  
% 1.49/1.03  %Foreground sorts:
% 1.49/1.03  
% 1.49/1.03  
% 1.49/1.03  %Background operators:
% 1.49/1.03  
% 1.49/1.03  
% 1.49/1.03  %Foreground operators:
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.49/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.49/1.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.49/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.03  
% 1.49/1.04  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.49/1.04  tff(f_29, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 1.49/1.04  tff(f_32, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 1.49/1.04  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.49/1.04  tff(c_4, plain, (![A_2, B_3]: (k3_enumset1(A_2, A_2, A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.04  tff(c_6, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.04  tff(c_7, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.49/1.04  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.49/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.04  
% 1.49/1.04  Inference rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Ref     : 0
% 1.49/1.04  #Sup     : 0
% 1.49/1.04  #Fact    : 0
% 1.49/1.04  #Define  : 0
% 1.49/1.04  #Split   : 0
% 1.49/1.04  #Chain   : 0
% 1.49/1.04  #Close   : 0
% 1.49/1.04  
% 1.49/1.04  Ordering : KBO
% 1.49/1.04  
% 1.49/1.04  Simplification rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Subsume      : 2
% 1.49/1.04  #Demod        : 2
% 1.49/1.04  #Tautology    : 0
% 1.49/1.04  #SimpNegUnit  : 0
% 1.49/1.04  #BackRed      : 0
% 1.49/1.04  
% 1.49/1.04  #Partial instantiations: 0
% 1.49/1.04  #Strategies tried      : 1
% 1.49/1.04  
% 1.49/1.04  Timing (in seconds)
% 1.49/1.04  ----------------------
% 1.49/1.04  Preprocessing        : 0.25
% 1.49/1.04  Parsing              : 0.13
% 1.49/1.04  CNF conversion       : 0.01
% 1.49/1.04  Main loop            : 0.02
% 1.49/1.04  Inferencing          : 0.00
% 1.49/1.04  Reduction            : 0.02
% 1.49/1.04  Demodulation         : 0.01
% 1.49/1.04  BG Simplification    : 0.01
% 1.49/1.04  Subsumption          : 0.01
% 1.49/1.04  Abstraction          : 0.00
% 1.49/1.05  MUC search           : 0.00
% 1.49/1.05  Cooper               : 0.00
% 1.49/1.05  Total                : 0.30
% 1.49/1.05  Index Insertion      : 0.00
% 1.49/1.05  Index Deletion       : 0.00
% 1.49/1.05  Index Matching       : 0.00
% 1.49/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:26 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_enumset1(A_2,A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.19  
% 1.68/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.19  %$ k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.68/1.19  
% 1.68/1.19  %Foreground sorts:
% 1.68/1.19  
% 1.68/1.19  
% 1.68/1.19  %Background operators:
% 1.68/1.19  
% 1.68/1.19  
% 1.68/1.19  %Foreground operators:
% 1.68/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.19  
% 1.68/1.20  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.68/1.20  tff(f_29, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.68/1.20  tff(f_32, negated_conjecture, ~(![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.68/1.20  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.20  tff(c_4, plain, (![A_2, B_3]: (k2_enumset1(A_2, A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.20  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.20  tff(c_7, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.68/1.20  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.68/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.20  
% 1.68/1.20  Inference rules
% 1.68/1.20  ----------------------
% 1.68/1.20  #Ref     : 0
% 1.68/1.20  #Sup     : 0
% 1.68/1.20  #Fact    : 0
% 1.68/1.20  #Define  : 0
% 1.68/1.20  #Split   : 0
% 1.68/1.20  #Chain   : 0
% 1.68/1.20  #Close   : 0
% 1.68/1.20  
% 1.68/1.20  Ordering : KBO
% 1.68/1.20  
% 1.68/1.20  Simplification rules
% 1.68/1.20  ----------------------
% 1.68/1.20  #Subsume      : 2
% 1.68/1.20  #Demod        : 2
% 1.68/1.20  #Tautology    : 0
% 1.68/1.20  #SimpNegUnit  : 0
% 1.68/1.20  #BackRed      : 0
% 1.68/1.20  
% 1.68/1.20  #Partial instantiations: 0
% 1.68/1.20  #Strategies tried      : 1
% 1.68/1.20  
% 1.68/1.20  Timing (in seconds)
% 1.68/1.20  ----------------------
% 1.68/1.20  Preprocessing        : 0.37
% 1.68/1.20  Parsing              : 0.21
% 1.68/1.20  CNF conversion       : 0.02
% 1.68/1.20  Main loop            : 0.02
% 1.68/1.20  Inferencing          : 0.00
% 1.68/1.20  Reduction            : 0.01
% 1.68/1.20  Demodulation         : 0.01
% 1.68/1.20  BG Simplification    : 0.01
% 1.68/1.20  Subsumption          : 0.00
% 1.68/1.20  Abstraction          : 0.00
% 1.68/1.20  MUC search           : 0.00
% 1.68/1.20  Cooper               : 0.00
% 1.68/1.20  Total                : 0.41
% 1.68/1.20  Index Insertion      : 0.00
% 1.68/1.21  Index Deletion       : 0.00
% 1.68/1.21  Index Matching       : 0.00
% 1.68/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

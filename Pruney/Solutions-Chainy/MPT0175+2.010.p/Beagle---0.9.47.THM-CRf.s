%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:34 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

tff(c_4,plain,(
    ! [A_4] : k1_enumset1(A_4,A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_enumset1(A_1,A_1,B_2,C_3) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k4_enumset1(A_5,A_5,A_5,B_6,C_7,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_10,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9])).

tff(c_12,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.37/1.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.37/1.01  
% 1.37/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.37/1.01  %$ k4_enumset1 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_1
% 1.37/1.01  
% 1.37/1.01  %Foreground sorts:
% 1.37/1.01  
% 1.37/1.01  
% 1.37/1.01  %Background operators:
% 1.37/1.01  
% 1.37/1.01  
% 1.37/1.01  %Foreground operators:
% 1.37/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.37/1.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.37/1.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.37/1.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.37/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.37/1.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.37/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.37/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.37/1.01  
% 1.37/1.02  tff(f_29, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.37/1.02  tff(f_27, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.37/1.02  tff(f_31, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 1.37/1.02  tff(f_34, negated_conjecture, ~(![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 1.37/1.02  tff(c_4, plain, (![A_4]: (k1_enumset1(A_4, A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.37/1.02  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_enumset1(A_1, A_1, B_2, C_3)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.37/1.02  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k4_enumset1(A_5, A_5, A_5, B_6, C_7, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.37/1.02  tff(c_8, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.37/1.02  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.37/1.02  tff(c_10, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9])).
% 1.37/1.02  tff(c_12, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.37/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.37/1.02  
% 1.37/1.02  Inference rules
% 1.37/1.02  ----------------------
% 1.37/1.02  #Ref     : 0
% 1.37/1.02  #Sup     : 0
% 1.37/1.02  #Fact    : 0
% 1.37/1.02  #Define  : 0
% 1.37/1.02  #Split   : 0
% 1.37/1.02  #Chain   : 0
% 1.37/1.02  #Close   : 0
% 1.37/1.02  
% 1.37/1.02  Ordering : KBO
% 1.37/1.02  
% 1.37/1.02  Simplification rules
% 1.37/1.02  ----------------------
% 1.37/1.02  #Subsume      : 3
% 1.37/1.02  #Demod        : 3
% 1.37/1.02  #Tautology    : 0
% 1.37/1.02  #SimpNegUnit  : 0
% 1.37/1.02  #BackRed      : 0
% 1.37/1.02  
% 1.37/1.02  #Partial instantiations: 0
% 1.37/1.02  #Strategies tried      : 1
% 1.37/1.02  
% 1.37/1.02  Timing (in seconds)
% 1.37/1.02  ----------------------
% 1.37/1.02  Preprocessing        : 0.25
% 1.37/1.02  Parsing              : 0.13
% 1.37/1.02  CNF conversion       : 0.01
% 1.37/1.02  Main loop            : 0.02
% 1.37/1.02  Inferencing          : 0.00
% 1.37/1.02  Reduction            : 0.01
% 1.37/1.02  Demodulation         : 0.01
% 1.37/1.02  BG Simplification    : 0.01
% 1.37/1.02  Subsumption          : 0.00
% 1.37/1.02  Abstraction          : 0.00
% 1.37/1.02  MUC search           : 0.00
% 1.37/1.02  Cooper               : 0.00
% 1.37/1.02  Total                : 0.29
% 1.37/1.02  Index Insertion      : 0.00
% 1.37/1.02  Index Deletion       : 0.00
% 1.37/1.02  Index Matching       : 0.00
% 1.37/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------

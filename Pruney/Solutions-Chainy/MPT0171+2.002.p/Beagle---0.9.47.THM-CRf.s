%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:29 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_6,plain,(
    ! [A_10] : k2_enumset1(A_10,A_10,A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8,D_9] : k3_enumset1(A_6,A_6,B_7,C_8,D_9) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_11,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.05  
% 1.53/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.05  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.53/1.05  
% 1.53/1.05  %Foreground sorts:
% 1.53/1.05  
% 1.53/1.05  
% 1.53/1.05  %Background operators:
% 1.53/1.05  
% 1.53/1.05  
% 1.53/1.05  %Foreground operators:
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.53/1.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.53/1.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.53/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.53/1.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.53/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.53/1.05  
% 1.53/1.06  tff(f_31, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.53/1.06  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.53/1.06  tff(f_34, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 1.53/1.06  tff(c_6, plain, (![A_10]: (k2_enumset1(A_10, A_10, A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.06  tff(c_4, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.53/1.06  tff(c_8, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.53/1.06  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.53/1.06  tff(c_11, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9])).
% 1.53/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.06  
% 1.53/1.06  Inference rules
% 1.53/1.06  ----------------------
% 1.53/1.06  #Ref     : 0
% 1.53/1.06  #Sup     : 0
% 1.53/1.06  #Fact    : 0
% 1.53/1.06  #Define  : 0
% 1.53/1.06  #Split   : 0
% 1.53/1.06  #Chain   : 0
% 1.53/1.06  #Close   : 0
% 1.53/1.06  
% 1.53/1.06  Ordering : KBO
% 1.53/1.06  
% 1.53/1.06  Simplification rules
% 1.53/1.06  ----------------------
% 1.53/1.06  #Subsume      : 3
% 1.53/1.06  #Demod        : 2
% 1.53/1.06  #Tautology    : 0
% 1.53/1.06  #SimpNegUnit  : 0
% 1.53/1.06  #BackRed      : 0
% 1.53/1.06  
% 1.53/1.06  #Partial instantiations: 0
% 1.53/1.06  #Strategies tried      : 1
% 1.53/1.06  
% 1.53/1.06  Timing (in seconds)
% 1.53/1.06  ----------------------
% 1.53/1.06  Preprocessing        : 0.25
% 1.53/1.06  Parsing              : 0.13
% 1.53/1.06  CNF conversion       : 0.01
% 1.53/1.06  Main loop            : 0.02
% 1.53/1.06  Inferencing          : 0.00
% 1.53/1.06  Reduction            : 0.01
% 1.53/1.06  Demodulation         : 0.01
% 1.53/1.06  BG Simplification    : 0.01
% 1.53/1.06  Subsumption          : 0.00
% 1.53/1.06  Abstraction          : 0.00
% 1.53/1.06  MUC search           : 0.00
% 1.53/1.06  Cooper               : 0.00
% 1.53/1.06  Total                : 0.29
% 1.53/1.06  Index Insertion      : 0.00
% 1.53/1.06  Index Deletion       : 0.00
% 1.53/1.06  Index Matching       : 0.00
% 1.53/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

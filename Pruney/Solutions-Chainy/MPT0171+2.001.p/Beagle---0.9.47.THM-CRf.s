%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:29 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_36,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),k1_tarski(B_28)) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [B_28] : k2_tarski(B_28,B_28) = k1_tarski(B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_14,plain,(
    ! [A_22,B_23] : k3_enumset1(A_22,A_22,A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.08  
% 1.58/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.08  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.58/1.08  
% 1.58/1.08  %Foreground sorts:
% 1.58/1.08  
% 1.58/1.08  
% 1.58/1.08  %Background operators:
% 1.58/1.08  
% 1.58/1.08  
% 1.58/1.08  %Foreground operators:
% 1.58/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.58/1.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.58/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.08  
% 1.66/1.09  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.66/1.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.66/1.09  tff(f_39, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 1.66/1.09  tff(f_42, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 1.66/1.09  tff(c_36, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(B_28))=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.09  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.09  tff(c_43, plain, (![B_28]: (k2_tarski(B_28, B_28)=k1_tarski(B_28))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2])).
% 1.66/1.09  tff(c_14, plain, (![A_22, B_23]: (k3_enumset1(A_22, A_22, A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.09  tff(c_16, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.09  tff(c_17, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 1.66/1.09  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_17])).
% 1.66/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  Inference rules
% 1.66/1.09  ----------------------
% 1.66/1.09  #Ref     : 0
% 1.66/1.09  #Sup     : 8
% 1.66/1.09  #Fact    : 0
% 1.66/1.09  #Define  : 0
% 1.66/1.09  #Split   : 0
% 1.66/1.09  #Chain   : 0
% 1.66/1.09  #Close   : 0
% 1.66/1.09  
% 1.66/1.09  Ordering : KBO
% 1.66/1.09  
% 1.66/1.09  Simplification rules
% 1.66/1.09  ----------------------
% 1.66/1.09  #Subsume      : 0
% 1.66/1.09  #Demod        : 2
% 1.66/1.09  #Tautology    : 6
% 1.66/1.09  #SimpNegUnit  : 0
% 1.66/1.09  #BackRed      : 1
% 1.66/1.09  
% 1.66/1.09  #Partial instantiations: 0
% 1.66/1.09  #Strategies tried      : 1
% 1.66/1.09  
% 1.66/1.09  Timing (in seconds)
% 1.66/1.09  ----------------------
% 1.66/1.09  Preprocessing        : 0.27
% 1.66/1.09  Parsing              : 0.14
% 1.66/1.09  CNF conversion       : 0.01
% 1.66/1.09  Main loop            : 0.06
% 1.66/1.09  Inferencing          : 0.02
% 1.66/1.09  Reduction            : 0.02
% 1.66/1.09  Demodulation         : 0.02
% 1.66/1.09  BG Simplification    : 0.01
% 1.66/1.09  Subsumption          : 0.01
% 1.66/1.09  Abstraction          : 0.00
% 1.66/1.09  MUC search           : 0.00
% 1.66/1.09  Cooper               : 0.00
% 1.66/1.09  Total                : 0.34
% 1.66/1.09  Index Insertion      : 0.00
% 1.66/1.09  Index Deletion       : 0.00
% 1.66/1.09  Index Matching       : 0.00
% 1.66/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

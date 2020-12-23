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
% DateTime   : Thu Dec  3 09:46:09 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_6,C_12] : k2_xboole_0(k1_tarski(A_6),k1_tarski(C_12)) = k1_enumset1(A_6,A_6,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_39,plain,(
    ! [A_6,C_12] : k1_enumset1(A_6,A_6,C_12) = k2_tarski(A_6,C_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_8,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  %$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.12  
% 1.71/1.13  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.71/1.13  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.13  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.71/1.13  tff(f_34, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.71/1.13  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.13  tff(c_6, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.13  tff(c_27, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.13  tff(c_36, plain, (![A_6, C_12]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(C_12))=k1_enumset1(A_6, A_6, C_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_27])).
% 1.71/1.13  tff(c_39, plain, (![A_6, C_12]: (k1_enumset1(A_6, A_6, C_12)=k2_tarski(A_6, C_12))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.71/1.13  tff(c_8, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.71/1.13  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_8])).
% 1.71/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  Inference rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Ref     : 0
% 1.71/1.13  #Sup     : 7
% 1.71/1.13  #Fact    : 0
% 1.71/1.13  #Define  : 0
% 1.71/1.13  #Split   : 0
% 1.71/1.13  #Chain   : 0
% 1.71/1.13  #Close   : 0
% 1.71/1.13  
% 1.71/1.13  Ordering : KBO
% 1.71/1.13  
% 1.71/1.13  Simplification rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Subsume      : 0
% 1.71/1.13  #Demod        : 2
% 1.71/1.13  #Tautology    : 6
% 1.71/1.13  #SimpNegUnit  : 0
% 1.71/1.13  #BackRed      : 1
% 1.71/1.13  
% 1.71/1.13  #Partial instantiations: 0
% 1.71/1.13  #Strategies tried      : 1
% 1.71/1.13  
% 1.71/1.13  Timing (in seconds)
% 1.71/1.13  ----------------------
% 1.71/1.13  Preprocessing        : 0.27
% 1.71/1.13  Parsing              : 0.14
% 1.71/1.13  CNF conversion       : 0.02
% 1.71/1.13  Main loop            : 0.06
% 1.71/1.13  Inferencing          : 0.03
% 1.71/1.13  Reduction            : 0.02
% 1.71/1.13  Demodulation         : 0.02
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.01
% 1.71/1.13  Abstraction          : 0.00
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.35
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

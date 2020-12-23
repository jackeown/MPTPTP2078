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
% DateTime   : Thu Dec  3 09:46:26 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(c_8,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_11] : k1_enumset1(A_11,A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_11,D_22] : k2_xboole_0(k1_tarski(A_11),k1_tarski(D_22)) = k2_enumset1(A_11,A_11,A_11,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_65,plain,(
    ! [A_11,D_22] : k2_enumset1(A_11,A_11,A_11,D_22) = k2_tarski(A_11,D_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.09  
% 1.69/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.69/1.10  
% 1.69/1.10  %Foreground sorts:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Background operators:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Foreground operators:
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.10  
% 1.69/1.10  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.69/1.10  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.69/1.10  tff(f_35, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.69/1.10  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.69/1.10  tff(f_38, negated_conjecture, ~(![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.69/1.10  tff(c_8, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.10  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.10  tff(c_10, plain, (![A_11]: (k1_enumset1(A_11, A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.10  tff(c_53, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.10  tff(c_62, plain, (![A_11, D_22]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(D_22))=k2_enumset1(A_11, A_11, A_11, D_22))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 1.69/1.10  tff(c_65, plain, (![A_11, D_22]: (k2_enumset1(A_11, A_11, A_11, D_22)=k2_tarski(A_11, D_22))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 1.69/1.10  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.10  tff(c_88, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_12])).
% 1.69/1.10  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 1.69/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  Inference rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Ref     : 0
% 1.69/1.10  #Sup     : 17
% 1.69/1.10  #Fact    : 0
% 1.69/1.10  #Define  : 0
% 1.69/1.10  #Split   : 0
% 1.69/1.10  #Chain   : 0
% 1.69/1.10  #Close   : 0
% 1.69/1.10  
% 1.69/1.10  Ordering : KBO
% 1.69/1.10  
% 1.69/1.10  Simplification rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Subsume      : 0
% 1.69/1.10  #Demod        : 7
% 1.69/1.10  #Tautology    : 14
% 1.69/1.10  #SimpNegUnit  : 0
% 1.69/1.10  #BackRed      : 1
% 1.69/1.10  
% 1.69/1.10  #Partial instantiations: 0
% 1.69/1.10  #Strategies tried      : 1
% 1.69/1.10  
% 1.69/1.10  Timing (in seconds)
% 1.69/1.10  ----------------------
% 1.69/1.11  Preprocessing        : 0.27
% 1.69/1.11  Parsing              : 0.14
% 1.69/1.11  CNF conversion       : 0.01
% 1.69/1.11  Main loop            : 0.09
% 1.69/1.11  Inferencing          : 0.04
% 1.69/1.11  Reduction            : 0.03
% 1.69/1.11  Demodulation         : 0.02
% 1.69/1.11  BG Simplification    : 0.01
% 1.69/1.11  Subsumption          : 0.01
% 1.69/1.11  Abstraction          : 0.01
% 1.69/1.11  MUC search           : 0.00
% 1.69/1.11  Cooper               : 0.00
% 1.69/1.11  Total                : 0.38
% 1.69/1.11  Index Insertion      : 0.00
% 1.69/1.11  Index Deletion       : 0.00
% 1.69/1.11  Index Matching       : 0.00
% 1.69/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

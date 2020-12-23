%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:30 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_9] : k3_enumset1(A_9,A_9,A_9,A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_16,E_13,F_15,D_14,B_18,C_17] : k2_xboole_0(k3_enumset1(A_16,B_18,C_17,D_14,E_13),k1_tarski(F_15)) = k4_enumset1(A_16,B_18,C_17,D_14,E_13,F_15) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_9,F_15] : k4_enumset1(A_9,A_9,A_9,A_9,A_9,F_15) = k2_xboole_0(k1_tarski(A_9),k1_tarski(F_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_39,plain,(
    ! [A_9,F_15] : k4_enumset1(A_9,A_9,A_9,A_9,A_9,F_15) = k2_tarski(A_9,F_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_8,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:06 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.12  %$ k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.60/1.12  
% 1.60/1.12  %Foreground sorts:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Background operators:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Foreground operators:
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.60/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.12  
% 1.60/1.12  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.60/1.12  tff(f_31, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 1.60/1.12  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 1.60/1.12  tff(f_34, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 1.60/1.12  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.12  tff(c_6, plain, (![A_9]: (k3_enumset1(A_9, A_9, A_9, A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.12  tff(c_27, plain, (![A_16, E_13, F_15, D_14, B_18, C_17]: (k2_xboole_0(k3_enumset1(A_16, B_18, C_17, D_14, E_13), k1_tarski(F_15))=k4_enumset1(A_16, B_18, C_17, D_14, E_13, F_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.12  tff(c_36, plain, (![A_9, F_15]: (k4_enumset1(A_9, A_9, A_9, A_9, A_9, F_15)=k2_xboole_0(k1_tarski(A_9), k1_tarski(F_15)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_27])).
% 1.60/1.12  tff(c_39, plain, (![A_9, F_15]: (k4_enumset1(A_9, A_9, A_9, A_9, A_9, F_15)=k2_tarski(A_9, F_15))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.60/1.12  tff(c_8, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.12  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_8])).
% 1.60/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  Inference rules
% 1.60/1.12  ----------------------
% 1.60/1.12  #Ref     : 0
% 1.60/1.12  #Sup     : 7
% 1.60/1.12  #Fact    : 0
% 1.60/1.12  #Define  : 0
% 1.60/1.12  #Split   : 0
% 1.60/1.12  #Chain   : 0
% 1.60/1.12  #Close   : 0
% 1.60/1.12  
% 1.60/1.12  Ordering : KBO
% 1.60/1.12  
% 1.60/1.12  Simplification rules
% 1.60/1.12  ----------------------
% 1.60/1.12  #Subsume      : 0
% 1.60/1.12  #Demod        : 2
% 1.60/1.12  #Tautology    : 6
% 1.60/1.12  #SimpNegUnit  : 0
% 1.60/1.12  #BackRed      : 1
% 1.60/1.12  
% 1.60/1.12  #Partial instantiations: 0
% 1.60/1.12  #Strategies tried      : 1
% 1.60/1.12  
% 1.60/1.12  Timing (in seconds)
% 1.60/1.12  ----------------------
% 1.60/1.13  Preprocessing        : 0.27
% 1.60/1.13  Parsing              : 0.14
% 1.60/1.13  CNF conversion       : 0.02
% 1.60/1.13  Main loop            : 0.06
% 1.60/1.13  Inferencing          : 0.03
% 1.60/1.13  Reduction            : 0.02
% 1.60/1.13  Demodulation         : 0.02
% 1.60/1.13  BG Simplification    : 0.01
% 1.60/1.13  Subsumption          : 0.01
% 1.60/1.13  Abstraction          : 0.00
% 1.60/1.13  MUC search           : 0.00
% 1.60/1.13  Cooper               : 0.00
% 1.60/1.13  Total                : 0.36
% 1.60/1.13  Index Insertion      : 0.00
% 1.60/1.13  Index Deletion       : 0.00
% 1.60/1.13  Index Matching       : 0.00
% 1.60/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [B_26] : k2_tarski(B_26,B_26) = k1_tarski(B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_4])).

tff(c_165,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k2_tarski(A_33,B_34),k1_tarski(C_35)) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [B_26,C_35] : k2_xboole_0(k1_tarski(B_26),k1_tarski(C_35)) = k1_enumset1(B_26,B_26,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_165])).

tff(c_177,plain,(
    ! [B_26,C_35] : k1_enumset1(B_26,B_26,C_35) = k2_tarski(B_26,C_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_18,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:04:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.13  
% 1.68/1.13  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.68/1.13  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.68/1.13  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.68/1.13  tff(f_44, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.68/1.13  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.13  tff(c_88, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.13  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.13  tff(c_95, plain, (![B_26]: (k2_tarski(B_26, B_26)=k1_tarski(B_26))), inference(superposition, [status(thm), theory('equality')], [c_88, c_4])).
% 1.68/1.13  tff(c_165, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_tarski(C_35))=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.13  tff(c_174, plain, (![B_26, C_35]: (k2_xboole_0(k1_tarski(B_26), k1_tarski(C_35))=k1_enumset1(B_26, B_26, C_35))), inference(superposition, [status(thm), theory('equality')], [c_95, c_165])).
% 1.68/1.13  tff(c_177, plain, (![B_26, C_35]: (k1_enumset1(B_26, B_26, C_35)=k2_tarski(B_26, C_35))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_174])).
% 1.68/1.13  tff(c_18, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.13  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_18])).
% 1.68/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  Inference rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Ref     : 0
% 1.68/1.13  #Sup     : 37
% 1.68/1.13  #Fact    : 0
% 1.68/1.13  #Define  : 0
% 1.68/1.13  #Split   : 0
% 1.68/1.13  #Chain   : 0
% 1.68/1.13  #Close   : 0
% 1.68/1.13  
% 1.68/1.13  Ordering : KBO
% 1.68/1.13  
% 1.68/1.13  Simplification rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Subsume      : 0
% 1.68/1.13  #Demod        : 7
% 1.68/1.13  #Tautology    : 33
% 1.68/1.13  #SimpNegUnit  : 0
% 1.68/1.13  #BackRed      : 1
% 1.68/1.13  
% 1.68/1.13  #Partial instantiations: 0
% 1.68/1.13  #Strategies tried      : 1
% 1.68/1.13  
% 1.68/1.13  Timing (in seconds)
% 1.68/1.13  ----------------------
% 1.80/1.14  Preprocessing        : 0.27
% 1.80/1.14  Parsing              : 0.14
% 1.80/1.14  CNF conversion       : 0.02
% 1.80/1.14  Main loop            : 0.11
% 1.80/1.14  Inferencing          : 0.05
% 1.80/1.14  Reduction            : 0.04
% 1.80/1.14  Demodulation         : 0.03
% 1.80/1.14  BG Simplification    : 0.01
% 1.80/1.14  Subsumption          : 0.01
% 1.80/1.14  Abstraction          : 0.01
% 1.80/1.14  MUC search           : 0.00
% 1.80/1.14  Cooper               : 0.00
% 1.80/1.14  Total                : 0.40
% 1.80/1.14  Index Insertion      : 0.00
% 1.80/1.14  Index Deletion       : 0.00
% 1.80/1.14  Index Matching       : 0.00
% 1.80/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

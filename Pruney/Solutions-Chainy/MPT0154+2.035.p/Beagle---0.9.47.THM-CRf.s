%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:08 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_67,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k1_tarski(A_16),k2_tarski(B_17,C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k2_tarski(A_3,B_4)) = k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_49,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k2_tarski(A_3,B_4)) = k2_tarski(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_74,plain,(
    ! [B_17,C_18] : k1_enumset1(B_17,B_17,C_18) = k2_tarski(B_17,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_49])).

tff(c_10,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  %$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.62/1.11  
% 1.62/1.11  %Foreground sorts:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Background operators:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Foreground operators:
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.11  
% 1.62/1.12  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.62/1.12  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.62/1.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.62/1.12  tff(f_36, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.62/1.12  tff(c_67, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k1_tarski(A_16), k2_tarski(B_17, C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.12  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.12  tff(c_29, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.12  tff(c_44, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(A_3, B_4))=k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_29])).
% 1.62/1.12  tff(c_49, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(A_3, B_4))=k2_tarski(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_44])).
% 1.62/1.12  tff(c_74, plain, (![B_17, C_18]: (k1_enumset1(B_17, B_17, C_18)=k2_tarski(B_17, C_18))), inference(superposition, [status(thm), theory('equality')], [c_67, c_49])).
% 1.62/1.12  tff(c_10, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.12  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_10])).
% 1.62/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  Inference rules
% 1.62/1.12  ----------------------
% 1.62/1.12  #Ref     : 0
% 1.62/1.12  #Sup     : 21
% 1.62/1.12  #Fact    : 0
% 1.62/1.12  #Define  : 0
% 1.62/1.12  #Split   : 0
% 1.62/1.12  #Chain   : 0
% 1.62/1.12  #Close   : 0
% 1.62/1.12  
% 1.62/1.12  Ordering : KBO
% 1.62/1.12  
% 1.62/1.12  Simplification rules
% 1.62/1.12  ----------------------
% 1.62/1.12  #Subsume      : 0
% 1.62/1.12  #Demod        : 11
% 1.62/1.12  #Tautology    : 15
% 1.62/1.12  #SimpNegUnit  : 0
% 1.62/1.12  #BackRed      : 1
% 1.62/1.12  
% 1.62/1.12  #Partial instantiations: 0
% 1.62/1.12  #Strategies tried      : 1
% 1.62/1.12  
% 1.62/1.12  Timing (in seconds)
% 1.62/1.12  ----------------------
% 1.62/1.12  Preprocessing        : 0.26
% 1.62/1.12  Parsing              : 0.14
% 1.62/1.12  CNF conversion       : 0.01
% 1.62/1.12  Main loop            : 0.09
% 1.62/1.12  Inferencing          : 0.04
% 1.62/1.12  Reduction            : 0.03
% 1.62/1.12  Demodulation         : 0.02
% 1.62/1.12  BG Simplification    : 0.01
% 1.62/1.12  Subsumption          : 0.01
% 1.62/1.12  Abstraction          : 0.01
% 1.62/1.12  MUC search           : 0.00
% 1.62/1.12  Cooper               : 0.00
% 1.62/1.12  Total                : 0.37
% 1.62/1.12  Index Insertion      : 0.00
% 1.62/1.12  Index Deletion       : 0.00
% 1.62/1.12  Index Matching       : 0.00
% 1.62/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

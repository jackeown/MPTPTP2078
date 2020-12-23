%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:40 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   16 (  20 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_8,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_xboole_0(k1_tarski(A_10),k1_enumset1(B_11,C_12,D_13)) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_tarski(A_7,B_8),k1_tarski(C_9)) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_23,B_24),C_25),D_26) = k2_xboole_0(A_23,k2_xboole_0(k2_xboole_0(B_24,C_25),D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_xboole_0(k1_tarski(A_27),k2_xboole_0(k2_xboole_0(k1_tarski(B_28),C_29),D_30)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_27,B_28),C_29),D_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_91,plain,(
    ! [A_27,A_5,B_6,D_30] : k2_xboole_0(k2_xboole_0(k2_tarski(A_27,A_5),k1_tarski(B_6)),D_30) = k2_xboole_0(k1_tarski(A_27),k2_xboole_0(k2_tarski(A_5,B_6),D_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_98,plain,(
    ! [A_31,A_32,B_33,D_34] : k2_xboole_0(k1_tarski(A_31),k2_xboole_0(k2_tarski(A_32,B_33),D_34)) = k2_xboole_0(k1_enumset1(A_31,A_32,B_33),D_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_113,plain,(
    ! [A_31,A_7,B_8,C_9] : k2_xboole_0(k1_enumset1(A_31,A_7,B_8),k1_tarski(C_9)) = k2_xboole_0(k1_tarski(A_31),k1_enumset1(A_7,B_8,C_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_117,plain,(
    ! [A_31,A_7,B_8,C_9] : k2_xboole_0(k1_enumset1(A_31,A_7,B_8),k1_tarski(C_9)) = k2_enumset1(A_31,A_7,B_8,C_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_10,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.18  
% 1.77/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.18  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.77/1.18  
% 1.77/1.18  %Foreground sorts:
% 1.77/1.18  
% 1.77/1.18  
% 1.77/1.18  %Background operators:
% 1.77/1.18  
% 1.77/1.18  
% 1.77/1.18  %Foreground operators:
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.18  
% 1.77/1.19  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.77/1.19  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.77/1.19  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.77/1.19  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 1.77/1.19  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.77/1.19  tff(c_8, plain, (![A_10, B_11, C_12, D_13]: (k2_xboole_0(k1_tarski(A_10), k1_enumset1(B_11, C_12, D_13))=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.19  tff(c_6, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_tarski(A_7, B_8), k1_tarski(C_9))=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.19  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.19  tff(c_38, plain, (![A_23, B_24, C_25, D_26]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_23, B_24), C_25), D_26)=k2_xboole_0(A_23, k2_xboole_0(k2_xboole_0(B_24, C_25), D_26)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.19  tff(c_70, plain, (![A_27, B_28, C_29, D_30]: (k2_xboole_0(k1_tarski(A_27), k2_xboole_0(k2_xboole_0(k1_tarski(B_28), C_29), D_30))=k2_xboole_0(k2_xboole_0(k2_tarski(A_27, B_28), C_29), D_30))), inference(superposition, [status(thm), theory('equality')], [c_4, c_38])).
% 1.77/1.19  tff(c_91, plain, (![A_27, A_5, B_6, D_30]: (k2_xboole_0(k2_xboole_0(k2_tarski(A_27, A_5), k1_tarski(B_6)), D_30)=k2_xboole_0(k1_tarski(A_27), k2_xboole_0(k2_tarski(A_5, B_6), D_30)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70])).
% 1.77/1.19  tff(c_98, plain, (![A_31, A_32, B_33, D_34]: (k2_xboole_0(k1_tarski(A_31), k2_xboole_0(k2_tarski(A_32, B_33), D_34))=k2_xboole_0(k1_enumset1(A_31, A_32, B_33), D_34))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_91])).
% 1.77/1.19  tff(c_113, plain, (![A_31, A_7, B_8, C_9]: (k2_xboole_0(k1_enumset1(A_31, A_7, B_8), k1_tarski(C_9))=k2_xboole_0(k1_tarski(A_31), k1_enumset1(A_7, B_8, C_9)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_98])).
% 1.77/1.19  tff(c_117, plain, (![A_31, A_7, B_8, C_9]: (k2_xboole_0(k1_enumset1(A_31, A_7, B_8), k1_tarski(C_9))=k2_enumset1(A_31, A_7, B_8, C_9))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_113])).
% 1.77/1.19  tff(c_10, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.77/1.19  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_10])).
% 1.77/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.19  
% 1.77/1.19  Inference rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Ref     : 0
% 1.77/1.19  #Sup     : 27
% 1.77/1.19  #Fact    : 0
% 1.77/1.19  #Define  : 0
% 1.77/1.19  #Split   : 0
% 1.77/1.19  #Chain   : 0
% 1.77/1.19  #Close   : 0
% 1.77/1.19  
% 1.77/1.19  Ordering : KBO
% 1.77/1.19  
% 1.77/1.19  Simplification rules
% 1.77/1.19  ----------------------
% 1.77/1.19  #Subsume      : 0
% 1.77/1.19  #Demod        : 17
% 1.77/1.19  #Tautology    : 14
% 1.77/1.19  #SimpNegUnit  : 0
% 1.77/1.19  #BackRed      : 1
% 1.77/1.19  
% 1.77/1.19  #Partial instantiations: 0
% 1.77/1.19  #Strategies tried      : 1
% 1.77/1.19  
% 1.77/1.19  Timing (in seconds)
% 1.77/1.19  ----------------------
% 1.77/1.19  Preprocessing        : 0.25
% 1.77/1.19  Parsing              : 0.15
% 1.77/1.19  CNF conversion       : 0.01
% 1.77/1.19  Main loop            : 0.14
% 1.77/1.19  Inferencing          : 0.06
% 1.77/1.19  Reduction            : 0.05
% 1.77/1.19  Demodulation         : 0.04
% 1.77/1.19  BG Simplification    : 0.01
% 1.77/1.19  Subsumption          : 0.01
% 1.77/1.19  Abstraction          : 0.01
% 1.77/1.19  MUC search           : 0.00
% 1.77/1.19  Cooper               : 0.00
% 1.77/1.19  Total                : 0.42
% 1.77/1.19  Index Insertion      : 0.00
% 1.77/1.19  Index Deletion       : 0.00
% 1.77/1.19  Index Matching       : 0.00
% 1.77/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

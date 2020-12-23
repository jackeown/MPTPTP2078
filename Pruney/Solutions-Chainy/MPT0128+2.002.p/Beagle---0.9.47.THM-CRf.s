%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:38 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  23 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_xboole_0(A_15,B_16),C_17) = k2_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k1_tarski(A_25),k2_xboole_0(k1_tarski(B_26),C_27)) = k2_xboole_0(k2_tarski(A_25,B_26),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_82,plain,(
    ! [A_25,A_8,B_9] : k2_xboole_0(k2_tarski(A_25,A_8),k1_tarski(B_9)) = k2_xboole_0(k1_tarski(A_25),k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_87,plain,(
    ! [A_28,A_29,B_30] : k2_xboole_0(k1_tarski(A_28),k2_tarski(A_29,B_30)) = k1_enumset1(A_28,A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_35,plain,(
    ! [A_8,B_9,C_17] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k1_tarski(B_9),C_17)) = k2_xboole_0(k2_tarski(A_8,B_9),C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_93,plain,(
    ! [A_8,A_28,A_29,B_30] : k2_xboole_0(k2_tarski(A_8,A_28),k2_tarski(A_29,B_30)) = k2_xboole_0(k1_tarski(A_8),k1_enumset1(A_28,A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_35])).

tff(c_101,plain,(
    ! [A_8,A_28,A_29,B_30] : k2_xboole_0(k1_tarski(A_8),k1_enumset1(A_28,A_29,B_30)) = k2_enumset1(A_8,A_28,A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_enumset1('#skF_2','#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.10  
% 1.65/1.11  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.65/1.11  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.65/1.11  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.65/1.11  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.65/1.11  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.65/1.11  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.11  tff(c_8, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.11  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.11  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_xboole_0(A_15, B_16), C_17)=k2_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.11  tff(c_64, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k1_tarski(A_25), k2_xboole_0(k1_tarski(B_26), C_27))=k2_xboole_0(k2_tarski(A_25, B_26), C_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20])).
% 1.65/1.11  tff(c_82, plain, (![A_25, A_8, B_9]: (k2_xboole_0(k2_tarski(A_25, A_8), k1_tarski(B_9))=k2_xboole_0(k1_tarski(A_25), k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 1.65/1.11  tff(c_87, plain, (![A_28, A_29, B_30]: (k2_xboole_0(k1_tarski(A_28), k2_tarski(A_29, B_30))=k1_enumset1(A_28, A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_82])).
% 1.65/1.11  tff(c_35, plain, (![A_8, B_9, C_17]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_17))=k2_xboole_0(k2_tarski(A_8, B_9), C_17))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20])).
% 1.65/1.11  tff(c_93, plain, (![A_8, A_28, A_29, B_30]: (k2_xboole_0(k2_tarski(A_8, A_28), k2_tarski(A_29, B_30))=k2_xboole_0(k1_tarski(A_8), k1_enumset1(A_28, A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_35])).
% 1.65/1.11  tff(c_101, plain, (![A_8, A_28, A_29, B_30]: (k2_xboole_0(k1_tarski(A_8), k1_enumset1(A_28, A_29, B_30))=k2_enumset1(A_8, A_28, A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93])).
% 1.65/1.11  tff(c_10, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_enumset1('#skF_2', '#skF_3', '#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.11  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_10])).
% 1.65/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  Inference rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Ref     : 0
% 1.65/1.11  #Sup     : 23
% 1.65/1.11  #Fact    : 0
% 1.65/1.11  #Define  : 0
% 1.65/1.11  #Split   : 0
% 1.65/1.11  #Chain   : 0
% 1.65/1.11  #Close   : 0
% 1.65/1.11  
% 1.65/1.11  Ordering : KBO
% 1.65/1.11  
% 1.65/1.11  Simplification rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Subsume      : 0
% 1.65/1.11  #Demod        : 12
% 1.65/1.11  #Tautology    : 15
% 1.65/1.11  #SimpNegUnit  : 0
% 1.65/1.11  #BackRed      : 1
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.11  Preprocessing        : 0.24
% 1.65/1.11  Parsing              : 0.13
% 1.65/1.11  CNF conversion       : 0.01
% 1.65/1.11  Main loop            : 0.11
% 1.65/1.11  Inferencing          : 0.05
% 1.65/1.11  Reduction            : 0.04
% 1.65/1.11  Demodulation         : 0.03
% 1.65/1.11  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.01
% 1.65/1.11  Abstraction          : 0.01
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.38
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

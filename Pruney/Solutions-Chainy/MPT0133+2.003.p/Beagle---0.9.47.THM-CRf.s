%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k1_tarski(A_30),k2_xboole_0(k1_tarski(B_31),C_32)) = k2_xboole_0(k2_tarski(A_30,B_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_87,plain,(
    ! [A_30,A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_30,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k1_tarski(A_30),k1_enumset1(A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_94,plain,(
    ! [A_30,A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_30,A_6),k2_tarski(B_7,C_8)) = k2_enumset1(A_30,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_135,plain,(
    ! [A_45,B_46,C_47,C_48] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k2_tarski(B_46,C_47),C_48)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_150,plain,(
    ! [B_7,C_8,A_45,A_30,A_6] : k2_xboole_0(k1_enumset1(A_45,A_30,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_30,A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_135])).

tff(c_157,plain,(
    ! [B_7,C_8,A_45,A_30,A_6] : k2_xboole_0(k1_enumset1(A_45,A_30,A_6),k2_tarski(B_7,C_8)) = k3_enumset1(A_45,A_30,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_150])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.19  
% 1.99/1.19  %Foreground sorts:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Background operators:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Foreground operators:
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.19  
% 2.03/1.20  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.03/1.20  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.03/1.20  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.03/1.20  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.03/1.20  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.03/1.20  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 2.03/1.20  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.20  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.20  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.20  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.20  tff(c_31, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.20  tff(c_66, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k1_tarski(A_30), k2_xboole_0(k1_tarski(B_31), C_32))=k2_xboole_0(k2_tarski(A_30, B_31), C_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 2.03/1.20  tff(c_87, plain, (![A_30, A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_30, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k1_tarski(A_30), k1_enumset1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.03/1.20  tff(c_94, plain, (![A_30, A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_30, A_6), k2_tarski(B_7, C_8))=k2_enumset1(A_30, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 2.03/1.20  tff(c_135, plain, (![A_45, B_46, C_47, C_48]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k2_tarski(B_46, C_47), C_48))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_48))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.03/1.20  tff(c_150, plain, (![B_7, C_8, A_45, A_30, A_6]: (k2_xboole_0(k1_enumset1(A_45, A_30, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_30, A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_135])).
% 2.03/1.20  tff(c_157, plain, (![B_7, C_8, A_45, A_30, A_6]: (k2_xboole_0(k1_enumset1(A_45, A_30, A_6), k2_tarski(B_7, C_8))=k3_enumset1(A_45, A_30, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_150])).
% 2.03/1.20  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.20  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_12])).
% 2.03/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  Inference rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Ref     : 0
% 2.03/1.20  #Sup     : 50
% 2.03/1.20  #Fact    : 0
% 2.03/1.20  #Define  : 0
% 2.03/1.20  #Split   : 0
% 2.03/1.20  #Chain   : 0
% 2.03/1.20  #Close   : 0
% 2.03/1.20  
% 2.03/1.20  Ordering : KBO
% 2.03/1.20  
% 2.03/1.20  Simplification rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Subsume      : 0
% 2.03/1.20  #Demod        : 22
% 2.03/1.20  #Tautology    : 28
% 2.03/1.20  #SimpNegUnit  : 0
% 2.03/1.20  #BackRed      : 1
% 2.03/1.20  
% 2.03/1.20  #Partial instantiations: 0
% 2.03/1.20  #Strategies tried      : 1
% 2.03/1.20  
% 2.03/1.20  Timing (in seconds)
% 2.03/1.20  ----------------------
% 2.03/1.21  Preprocessing        : 0.27
% 2.03/1.21  Parsing              : 0.15
% 2.03/1.21  CNF conversion       : 0.02
% 2.03/1.21  Main loop            : 0.18
% 2.03/1.21  Inferencing          : 0.08
% 2.03/1.21  Reduction            : 0.06
% 2.03/1.21  Demodulation         : 0.05
% 2.03/1.21  BG Simplification    : 0.01
% 2.03/1.21  Subsumption          : 0.02
% 2.03/1.21  Abstraction          : 0.01
% 2.03/1.21  MUC search           : 0.00
% 2.03/1.21  Cooper               : 0.00
% 2.03/1.21  Total                : 0.48
% 2.03/1.21  Index Insertion      : 0.00
% 2.03/1.21  Index Deletion       : 0.00
% 2.03/1.21  Index Matching       : 0.00
% 2.03/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

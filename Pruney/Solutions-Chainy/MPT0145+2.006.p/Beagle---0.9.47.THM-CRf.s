%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:53 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k3_enumset1(A_20,B_21,C_22,D_23,E_24),k2_tarski(F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_76,B_75,D_73,C_74,F_72,E_71] : k2_xboole_0(k3_enumset1(A_76,B_75,C_74,D_73,E_71),k1_tarski(F_72)) = k4_enumset1(A_76,B_75,C_74,D_73,E_71,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_379,plain,(
    ! [C_114,F_115,D_113,A_118,B_116,C_117,E_112] : k2_xboole_0(k3_enumset1(A_118,B_116,C_114,D_113,E_112),k2_xboole_0(k1_tarski(F_115),C_117)) = k2_xboole_0(k4_enumset1(A_118,B_116,C_114,D_113,E_112,F_115),C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_2])).

tff(c_400,plain,(
    ! [C_114,B_10,D_113,A_118,B_116,E_112,A_9] : k2_xboole_0(k4_enumset1(A_118,B_116,C_114,D_113,E_112,A_9),k1_tarski(B_10)) = k2_xboole_0(k3_enumset1(A_118,B_116,C_114,D_113,E_112),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_379])).

tff(c_404,plain,(
    ! [C_114,B_10,D_113,A_118,B_116,E_112,A_9] : k2_xboole_0(k4_enumset1(A_118,B_116,C_114,D_113,E_112,A_9),k1_tarski(B_10)) = k5_enumset1(A_118,B_116,C_114,D_113,E_112,A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_400])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.31  
% 2.51/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.32  
% 2.51/1.32  %Foreground sorts:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Background operators:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Foreground operators:
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.32  
% 2.51/1.32  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.51/1.32  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.51/1.32  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.51/1.32  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.51/1.32  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.51/1.32  tff(c_12, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k3_enumset1(A_20, B_21, C_22, D_23, E_24), k2_tarski(F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.32  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.32  tff(c_215, plain, (![A_76, B_75, D_73, C_74, F_72, E_71]: (k2_xboole_0(k3_enumset1(A_76, B_75, C_74, D_73, E_71), k1_tarski(F_72))=k4_enumset1(A_76, B_75, C_74, D_73, E_71, F_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.32  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.32  tff(c_379, plain, (![C_114, F_115, D_113, A_118, B_116, C_117, E_112]: (k2_xboole_0(k3_enumset1(A_118, B_116, C_114, D_113, E_112), k2_xboole_0(k1_tarski(F_115), C_117))=k2_xboole_0(k4_enumset1(A_118, B_116, C_114, D_113, E_112, F_115), C_117))), inference(superposition, [status(thm), theory('equality')], [c_215, c_2])).
% 2.51/1.32  tff(c_400, plain, (![C_114, B_10, D_113, A_118, B_116, E_112, A_9]: (k2_xboole_0(k4_enumset1(A_118, B_116, C_114, D_113, E_112, A_9), k1_tarski(B_10))=k2_xboole_0(k3_enumset1(A_118, B_116, C_114, D_113, E_112), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_379])).
% 2.51/1.32  tff(c_404, plain, (![C_114, B_10, D_113, A_118, B_116, E_112, A_9]: (k2_xboole_0(k4_enumset1(A_118, B_116, C_114, D_113, E_112, A_9), k1_tarski(B_10))=k5_enumset1(A_118, B_116, C_114, D_113, E_112, A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_400])).
% 2.51/1.32  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.32  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_14])).
% 2.51/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  
% 2.51/1.32  Inference rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Ref     : 0
% 2.51/1.32  #Sup     : 105
% 2.51/1.32  #Fact    : 0
% 2.51/1.32  #Define  : 0
% 2.51/1.32  #Split   : 0
% 2.51/1.32  #Chain   : 0
% 2.51/1.32  #Close   : 0
% 2.51/1.32  
% 2.51/1.32  Ordering : KBO
% 2.51/1.32  
% 2.51/1.32  Simplification rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Subsume      : 0
% 2.51/1.32  #Demod        : 75
% 2.51/1.32  #Tautology    : 62
% 2.51/1.32  #SimpNegUnit  : 0
% 2.51/1.32  #BackRed      : 3
% 2.51/1.32  
% 2.51/1.32  #Partial instantiations: 0
% 2.51/1.32  #Strategies tried      : 1
% 2.51/1.32  
% 2.51/1.32  Timing (in seconds)
% 2.51/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.28
% 2.51/1.33  Parsing              : 0.16
% 2.51/1.33  CNF conversion       : 0.02
% 2.51/1.33  Main loop            : 0.28
% 2.51/1.33  Inferencing          : 0.13
% 2.51/1.33  Reduction            : 0.10
% 2.51/1.33  Demodulation         : 0.08
% 2.51/1.33  BG Simplification    : 0.02
% 2.51/1.33  Subsumption          : 0.03
% 2.51/1.33  Abstraction          : 0.02
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.58
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

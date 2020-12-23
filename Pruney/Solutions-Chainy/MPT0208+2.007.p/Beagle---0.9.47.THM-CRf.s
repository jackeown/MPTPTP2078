%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_6,plain,(
    ! [H_20,E_17,F_18,I_21,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18),k1_enumset1(G_19,H_20,I_21)) = k7_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20,I_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_209,plain,(
    ! [G_87,A_88,D_84,F_81,E_85,H_83,B_86,C_82] : k2_xboole_0(k4_enumset1(A_88,B_86,C_82,D_84,E_85,F_81),k2_tarski(G_87,H_83)) = k6_enumset1(A_88,B_86,C_82,D_84,E_85,F_81,G_87,H_83) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_453,plain,(
    ! [A_152,G_148,H_147,B_146,F_151,C_153,E_150,C_149,D_154] : k2_xboole_0(k4_enumset1(A_152,B_146,C_149,D_154,E_150,F_151),k2_xboole_0(k2_tarski(G_148,H_147),C_153)) = k2_xboole_0(k6_enumset1(A_152,B_146,C_149,D_154,E_150,F_151,G_148,H_147),C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2])).

tff(c_474,plain,(
    ! [A_152,A_24,B_25,C_26,B_146,F_151,E_150,C_149,D_154] : k2_xboole_0(k6_enumset1(A_152,B_146,C_149,D_154,E_150,F_151,A_24,B_25),k1_tarski(C_26)) = k2_xboole_0(k4_enumset1(A_152,B_146,C_149,D_154,E_150,F_151),k1_enumset1(A_24,B_25,C_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_478,plain,(
    ! [A_152,A_24,B_25,C_26,B_146,F_151,E_150,C_149,D_154] : k2_xboole_0(k6_enumset1(A_152,B_146,C_149,D_154,E_150,F_151,A_24,B_25),k1_tarski(C_26)) = k7_enumset1(A_152,B_146,C_149,D_154,E_150,F_151,A_24,B_25,C_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_474])).

tff(c_18,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.42  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.77/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.42  
% 2.77/1.43  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 2.77/1.43  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.77/1.43  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 2.77/1.43  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.77/1.43  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 2.77/1.43  tff(c_6, plain, (![H_20, E_17, F_18, I_21, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18), k1_enumset1(G_19, H_20, I_21))=k7_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20, I_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.43  tff(c_10, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.43  tff(c_209, plain, (![G_87, A_88, D_84, F_81, E_85, H_83, B_86, C_82]: (k2_xboole_0(k4_enumset1(A_88, B_86, C_82, D_84, E_85, F_81), k2_tarski(G_87, H_83))=k6_enumset1(A_88, B_86, C_82, D_84, E_85, F_81, G_87, H_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.43  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.43  tff(c_453, plain, (![A_152, G_148, H_147, B_146, F_151, C_153, E_150, C_149, D_154]: (k2_xboole_0(k4_enumset1(A_152, B_146, C_149, D_154, E_150, F_151), k2_xboole_0(k2_tarski(G_148, H_147), C_153))=k2_xboole_0(k6_enumset1(A_152, B_146, C_149, D_154, E_150, F_151, G_148, H_147), C_153))), inference(superposition, [status(thm), theory('equality')], [c_209, c_2])).
% 2.77/1.43  tff(c_474, plain, (![A_152, A_24, B_25, C_26, B_146, F_151, E_150, C_149, D_154]: (k2_xboole_0(k6_enumset1(A_152, B_146, C_149, D_154, E_150, F_151, A_24, B_25), k1_tarski(C_26))=k2_xboole_0(k4_enumset1(A_152, B_146, C_149, D_154, E_150, F_151), k1_enumset1(A_24, B_25, C_26)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_453])).
% 2.77/1.43  tff(c_478, plain, (![A_152, A_24, B_25, C_26, B_146, F_151, E_150, C_149, D_154]: (k2_xboole_0(k6_enumset1(A_152, B_146, C_149, D_154, E_150, F_151, A_24, B_25), k1_tarski(C_26))=k7_enumset1(A_152, B_146, C_149, D_154, E_150, F_151, A_24, B_25, C_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_474])).
% 2.77/1.43  tff(c_18, plain, (k2_xboole_0(k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.43  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_478, c_18])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 113
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 0
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 0
% 2.77/1.43  #Demod        : 90
% 2.77/1.43  #Tautology    : 83
% 2.77/1.43  #SimpNegUnit  : 0
% 2.77/1.43  #BackRed      : 3
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.32
% 2.77/1.43  Parsing              : 0.16
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.30
% 2.77/1.43  Inferencing          : 0.13
% 2.77/1.43  Reduction            : 0.11
% 2.77/1.43  Demodulation         : 0.09
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.03
% 2.77/1.43  Abstraction          : 0.03
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.64
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

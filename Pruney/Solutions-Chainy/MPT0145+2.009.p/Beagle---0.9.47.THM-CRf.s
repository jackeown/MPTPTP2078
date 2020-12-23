%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_14,plain,(
    ! [A_21,B_22,D_24,C_23,G_27,F_26,E_25] : k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k2_enumset1(D_24,E_25,F_26,G_27)) = k5_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k1_tarski(D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [C_43,A_45,E_46,D_42,B_44,F_47] : k2_xboole_0(k1_enumset1(A_45,B_44,C_43),k1_enumset1(D_42,E_46,F_47)) = k4_enumset1(A_45,B_44,C_43,D_42,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_543,plain,(
    ! [C_137,B_140,A_138,F_142,C_141,E_136,D_139] : k2_xboole_0(k1_enumset1(A_138,B_140,C_137),k2_xboole_0(k1_enumset1(D_139,E_136,F_142),C_141)) = k2_xboole_0(k4_enumset1(A_138,B_140,C_137,D_139,E_136,F_142),C_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_579,plain,(
    ! [C_137,B_140,A_138,D_20,C_19,B_18,A_17] : k2_xboole_0(k4_enumset1(A_138,B_140,C_137,A_17,B_18,C_19),k1_tarski(D_20)) = k2_xboole_0(k1_enumset1(A_138,B_140,C_137),k2_enumset1(A_17,B_18,C_19,D_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_543])).

tff(c_584,plain,(
    ! [C_137,B_140,A_138,D_20,C_19,B_18,A_17] : k2_xboole_0(k4_enumset1(A_138,B_140,C_137,A_17,B_18,C_19),k1_tarski(D_20)) = k5_enumset1(A_138,B_140,C_137,A_17,B_18,C_19,D_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_579])).

tff(c_16,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.38  
% 2.77/1.39  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.77/1.39  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.77/1.39  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.77/1.39  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.77/1.39  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.77/1.39  tff(c_14, plain, (![A_21, B_22, D_24, C_23, G_27, F_26, E_25]: (k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k2_enumset1(D_24, E_25, F_26, G_27))=k5_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.39  tff(c_12, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k1_tarski(D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.39  tff(c_85, plain, (![C_43, A_45, E_46, D_42, B_44, F_47]: (k2_xboole_0(k1_enumset1(A_45, B_44, C_43), k1_enumset1(D_42, E_46, F_47))=k4_enumset1(A_45, B_44, C_43, D_42, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.39  tff(c_543, plain, (![C_137, B_140, A_138, F_142, C_141, E_136, D_139]: (k2_xboole_0(k1_enumset1(A_138, B_140, C_137), k2_xboole_0(k1_enumset1(D_139, E_136, F_142), C_141))=k2_xboole_0(k4_enumset1(A_138, B_140, C_137, D_139, E_136, F_142), C_141))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 2.77/1.39  tff(c_579, plain, (![C_137, B_140, A_138, D_20, C_19, B_18, A_17]: (k2_xboole_0(k4_enumset1(A_138, B_140, C_137, A_17, B_18, C_19), k1_tarski(D_20))=k2_xboole_0(k1_enumset1(A_138, B_140, C_137), k2_enumset1(A_17, B_18, C_19, D_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_543])).
% 2.77/1.39  tff(c_584, plain, (![C_137, B_140, A_138, D_20, C_19, B_18, A_17]: (k2_xboole_0(k4_enumset1(A_138, B_140, C_137, A_17, B_18, C_19), k1_tarski(D_20))=k5_enumset1(A_138, B_140, C_137, A_17, B_18, C_19, D_20))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_579])).
% 2.77/1.39  tff(c_16, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.39  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_16])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 149
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 0
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 0
% 2.77/1.39  #Demod        : 75
% 2.77/1.39  #Tautology    : 71
% 2.77/1.39  #SimpNegUnit  : 0
% 2.77/1.39  #BackRed      : 4
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.28
% 2.77/1.39  Parsing              : 0.16
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.39  Main loop            : 0.35
% 2.77/1.39  Inferencing          : 0.16
% 2.77/1.39  Reduction            : 0.12
% 2.77/1.39  Demodulation         : 0.10
% 2.77/1.39  BG Simplification    : 0.03
% 2.77/1.39  Subsumption          : 0.04
% 2.77/1.39  Abstraction          : 0.03
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.66
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

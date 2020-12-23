%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_14,plain,(
    ! [A_23,B_24,F_28,D_26,G_29,C_25,H_30,E_27] : k2_xboole_0(k1_tarski(A_23),k5_enumset1(B_24,C_25,D_26,E_27,F_28,G_29,H_30)) = k6_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,G_29,H_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_6] : k2_xboole_0(k2_enumset1(A_6,B_7,C_8,D_9),k1_enumset1(E_10,F_11,G_12)) = k5_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_44,E_46,C_45,D_47,B_48] : k2_xboole_0(k1_tarski(A_44),k2_enumset1(B_48,C_45,D_47,E_46)) = k3_enumset1(A_44,B_48,C_45,D_47,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [C_85,C_81,B_83,E_80,A_84,D_82] : k2_xboole_0(k1_tarski(A_84),k2_xboole_0(k2_enumset1(B_83,C_81,D_82,E_80),C_85)) = k2_xboole_0(k3_enumset1(A_84,B_83,C_81,D_82,E_80),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_248,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_84,A_6] : k2_xboole_0(k3_enumset1(A_84,A_6,B_7,C_8,D_9),k1_enumset1(E_10,F_11,G_12)) = k2_xboole_0(k1_tarski(A_84),k5_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_480,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_84,A_6] : k2_xboole_0(k3_enumset1(A_84,A_6,B_7,C_8,D_9),k1_enumset1(E_10,F_11,G_12)) = k6_enumset1(A_84,A_6,B_7,C_8,D_9,E_10,F_11,G_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_16,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:23:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.89  
% 3.39/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.90  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.39/1.90  
% 3.39/1.90  %Foreground sorts:
% 3.39/1.90  
% 3.39/1.90  
% 3.39/1.90  %Background operators:
% 3.39/1.90  
% 3.39/1.90  
% 3.39/1.90  %Foreground operators:
% 3.39/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.90  tff('#skF_7', type, '#skF_7': $i).
% 3.39/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.90  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.90  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.90  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.90  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.90  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.90  tff('#skF_8', type, '#skF_8': $i).
% 3.39/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.90  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.90  
% 3.39/1.91  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.39/1.91  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.39/1.91  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.39/1.91  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.39/1.91  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 3.39/1.91  tff(c_14, plain, (![A_23, B_24, F_28, D_26, G_29, C_25, H_30, E_27]: (k2_xboole_0(k1_tarski(A_23), k5_enumset1(B_24, C_25, D_26, E_27, F_28, G_29, H_30))=k6_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, G_29, H_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.39/1.91  tff(c_6, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_6]: (k2_xboole_0(k2_enumset1(A_6, B_7, C_8, D_9), k1_enumset1(E_10, F_11, G_12))=k5_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.91  tff(c_93, plain, (![A_44, E_46, C_45, D_47, B_48]: (k2_xboole_0(k1_tarski(A_44), k2_enumset1(B_48, C_45, D_47, E_46))=k3_enumset1(A_44, B_48, C_45, D_47, E_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.91  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.91  tff(c_230, plain, (![C_85, C_81, B_83, E_80, A_84, D_82]: (k2_xboole_0(k1_tarski(A_84), k2_xboole_0(k2_enumset1(B_83, C_81, D_82, E_80), C_85))=k2_xboole_0(k3_enumset1(A_84, B_83, C_81, D_82, E_80), C_85))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 3.39/1.91  tff(c_248, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_84, A_6]: (k2_xboole_0(k3_enumset1(A_84, A_6, B_7, C_8, D_9), k1_enumset1(E_10, F_11, G_12))=k2_xboole_0(k1_tarski(A_84), k5_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_230])).
% 3.39/1.91  tff(c_480, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_84, A_6]: (k2_xboole_0(k3_enumset1(A_84, A_6, B_7, C_8, D_9), k1_enumset1(E_10, F_11, G_12))=k6_enumset1(A_84, A_6, B_7, C_8, D_9, E_10, F_11, G_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_248])).
% 3.39/1.91  tff(c_16, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.91  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_480, c_16])).
% 3.39/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.91  
% 3.39/1.91  Inference rules
% 3.39/1.91  ----------------------
% 3.39/1.91  #Ref     : 0
% 3.39/1.91  #Sup     : 116
% 3.39/1.91  #Fact    : 0
% 3.39/1.91  #Define  : 0
% 3.39/1.91  #Split   : 0
% 3.39/1.91  #Chain   : 0
% 3.39/1.91  #Close   : 0
% 3.39/1.91  
% 3.39/1.91  Ordering : KBO
% 3.39/1.91  
% 3.39/1.91  Simplification rules
% 3.39/1.91  ----------------------
% 3.39/1.91  #Subsume      : 0
% 3.39/1.91  #Demod        : 94
% 3.39/1.91  #Tautology    : 75
% 3.39/1.91  #SimpNegUnit  : 0
% 3.39/1.91  #BackRed      : 1
% 3.39/1.91  
% 3.39/1.91  #Partial instantiations: 0
% 3.39/1.91  #Strategies tried      : 1
% 3.39/1.91  
% 3.39/1.91  Timing (in seconds)
% 3.39/1.91  ----------------------
% 3.39/1.92  Preprocessing        : 0.45
% 3.39/1.92  Parsing              : 0.25
% 3.39/1.92  CNF conversion       : 0.03
% 3.39/1.92  Main loop            : 0.58
% 3.39/1.92  Inferencing          : 0.25
% 3.39/1.92  Reduction            : 0.21
% 3.39/1.92  Demodulation         : 0.17
% 3.39/1.92  BG Simplification    : 0.04
% 3.39/1.92  Subsumption          : 0.06
% 3.39/1.92  Abstraction          : 0.05
% 3.39/1.92  MUC search           : 0.00
% 3.39/1.92  Cooper               : 0.00
% 3.39/1.92  Total                : 1.07
% 3.39/1.92  Index Insertion      : 0.00
% 3.39/1.92  Index Deletion       : 0.00
% 3.39/1.92  Index Matching       : 0.00
% 3.39/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------

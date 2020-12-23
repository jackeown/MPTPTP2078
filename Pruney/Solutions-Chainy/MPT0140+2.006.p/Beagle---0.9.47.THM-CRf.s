%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:47 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_6] : k2_xboole_0(k2_enumset1(A_6,B_7,C_8,D_9),k1_enumset1(E_10,F_11,G_12)) = k5_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_44,B_45,C_46,D_47] : k2_xboole_0(k1_tarski(A_44),k1_enumset1(B_45,C_46,D_47)) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_232,plain,(
    ! [A_85,C_86,B_84,C_83,D_82] : k2_xboole_0(k1_tarski(A_85),k2_xboole_0(k1_enumset1(B_84,C_83,D_82),C_86)) = k2_xboole_0(k2_enumset1(A_85,B_84,C_83,D_82),C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2])).

tff(c_250,plain,(
    ! [A_85,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k2_enumset1(A_85,A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k2_xboole_0(k1_tarski(A_85),k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_232])).

tff(c_615,plain,(
    ! [A_85,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_85),k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27)) = k5_enumset1(A_85,A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_250])).

tff(c_18,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.46  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.02/1.46  
% 3.02/1.46  %Foreground sorts:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Background operators:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Foreground operators:
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.46  
% 3.02/1.47  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.02/1.47  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 3.02/1.47  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.02/1.47  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.02/1.47  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 3.02/1.47  tff(c_6, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_6]: (k2_xboole_0(k2_enumset1(A_6, B_7, C_8, D_9), k1_enumset1(E_10, F_11, G_12))=k5_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.47  tff(c_14, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.47  tff(c_75, plain, (![A_44, B_45, C_46, D_47]: (k2_xboole_0(k1_tarski(A_44), k1_enumset1(B_45, C_46, D_47))=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.47  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.47  tff(c_232, plain, (![A_85, C_86, B_84, C_83, D_82]: (k2_xboole_0(k1_tarski(A_85), k2_xboole_0(k1_enumset1(B_84, C_83, D_82), C_86))=k2_xboole_0(k2_enumset1(A_85, B_84, C_83, D_82), C_86))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2])).
% 3.02/1.47  tff(c_250, plain, (![A_85, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k2_enumset1(A_85, A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k2_xboole_0(k1_tarski(A_85), k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_232])).
% 3.02/1.47  tff(c_615, plain, (![A_85, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_85), k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))=k5_enumset1(A_85, A_22, B_23, C_24, D_25, E_26, F_27))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_250])).
% 3.02/1.47  tff(c_18, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.02/1.47  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_18])).
% 3.02/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  Inference rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Ref     : 0
% 3.02/1.47  #Sup     : 158
% 3.02/1.47  #Fact    : 0
% 3.02/1.47  #Define  : 0
% 3.02/1.47  #Split   : 0
% 3.02/1.47  #Chain   : 0
% 3.02/1.47  #Close   : 0
% 3.02/1.47  
% 3.02/1.47  Ordering : KBO
% 3.02/1.47  
% 3.02/1.47  Simplification rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Subsume      : 0
% 3.02/1.47  #Demod        : 85
% 3.02/1.47  #Tautology    : 78
% 3.02/1.47  #SimpNegUnit  : 0
% 3.02/1.47  #BackRed      : 1
% 3.02/1.47  
% 3.02/1.47  #Partial instantiations: 0
% 3.02/1.47  #Strategies tried      : 1
% 3.02/1.47  
% 3.02/1.47  Timing (in seconds)
% 3.02/1.47  ----------------------
% 3.02/1.48  Preprocessing        : 0.29
% 3.02/1.48  Parsing              : 0.16
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.41
% 3.02/1.48  Inferencing          : 0.18
% 3.02/1.48  Reduction            : 0.13
% 3.02/1.48  Demodulation         : 0.11
% 3.02/1.48  BG Simplification    : 0.03
% 3.02/1.48  Subsumption          : 0.05
% 3.17/1.48  Abstraction          : 0.03
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.72
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.42s
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
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_14,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k1_tarski(A_19),k4_enumset1(B_20,C_21,D_22,E_23,F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_xboole_0(A_32,B_33),C_34) = k2_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k1_tarski(A_44),k2_xboole_0(k1_tarski(B_45),C_46)) = k2_xboole_0(k2_tarski(A_44,B_45),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_133,plain,(
    ! [E_17,F_18,A_13,B_14,A_44,C_15,D_16] : k2_xboole_0(k2_tarski(A_44,A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k2_xboole_0(k1_tarski(A_44),k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_2331,plain,(
    ! [E_17,F_18,A_13,B_14,A_44,C_15,D_16] : k2_xboole_0(k2_tarski(A_44,A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k5_enumset1(A_44,A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.79  
% 4.42/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.80  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.42/1.80  
% 4.42/1.80  %Foreground sorts:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Background operators:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Foreground operators:
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.42/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.42/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  
% 4.42/1.80  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 4.42/1.80  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 4.42/1.80  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.42/1.80  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.42/1.80  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 4.42/1.80  tff(c_14, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k1_tarski(A_19), k4_enumset1(B_20, C_21, D_22, E_23, F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.80  tff(c_12, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.42/1.80  tff(c_10, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.42/1.80  tff(c_44, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_xboole_0(A_32, B_33), C_34)=k2_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.42/1.80  tff(c_115, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k1_tarski(A_44), k2_xboole_0(k1_tarski(B_45), C_46))=k2_xboole_0(k2_tarski(A_44, B_45), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 4.42/1.80  tff(c_133, plain, (![E_17, F_18, A_13, B_14, A_44, C_15, D_16]: (k2_xboole_0(k2_tarski(A_44, A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k2_xboole_0(k1_tarski(A_44), k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 4.42/1.80  tff(c_2331, plain, (![E_17, F_18, A_13, B_14, A_44, C_15, D_16]: (k2_xboole_0(k2_tarski(A_44, A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k5_enumset1(A_44, A_13, B_14, C_15, D_16, E_17, F_18))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 4.42/1.80  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.42/1.80  tff(c_2334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2331, c_16])).
% 4.42/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.80  
% 4.42/1.80  Inference rules
% 4.42/1.80  ----------------------
% 4.42/1.80  #Ref     : 0
% 4.42/1.80  #Sup     : 565
% 4.42/1.80  #Fact    : 0
% 4.42/1.80  #Define  : 0
% 4.42/1.80  #Split   : 0
% 4.42/1.80  #Chain   : 0
% 4.42/1.80  #Close   : 0
% 4.42/1.80  
% 4.42/1.80  Ordering : KBO
% 4.42/1.80  
% 4.42/1.80  Simplification rules
% 4.42/1.80  ----------------------
% 4.42/1.80  #Subsume      : 0
% 4.42/1.80  #Demod        : 1052
% 4.42/1.80  #Tautology    : 273
% 4.42/1.80  #SimpNegUnit  : 0
% 4.42/1.80  #BackRed      : 1
% 4.42/1.80  
% 4.42/1.80  #Partial instantiations: 0
% 4.42/1.80  #Strategies tried      : 1
% 4.42/1.80  
% 4.42/1.80  Timing (in seconds)
% 4.42/1.80  ----------------------
% 4.42/1.81  Preprocessing        : 0.26
% 4.42/1.81  Parsing              : 0.14
% 4.42/1.81  CNF conversion       : 0.02
% 4.42/1.81  Main loop            : 0.80
% 4.42/1.81  Inferencing          : 0.29
% 4.42/1.81  Reduction            : 0.35
% 4.42/1.81  Demodulation         : 0.31
% 4.42/1.81  BG Simplification    : 0.06
% 4.42/1.81  Subsumption          : 0.07
% 4.42/1.81  Abstraction          : 0.07
% 4.42/1.81  MUC search           : 0.00
% 4.42/1.81  Cooper               : 0.00
% 4.42/1.81  Total                : 1.09
% 4.42/1.81  Index Insertion      : 0.00
% 4.42/1.81  Index Deletion       : 0.00
% 4.42/1.81  Index Matching       : 0.00
% 4.42/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

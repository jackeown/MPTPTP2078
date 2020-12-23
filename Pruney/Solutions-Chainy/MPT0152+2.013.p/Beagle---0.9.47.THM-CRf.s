%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_10,plain,(
    ! [C_22,H_27,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k5_enumset1(B_21,C_22,D_23,E_24,F_25,G_26,H_27)) = k6_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26,H_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18),k1_tarski(G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [B_36,A_37,G_33,F_39,D_34,E_38,C_35] : k2_xboole_0(k1_tarski(A_37),k4_enumset1(B_36,C_35,D_34,E_38,F_39,G_33)) = k5_enumset1(A_37,B_36,C_35,D_34,E_38,F_39,G_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [D_63,C_68,C_65,F_66,B_69,A_64,G_70,E_67] : k2_xboole_0(k1_tarski(A_64),k2_xboole_0(k4_enumset1(B_69,C_65,D_63,E_67,F_66,G_70),C_68)) = k2_xboole_0(k5_enumset1(A_64,B_69,C_65,D_63,E_67,F_66,G_70),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_112,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_64,D_16] : k2_xboole_0(k5_enumset1(A_64,A_13,B_14,C_15,D_16,E_17,F_18),k1_tarski(G_19)) = k2_xboole_0(k1_tarski(A_64),k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_116,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_64,D_16] : k2_xboole_0(k5_enumset1(A_64,A_13,B_14,C_15,D_16,E_17,F_18),k1_tarski(G_19)) = k6_enumset1(A_64,A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_12,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_7', type, '#skF_7': $i).
% 1.80/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.17  tff('#skF_8', type, '#skF_8': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.17  
% 1.80/1.18  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 1.80/1.18  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 1.80/1.18  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 1.80/1.18  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.80/1.18  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 1.80/1.18  tff(c_10, plain, (![C_22, H_27, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k5_enumset1(B_21, C_22, D_23, E_24, F_25, G_26, H_27))=k6_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26, H_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.18  tff(c_8, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18), k1_tarski(G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.18  tff(c_39, plain, (![B_36, A_37, G_33, F_39, D_34, E_38, C_35]: (k2_xboole_0(k1_tarski(A_37), k4_enumset1(B_36, C_35, D_34, E_38, F_39, G_33))=k5_enumset1(A_37, B_36, C_35, D_34, E_38, F_39, G_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.18  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.18  tff(c_94, plain, (![D_63, C_68, C_65, F_66, B_69, A_64, G_70, E_67]: (k2_xboole_0(k1_tarski(A_64), k2_xboole_0(k4_enumset1(B_69, C_65, D_63, E_67, F_66, G_70), C_68))=k2_xboole_0(k5_enumset1(A_64, B_69, C_65, D_63, E_67, F_66, G_70), C_68))), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 1.80/1.18  tff(c_112, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_64, D_16]: (k2_xboole_0(k5_enumset1(A_64, A_13, B_14, C_15, D_16, E_17, F_18), k1_tarski(G_19))=k2_xboole_0(k1_tarski(A_64), k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_94])).
% 1.80/1.18  tff(c_116, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_64, D_16]: (k2_xboole_0(k5_enumset1(A_64, A_13, B_14, C_15, D_16, E_17, F_18), k1_tarski(G_19))=k6_enumset1(A_64, A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_112])).
% 1.80/1.18  tff(c_12, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.18  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_12])).
% 1.80/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  Inference rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Ref     : 0
% 1.80/1.18  #Sup     : 26
% 1.80/1.18  #Fact    : 0
% 1.80/1.18  #Define  : 0
% 1.80/1.18  #Split   : 0
% 1.80/1.18  #Chain   : 0
% 1.80/1.18  #Close   : 0
% 1.80/1.18  
% 1.80/1.18  Ordering : KBO
% 1.80/1.18  
% 1.80/1.18  Simplification rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Subsume      : 0
% 1.80/1.18  #Demod        : 14
% 1.80/1.18  #Tautology    : 18
% 1.80/1.18  #SimpNegUnit  : 0
% 1.80/1.18  #BackRed      : 1
% 1.80/1.18  
% 1.80/1.18  #Partial instantiations: 0
% 1.80/1.18  #Strategies tried      : 1
% 1.80/1.18  
% 1.80/1.18  Timing (in seconds)
% 1.80/1.18  ----------------------
% 1.80/1.18  Preprocessing        : 0.27
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.13
% 1.80/1.18  Inferencing          : 0.07
% 1.80/1.18  Reduction            : 0.04
% 1.80/1.18  Demodulation         : 0.03
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.02
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.43
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

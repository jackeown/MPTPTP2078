%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:13 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

tff(c_6,plain,(
    ! [H_20,E_17,F_18,I_21,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_tarski(A_13),k6_enumset1(B_14,C_15,D_16,E_17,F_18,G_19,H_20,I_21)) = k7_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20,I_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [G_35,H_36,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34),k2_tarski(G_35,H_36)) = k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [D_67,B_68,C_63,F_65,G_66,A_62,E_64] : k2_xboole_0(k1_tarski(A_62),k4_enumset1(B_68,C_63,D_67,E_64,F_65,G_66)) = k5_enumset1(A_62,B_68,C_63,D_67,E_64,F_65,G_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [D_116,A_121,C_122,E_123,C_120,F_119,G_118,B_117] : k2_xboole_0(k1_tarski(A_121),k2_xboole_0(k4_enumset1(B_117,C_120,D_116,E_123,F_119,G_118),C_122)) = k2_xboole_0(k5_enumset1(A_121,B_117,C_120,D_116,E_123,F_119,G_118),C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_175,plain,(
    ! [G_35,H_36,E_33,A_29,A_121,F_34,D_32,C_31,B_30] : k2_xboole_0(k5_enumset1(A_121,A_29,B_30,C_31,D_32,E_33,F_34),k2_tarski(G_35,H_36)) = k2_xboole_0(k1_tarski(A_121),k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_163])).

tff(c_179,plain,(
    ! [G_35,H_36,E_33,A_29,A_121,F_34,D_32,C_31,B_30] : k2_xboole_0(k5_enumset1(A_121,A_29,B_30,C_31,D_32,E_33,F_34),k2_tarski(G_35,H_36)) = k7_enumset1(A_121,A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_18,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.62  
% 2.49/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.62  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.49/1.62  
% 2.49/1.62  %Foreground sorts:
% 2.49/1.62  
% 2.49/1.62  
% 2.49/1.62  %Background operators:
% 2.49/1.62  
% 2.49/1.62  
% 2.49/1.62  %Foreground operators:
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.62  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.62  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.62  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.62  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.62  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff('#skF_9', type, '#skF_9': $i).
% 2.49/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  tff('#skF_8', type, '#skF_8': $i).
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.62  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.62  
% 2.49/1.64  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 2.49/1.64  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 2.49/1.64  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.49/1.64  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.49/1.64  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_enumset1)).
% 2.49/1.64  tff(c_6, plain, (![H_20, E_17, F_18, I_21, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_tarski(A_13), k6_enumset1(B_14, C_15, D_16, E_17, F_18, G_19, H_20, I_21))=k7_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20, I_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.64  tff(c_10, plain, (![G_35, H_36, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34), k2_tarski(G_35, H_36))=k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.64  tff(c_54, plain, (![D_67, B_68, C_63, F_65, G_66, A_62, E_64]: (k2_xboole_0(k1_tarski(A_62), k4_enumset1(B_68, C_63, D_67, E_64, F_65, G_66))=k5_enumset1(A_62, B_68, C_63, D_67, E_64, F_65, G_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.64  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.64  tff(c_163, plain, (![D_116, A_121, C_122, E_123, C_120, F_119, G_118, B_117]: (k2_xboole_0(k1_tarski(A_121), k2_xboole_0(k4_enumset1(B_117, C_120, D_116, E_123, F_119, G_118), C_122))=k2_xboole_0(k5_enumset1(A_121, B_117, C_120, D_116, E_123, F_119, G_118), C_122))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.49/1.64  tff(c_175, plain, (![G_35, H_36, E_33, A_29, A_121, F_34, D_32, C_31, B_30]: (k2_xboole_0(k5_enumset1(A_121, A_29, B_30, C_31, D_32, E_33, F_34), k2_tarski(G_35, H_36))=k2_xboole_0(k1_tarski(A_121), k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_163])).
% 2.49/1.64  tff(c_179, plain, (![G_35, H_36, E_33, A_29, A_121, F_34, D_32, C_31, B_30]: (k2_xboole_0(k5_enumset1(A_121, A_29, B_30, C_31, D_32, E_33, F_34), k2_tarski(G_35, H_36))=k7_enumset1(A_121, A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 2.49/1.64  tff(c_18, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.64  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_18])).
% 2.49/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.64  
% 2.49/1.64  Inference rules
% 2.49/1.64  ----------------------
% 2.49/1.64  #Ref     : 0
% 2.49/1.64  #Sup     : 48
% 2.49/1.64  #Fact    : 0
% 2.49/1.64  #Define  : 0
% 2.49/1.64  #Split   : 0
% 2.49/1.64  #Chain   : 0
% 2.49/1.64  #Close   : 0
% 2.49/1.64  
% 2.49/1.64  Ordering : KBO
% 2.49/1.64  
% 2.49/1.64  Simplification rules
% 2.49/1.64  ----------------------
% 2.49/1.64  #Subsume      : 0
% 2.49/1.64  #Demod        : 13
% 2.49/1.64  #Tautology    : 34
% 2.49/1.64  #SimpNegUnit  : 0
% 2.49/1.64  #BackRed      : 1
% 2.49/1.64  
% 2.49/1.64  #Partial instantiations: 0
% 2.49/1.64  #Strategies tried      : 1
% 2.49/1.64  
% 2.49/1.64  Timing (in seconds)
% 2.49/1.64  ----------------------
% 2.79/1.64  Preprocessing        : 0.48
% 2.79/1.64  Parsing              : 0.25
% 2.79/1.64  CNF conversion       : 0.03
% 2.79/1.64  Main loop            : 0.31
% 2.79/1.65  Inferencing          : 0.15
% 2.79/1.65  Reduction            : 0.10
% 2.79/1.65  Demodulation         : 0.08
% 2.79/1.65  BG Simplification    : 0.03
% 2.79/1.65  Subsumption          : 0.03
% 2.79/1.65  Abstraction          : 0.03
% 2.79/1.65  MUC search           : 0.00
% 2.79/1.65  Cooper               : 0.00
% 2.79/1.65  Total                : 0.84
% 2.79/1.65  Index Insertion      : 0.00
% 2.79/1.65  Index Deletion       : 0.00
% 2.79/1.65  Index Matching       : 0.00
% 2.79/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

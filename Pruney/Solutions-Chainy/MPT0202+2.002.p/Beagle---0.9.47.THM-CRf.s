%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:11 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_tarski(A,B),k5_enumset1(C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k1_tarski(A_4),k6_enumset1(B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [E_44,H_39,A_45,D_40,B_42,F_43,C_38,G_41] : k2_xboole_0(k1_tarski(A_45),k5_enumset1(B_42,C_38,D_40,E_44,F_43,G_41,H_39)) = k6_enumset1(A_45,B_42,C_38,D_40,E_44,F_43,G_41,H_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_13,B_14,C_27] : k2_xboole_0(k1_tarski(A_13),k2_xboole_0(k1_tarski(B_14),C_27)) = k2_xboole_0(k2_tarski(A_13,B_14),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_105,plain,(
    ! [E_44,H_39,A_45,A_13,D_40,B_42,F_43,C_38,G_41] : k2_xboole_0(k2_tarski(A_13,A_45),k5_enumset1(B_42,C_38,D_40,E_44,F_43,G_41,H_39)) = k2_xboole_0(k1_tarski(A_13),k6_enumset1(A_45,B_42,C_38,D_40,E_44,F_43,G_41,H_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_35])).

tff(c_153,plain,(
    ! [E_44,H_39,A_45,A_13,D_40,B_42,F_43,C_38,G_41] : k2_xboole_0(k2_tarski(A_13,A_45),k5_enumset1(B_42,C_38,D_40,E_44,F_43,G_41,H_39)) = k7_enumset1(A_13,A_45,B_42,C_38,D_40,E_44,F_43,G_41,H_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k5_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:41:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.14  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.14  tff('#skF_7', type, '#skF_7': $i).
% 1.69/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.69/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.69/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.14  tff('#skF_9', type, '#skF_9': $i).
% 1.69/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.14  tff('#skF_8', type, '#skF_8': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.69/1.14  
% 1.91/1.15  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 1.91/1.15  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 1.91/1.15  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.91/1.15  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.91/1.15  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_tarski(A, B), k5_enumset1(C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_enumset1)).
% 1.91/1.15  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k1_tarski(A_4), k6_enumset1(B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.15  tff(c_96, plain, (![E_44, H_39, A_45, D_40, B_42, F_43, C_38, G_41]: (k2_xboole_0(k1_tarski(A_45), k5_enumset1(B_42, C_38, D_40, E_44, F_43, G_41, H_39))=k6_enumset1(A_45, B_42, C_38, D_40, E_44, F_43, G_41, H_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.15  tff(c_6, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.15  tff(c_20, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.15  tff(c_35, plain, (![A_13, B_14, C_27]: (k2_xboole_0(k1_tarski(A_13), k2_xboole_0(k1_tarski(B_14), C_27))=k2_xboole_0(k2_tarski(A_13, B_14), C_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20])).
% 1.91/1.15  tff(c_105, plain, (![E_44, H_39, A_45, A_13, D_40, B_42, F_43, C_38, G_41]: (k2_xboole_0(k2_tarski(A_13, A_45), k5_enumset1(B_42, C_38, D_40, E_44, F_43, G_41, H_39))=k2_xboole_0(k1_tarski(A_13), k6_enumset1(A_45, B_42, C_38, D_40, E_44, F_43, G_41, H_39)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_35])).
% 1.91/1.15  tff(c_153, plain, (![E_44, H_39, A_45, A_13, D_40, B_42, F_43, C_38, G_41]: (k2_xboole_0(k2_tarski(A_13, A_45), k5_enumset1(B_42, C_38, D_40, E_44, F_43, G_41, H_39))=k7_enumset1(A_13, A_45, B_42, C_38, D_40, E_44, F_43, G_41, H_39))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 1.91/1.15  tff(c_10, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k5_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.15  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_10])).
% 1.91/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.15  
% 1.91/1.15  Inference rules
% 1.91/1.15  ----------------------
% 1.91/1.15  #Ref     : 0
% 1.91/1.15  #Sup     : 36
% 1.91/1.15  #Fact    : 0
% 1.91/1.15  #Define  : 0
% 1.91/1.15  #Split   : 0
% 1.91/1.15  #Chain   : 0
% 1.91/1.15  #Close   : 0
% 1.91/1.15  
% 1.91/1.15  Ordering : KBO
% 1.91/1.15  
% 1.91/1.15  Simplification rules
% 1.91/1.15  ----------------------
% 1.91/1.15  #Subsume      : 0
% 1.91/1.15  #Demod        : 25
% 1.91/1.15  #Tautology    : 25
% 1.91/1.15  #SimpNegUnit  : 0
% 1.91/1.15  #BackRed      : 1
% 1.91/1.15  
% 1.91/1.15  #Partial instantiations: 0
% 1.91/1.15  #Strategies tried      : 1
% 1.91/1.15  
% 1.91/1.15  Timing (in seconds)
% 1.91/1.15  ----------------------
% 1.91/1.15  Preprocessing        : 0.25
% 1.91/1.15  Parsing              : 0.14
% 1.91/1.15  CNF conversion       : 0.02
% 1.91/1.15  Main loop            : 0.15
% 1.91/1.15  Inferencing          : 0.07
% 1.91/1.15  Reduction            : 0.05
% 1.91/1.15  Demodulation         : 0.04
% 1.91/1.16  BG Simplification    : 0.01
% 1.91/1.16  Subsumption          : 0.02
% 1.91/1.16  Abstraction          : 0.01
% 1.91/1.16  MUC search           : 0.00
% 1.91/1.16  Cooper               : 0.00
% 1.91/1.16  Total                : 0.43
% 1.91/1.16  Index Insertion      : 0.00
% 1.91/1.16  Index Deletion       : 0.00
% 1.91/1.16  Index Matching       : 0.00
% 1.91/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

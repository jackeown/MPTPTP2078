%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_12,plain,(
    ! [A_21,B_22,H_28,D_24,C_23,G_27,F_26,E_25] : k2_xboole_0(k1_tarski(A_21),k5_enumset1(B_22,C_23,D_24,E_25,F_26,G_27,H_28)) = k6_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27,H_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [G_20,E_18,C_16,D_17,F_19,A_14,B_15] : k2_xboole_0(k3_enumset1(A_14,B_15,C_16,D_17,E_18),k2_tarski(F_19,G_20)) = k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [C_46,E_44,F_42,B_45,A_43,D_47] : k2_xboole_0(k1_tarski(A_43),k3_enumset1(B_45,C_46,D_47,E_44,F_42)) = k4_enumset1(A_43,B_45,C_46,D_47,E_44,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_159,plain,(
    ! [C_70,F_68,C_73,B_72,A_71,E_67,D_69] : k2_xboole_0(k1_tarski(A_71),k2_xboole_0(k3_enumset1(B_72,C_70,D_69,E_67,F_68),C_73)) = k2_xboole_0(k4_enumset1(A_71,B_72,C_70,D_69,E_67,F_68),C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2])).

tff(c_177,plain,(
    ! [G_20,E_18,C_16,A_71,D_17,F_19,A_14,B_15] : k2_xboole_0(k4_enumset1(A_71,A_14,B_15,C_16,D_17,E_18),k2_tarski(F_19,G_20)) = k2_xboole_0(k1_tarski(A_71),k5_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_159])).

tff(c_181,plain,(
    ! [G_20,E_18,C_16,A_71,D_17,F_19,A_14,B_15] : k2_xboole_0(k4_enumset1(A_71,A_14,B_15,C_16,D_17,E_18),k2_tarski(F_19,G_20)) = k6_enumset1(A_71,A_14,B_15,C_16,D_17,E_18,F_19,G_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_177])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff('#skF_8', type, '#skF_8': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.20  
% 1.99/1.21  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 1.99/1.21  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 1.99/1.21  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 1.99/1.21  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.99/1.21  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 1.99/1.21  tff(c_12, plain, (![A_21, B_22, H_28, D_24, C_23, G_27, F_26, E_25]: (k2_xboole_0(k1_tarski(A_21), k5_enumset1(B_22, C_23, D_24, E_25, F_26, G_27, H_28))=k6_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27, H_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.21  tff(c_10, plain, (![G_20, E_18, C_16, D_17, F_19, A_14, B_15]: (k2_xboole_0(k3_enumset1(A_14, B_15, C_16, D_17, E_18), k2_tarski(F_19, G_20))=k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.21  tff(c_88, plain, (![C_46, E_44, F_42, B_45, A_43, D_47]: (k2_xboole_0(k1_tarski(A_43), k3_enumset1(B_45, C_46, D_47, E_44, F_42))=k4_enumset1(A_43, B_45, C_46, D_47, E_44, F_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.21  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.21  tff(c_159, plain, (![C_70, F_68, C_73, B_72, A_71, E_67, D_69]: (k2_xboole_0(k1_tarski(A_71), k2_xboole_0(k3_enumset1(B_72, C_70, D_69, E_67, F_68), C_73))=k2_xboole_0(k4_enumset1(A_71, B_72, C_70, D_69, E_67, F_68), C_73))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2])).
% 1.99/1.21  tff(c_177, plain, (![G_20, E_18, C_16, A_71, D_17, F_19, A_14, B_15]: (k2_xboole_0(k4_enumset1(A_71, A_14, B_15, C_16, D_17, E_18), k2_tarski(F_19, G_20))=k2_xboole_0(k1_tarski(A_71), k5_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_159])).
% 1.99/1.21  tff(c_181, plain, (![G_20, E_18, C_16, A_71, D_17, F_19, A_14, B_15]: (k2_xboole_0(k4_enumset1(A_71, A_14, B_15, C_16, D_17, E_18), k2_tarski(F_19, G_20))=k6_enumset1(A_71, A_14, B_15, C_16, D_17, E_18, F_19, G_20))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_177])).
% 1.99/1.21  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.21  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_14])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 45
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 0
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 0
% 1.99/1.21  #Demod        : 26
% 1.99/1.21  #Tautology    : 31
% 1.99/1.21  #SimpNegUnit  : 0
% 1.99/1.21  #BackRed      : 1
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.21  Preprocessing        : 0.26
% 1.99/1.21  Parsing              : 0.15
% 1.99/1.21  CNF conversion       : 0.02
% 1.99/1.21  Main loop            : 0.17
% 1.99/1.21  Inferencing          : 0.08
% 1.99/1.21  Reduction            : 0.06
% 1.99/1.21  Demodulation         : 0.05
% 1.99/1.21  BG Simplification    : 0.01
% 1.99/1.21  Subsumption          : 0.02
% 1.99/1.21  Abstraction          : 0.01
% 1.99/1.21  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.46
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:47:11 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k3_enumset1(E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42] : k2_xboole_0(k1_enumset1(A_38,B_39,C_37),k3_enumset1(D_41,E_42,F_40,G_43,H_44)) = k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_tarski(A_28),k1_enumset1(B_29,C_30,D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [C_30,C_3,D_31,B_29,A_28] : k2_xboole_0(k1_tarski(A_28),k2_xboole_0(k1_enumset1(B_29,C_30,D_31),C_3)) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_59,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42,A_28] : k2_xboole_0(k2_enumset1(A_28,A_38,B_39,C_37),k3_enumset1(D_41,E_42,F_40,G_43,H_44)) = k2_xboole_0(k1_tarski(A_28),k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_34])).

tff(c_96,plain,(
    ! [D_41,F_40,B_39,C_37,G_43,A_38,H_44,E_42,A_28] : k2_xboole_0(k1_tarski(A_28),k6_enumset1(A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44)) = k7_enumset1(A_28,A_38,B_39,C_37,D_41,E_42,F_40,G_43,H_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k6_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  %$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 1.68/1.11  
% 1.68/1.11  %Foreground sorts:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Background operators:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Foreground operators:
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.68/1.11  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.68/1.11  tff('#skF_7', type, '#skF_7': $i).
% 1.68/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.11  tff('#skF_6', type, '#skF_6': $i).
% 1.68/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.11  tff('#skF_9', type, '#skF_9': $i).
% 1.68/1.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.68/1.11  tff('#skF_8', type, '#skF_8': $i).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.11  
% 1.68/1.12  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 1.68/1.12  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 1.68/1.12  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.68/1.12  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.68/1.12  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 1.68/1.12  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k3_enumset1(E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.12  tff(c_53, plain, (![D_41, F_40, B_39, C_37, G_43, A_38, H_44, E_42]: (k2_xboole_0(k1_enumset1(A_38, B_39, C_37), k3_enumset1(D_41, E_42, F_40, G_43, H_44))=k6_enumset1(A_38, B_39, C_37, D_41, E_42, F_40, G_43, H_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.12  tff(c_28, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_tarski(A_28), k1_enumset1(B_29, C_30, D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.12  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.12  tff(c_34, plain, (![C_30, C_3, D_31, B_29, A_28]: (k2_xboole_0(k1_tarski(A_28), k2_xboole_0(k1_enumset1(B_29, C_30, D_31), C_3))=k2_xboole_0(k2_enumset1(A_28, B_29, C_30, D_31), C_3))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 1.68/1.12  tff(c_59, plain, (![D_41, F_40, B_39, C_37, G_43, A_38, H_44, E_42, A_28]: (k2_xboole_0(k2_enumset1(A_28, A_38, B_39, C_37), k3_enumset1(D_41, E_42, F_40, G_43, H_44))=k2_xboole_0(k1_tarski(A_28), k6_enumset1(A_38, B_39, C_37, D_41, E_42, F_40, G_43, H_44)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_34])).
% 1.68/1.12  tff(c_96, plain, (![D_41, F_40, B_39, C_37, G_43, A_38, H_44, E_42, A_28]: (k2_xboole_0(k1_tarski(A_28), k6_enumset1(A_38, B_39, C_37, D_41, E_42, F_40, G_43, H_44))=k7_enumset1(A_28, A_38, B_39, C_37, D_41, E_42, F_40, G_43, H_44))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 1.68/1.12  tff(c_10, plain, (k2_xboole_0(k1_tarski('#skF_1'), k6_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.12  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_10])).
% 1.68/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  Inference rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Ref     : 0
% 1.68/1.12  #Sup     : 21
% 1.68/1.12  #Fact    : 0
% 1.68/1.12  #Define  : 0
% 1.68/1.12  #Split   : 0
% 1.68/1.12  #Chain   : 0
% 1.68/1.12  #Close   : 0
% 1.68/1.12  
% 1.68/1.12  Ordering : KBO
% 1.68/1.12  
% 1.68/1.12  Simplification rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Subsume      : 0
% 1.68/1.12  #Demod        : 14
% 1.68/1.12  #Tautology    : 16
% 1.68/1.12  #SimpNegUnit  : 0
% 1.68/1.12  #BackRed      : 1
% 1.68/1.12  
% 1.68/1.12  #Partial instantiations: 0
% 1.68/1.12  #Strategies tried      : 1
% 1.68/1.12  
% 1.68/1.12  Timing (in seconds)
% 1.68/1.12  ----------------------
% 1.68/1.12  Preprocessing        : 0.26
% 1.68/1.12  Parsing              : 0.14
% 1.68/1.12  CNF conversion       : 0.02
% 1.68/1.12  Main loop            : 0.12
% 1.68/1.12  Inferencing          : 0.06
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.03
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.01
% 1.68/1.12  Abstraction          : 0.01
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.40
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

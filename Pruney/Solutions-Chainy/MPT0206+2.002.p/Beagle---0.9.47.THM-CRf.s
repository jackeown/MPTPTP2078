%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:12 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

tff(c_6,plain,(
    ! [H_20,E_17,F_18,I_21,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k4_enumset1(D_16,E_17,F_18,G_19,H_20,I_21)) = k7_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20,I_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_52,A_47,D_51,C_48,E_49,F_50] : k2_xboole_0(k1_enumset1(A_47,B_52,C_48),k1_enumset1(D_51,E_49,F_50)) = k4_enumset1(A_47,B_52,C_48,D_51,E_49,F_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [D_55,C_56,A_53,E_57,F_59,C_58,B_54] : k2_xboole_0(k1_enumset1(A_53,B_54,C_56),k2_xboole_0(k1_enumset1(D_55,E_57,F_59),C_58)) = k2_xboole_0(k4_enumset1(A_53,B_54,C_56,D_55,E_57,F_59),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_80,plain,(
    ! [E_26,C_56,F_27,A_53,A_22,B_23,B_54,D_25,C_24] : k2_xboole_0(k4_enumset1(A_53,B_54,C_56,A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k2_xboole_0(k1_enumset1(A_53,B_54,C_56),k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_390,plain,(
    ! [E_26,C_56,F_27,A_53,A_22,B_23,B_54,D_25,C_24] : k2_xboole_0(k4_enumset1(A_53,B_54,C_56,A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k7_enumset1(A_53,B_54,C_56,A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_enumset1('#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.37  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.63/1.37  
% 2.63/1.37  %Foreground sorts:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Background operators:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Foreground operators:
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.37  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.63/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.37  
% 2.63/1.38  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_enumset1)).
% 2.63/1.38  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 2.63/1.38  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.63/1.38  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 2.63/1.38  tff(c_6, plain, (![H_20, E_17, F_18, I_21, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k4_enumset1(D_16, E_17, F_18, G_19, H_20, I_21))=k7_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20, I_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.38  tff(c_8, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.38  tff(c_50, plain, (![B_52, A_47, D_51, C_48, E_49, F_50]: (k2_xboole_0(k1_enumset1(A_47, B_52, C_48), k1_enumset1(D_51, E_49, F_50))=k4_enumset1(A_47, B_52, C_48, D_51, E_49, F_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.38  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.38  tff(c_62, plain, (![D_55, C_56, A_53, E_57, F_59, C_58, B_54]: (k2_xboole_0(k1_enumset1(A_53, B_54, C_56), k2_xboole_0(k1_enumset1(D_55, E_57, F_59), C_58))=k2_xboole_0(k4_enumset1(A_53, B_54, C_56, D_55, E_57, F_59), C_58))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2])).
% 2.63/1.38  tff(c_80, plain, (![E_26, C_56, F_27, A_53, A_22, B_23, B_54, D_25, C_24]: (k2_xboole_0(k4_enumset1(A_53, B_54, C_56, A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k2_xboole_0(k1_enumset1(A_53, B_54, C_56), k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 2.63/1.38  tff(c_390, plain, (![E_26, C_56, F_27, A_53, A_22, B_23, B_54, D_25, C_24]: (k2_xboole_0(k4_enumset1(A_53, B_54, C_56, A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k7_enumset1(A_53, B_54, C_56, A_22, B_23, C_24, D_25, E_26, F_27))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80])).
% 2.63/1.38  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_enumset1('#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.38  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_14])).
% 2.63/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  Inference rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Ref     : 0
% 2.63/1.38  #Sup     : 98
% 2.63/1.38  #Fact    : 0
% 2.63/1.38  #Define  : 0
% 2.63/1.38  #Split   : 0
% 2.63/1.38  #Chain   : 0
% 2.63/1.38  #Close   : 0
% 2.63/1.38  
% 2.63/1.38  Ordering : KBO
% 2.63/1.38  
% 2.63/1.38  Simplification rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Subsume      : 21
% 2.63/1.38  #Demod        : 14
% 2.63/1.38  #Tautology    : 40
% 2.63/1.38  #SimpNegUnit  : 0
% 2.63/1.38  #BackRed      : 1
% 2.63/1.38  
% 2.63/1.38  #Partial instantiations: 0
% 2.63/1.38  #Strategies tried      : 1
% 2.63/1.38  
% 2.63/1.38  Timing (in seconds)
% 2.63/1.38  ----------------------
% 2.63/1.38  Preprocessing        : 0.29
% 2.63/1.38  Parsing              : 0.15
% 2.63/1.38  CNF conversion       : 0.02
% 2.63/1.38  Main loop            : 0.33
% 2.63/1.38  Inferencing          : 0.16
% 2.63/1.38  Reduction            : 0.11
% 2.63/1.38  Demodulation         : 0.10
% 2.63/1.38  BG Simplification    : 0.02
% 2.63/1.38  Subsumption          : 0.04
% 2.63/1.38  Abstraction          : 0.03
% 2.63/1.38  MUC search           : 0.00
% 2.63/1.38  Cooper               : 0.00
% 2.63/1.38  Total                : 0.64
% 2.63/1.38  Index Insertion      : 0.00
% 2.63/1.38  Index Deletion       : 0.00
% 2.63/1.38  Index Matching       : 0.00
% 2.63/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

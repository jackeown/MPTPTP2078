%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:49 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.18s
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
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_14,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [A_59,F_56,B_57,E_58,C_61,D_60] : k2_xboole_0(k1_tarski(A_59),k3_enumset1(B_57,C_61,D_60,E_58,F_56)) = k4_enumset1(A_59,B_57,C_61,D_60,E_58,F_56) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k2_xboole_0(A_36,B_37),C_38) = k2_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_9,B_10,C_38] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_38)) = k2_xboole_0(k2_tarski(A_9,B_10),C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_177,plain,(
    ! [A_59,F_56,B_57,E_58,C_61,D_60,A_9] : k2_xboole_0(k2_tarski(A_9,A_59),k3_enumset1(B_57,C_61,D_60,E_58,F_56)) = k2_xboole_0(k1_tarski(A_9),k4_enumset1(A_59,B_57,C_61,D_60,E_58,F_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_70])).

tff(c_452,plain,(
    ! [A_59,F_56,B_57,E_58,C_61,D_60,A_9] : k2_xboole_0(k2_tarski(A_9,A_59),k3_enumset1(B_57,C_61,D_60,E_58,F_56)) = k5_enumset1(A_9,A_59,B_57,C_61,D_60,E_58,F_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.83  
% 3.18/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.83  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.83  
% 3.18/1.83  %Foreground sorts:
% 3.18/1.83  
% 3.18/1.83  
% 3.18/1.83  %Background operators:
% 3.18/1.83  
% 3.18/1.83  
% 3.18/1.83  %Foreground operators:
% 3.18/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.83  tff('#skF_7', type, '#skF_7': $i).
% 3.18/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.83  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.83  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.83  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.83  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.83  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.83  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.83  
% 3.18/1.84  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 3.18/1.84  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.18/1.84  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.18/1.84  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.18/1.84  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 3.18/1.84  tff(c_14, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.84  tff(c_171, plain, (![A_59, F_56, B_57, E_58, C_61, D_60]: (k2_xboole_0(k1_tarski(A_59), k3_enumset1(B_57, C_61, D_60, E_58, F_56))=k4_enumset1(A_59, B_57, C_61, D_60, E_58, F_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.84  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.84  tff(c_55, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k2_xboole_0(A_36, B_37), C_38)=k2_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.84  tff(c_70, plain, (![A_9, B_10, C_38]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_38))=k2_xboole_0(k2_tarski(A_9, B_10), C_38))), inference(superposition, [status(thm), theory('equality')], [c_8, c_55])).
% 3.18/1.84  tff(c_177, plain, (![A_59, F_56, B_57, E_58, C_61, D_60, A_9]: (k2_xboole_0(k2_tarski(A_9, A_59), k3_enumset1(B_57, C_61, D_60, E_58, F_56))=k2_xboole_0(k1_tarski(A_9), k4_enumset1(A_59, B_57, C_61, D_60, E_58, F_56)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_70])).
% 3.18/1.84  tff(c_452, plain, (![A_59, F_56, B_57, E_58, C_61, D_60, A_9]: (k2_xboole_0(k2_tarski(A_9, A_59), k3_enumset1(B_57, C_61, D_60, E_58, F_56))=k5_enumset1(A_9, A_59, B_57, C_61, D_60, E_58, F_56))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_177])).
% 3.18/1.84  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.84  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_16])).
% 3.18/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.85  
% 3.18/1.85  Inference rules
% 3.18/1.85  ----------------------
% 3.18/1.85  #Ref     : 0
% 3.18/1.85  #Sup     : 109
% 3.18/1.85  #Fact    : 0
% 3.18/1.85  #Define  : 0
% 3.18/1.85  #Split   : 0
% 3.18/1.85  #Chain   : 0
% 3.18/1.85  #Close   : 0
% 3.18/1.85  
% 3.18/1.85  Ordering : KBO
% 3.18/1.85  
% 3.18/1.85  Simplification rules
% 3.18/1.85  ----------------------
% 3.18/1.85  #Subsume      : 0
% 3.18/1.85  #Demod        : 69
% 3.18/1.85  #Tautology    : 60
% 3.18/1.85  #SimpNegUnit  : 0
% 3.18/1.85  #BackRed      : 1
% 3.18/1.85  
% 3.18/1.85  #Partial instantiations: 0
% 3.18/1.85  #Strategies tried      : 1
% 3.18/1.85  
% 3.18/1.85  Timing (in seconds)
% 3.18/1.85  ----------------------
% 3.18/1.85  Preprocessing        : 0.43
% 3.18/1.85  Parsing              : 0.23
% 3.18/1.85  CNF conversion       : 0.03
% 3.18/1.85  Main loop            : 0.49
% 3.18/1.85  Inferencing          : 0.22
% 3.18/1.85  Reduction            : 0.16
% 3.18/1.85  Demodulation         : 0.13
% 3.18/1.85  BG Simplification    : 0.04
% 3.18/1.85  Subsumption          : 0.06
% 3.18/1.85  Abstraction          : 0.04
% 3.18/1.85  MUC search           : 0.00
% 3.18/1.85  Cooper               : 0.00
% 3.18/1.85  Total                : 0.96
% 3.18/1.85  Index Insertion      : 0.00
% 3.18/1.85  Index Deletion       : 0.00
% 3.18/1.85  Index Matching       : 0.00
% 3.18/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------

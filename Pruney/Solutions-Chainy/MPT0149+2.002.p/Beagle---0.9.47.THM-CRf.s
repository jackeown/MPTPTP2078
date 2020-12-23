%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
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
%$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

tff(c_12,plain,(
    ! [C_22,H_27,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k5_enumset1(B_21,C_22,D_23,E_24,F_25,G_26,H_27)) = k6_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26,H_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38,D_39] : k2_xboole_0(k1_tarski(A_36),k1_enumset1(B_37,C_38,D_39)) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [D_70,C_73,C_72,B_71,A_69] : k2_xboole_0(k1_tarski(A_69),k2_xboole_0(k1_enumset1(B_71,C_73,D_70),C_72)) = k2_xboole_0(k2_enumset1(A_69,B_71,C_73,D_70),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_222,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_69,D_16] : k2_xboole_0(k2_enumset1(A_69,A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k2_xboole_0(k1_tarski(A_69),k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_201])).

tff(c_556,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_69,D_16] : k2_xboole_0(k2_enumset1(A_69,A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k6_enumset1(A_69,A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_222])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:43:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  %$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.40  
% 2.74/1.40  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 2.74/1.40  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.74/1.40  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.74/1.40  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.74/1.40  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 2.74/1.40  tff(c_12, plain, (![C_22, H_27, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k5_enumset1(B_21, C_22, D_23, E_24, F_25, G_26, H_27))=k6_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26, H_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.40  tff(c_10, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.40  tff(c_56, plain, (![A_36, B_37, C_38, D_39]: (k2_xboole_0(k1_tarski(A_36), k1_enumset1(B_37, C_38, D_39))=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.40  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.40  tff(c_201, plain, (![D_70, C_73, C_72, B_71, A_69]: (k2_xboole_0(k1_tarski(A_69), k2_xboole_0(k1_enumset1(B_71, C_73, D_70), C_72))=k2_xboole_0(k2_enumset1(A_69, B_71, C_73, D_70), C_72))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.74/1.40  tff(c_222, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_69, D_16]: (k2_xboole_0(k2_enumset1(A_69, A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k2_xboole_0(k1_tarski(A_69), k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_201])).
% 2.74/1.40  tff(c_556, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_69, D_16]: (k2_xboole_0(k2_enumset1(A_69, A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k6_enumset1(A_69, A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_222])).
% 2.74/1.40  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.40  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_14])).
% 2.74/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  Inference rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Ref     : 0
% 2.74/1.40  #Sup     : 137
% 2.74/1.40  #Fact    : 0
% 2.74/1.40  #Define  : 0
% 2.74/1.40  #Split   : 0
% 2.74/1.40  #Chain   : 0
% 2.74/1.40  #Close   : 0
% 2.74/1.40  
% 2.74/1.40  Ordering : KBO
% 2.74/1.40  
% 2.74/1.40  Simplification rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Subsume      : 0
% 2.74/1.40  #Demod        : 110
% 2.74/1.40  #Tautology    : 81
% 2.74/1.40  #SimpNegUnit  : 0
% 2.74/1.40  #BackRed      : 1
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.41  Preprocessing        : 0.28
% 2.74/1.41  Parsing              : 0.16
% 2.74/1.41  CNF conversion       : 0.02
% 2.74/1.41  Main loop            : 0.35
% 2.74/1.41  Inferencing          : 0.15
% 2.74/1.41  Reduction            : 0.12
% 2.74/1.41  Demodulation         : 0.10
% 2.74/1.41  BG Simplification    : 0.02
% 2.74/1.41  Subsumption          : 0.04
% 2.74/1.41  Abstraction          : 0.03
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.65
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

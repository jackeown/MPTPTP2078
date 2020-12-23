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
% DateTime   : Thu Dec  3 09:47:13 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.98s
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
%$ k7_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,G_21,E_19,H_22,F_20,C_17,I_23] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k4_enumset1(D_18,E_19,F_20,G_21,H_22,I_23)) = k7_enumset1(A_15,B_16,C_17,D_18,E_19,F_20,G_21,H_22,I_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [D_41,F_38,B_39,E_42,A_43,C_40] : k2_xboole_0(k1_enumset1(A_43,B_39,C_40),k1_enumset1(D_41,E_42,F_38)) = k4_enumset1(A_43,B_39,C_40,D_41,E_42,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_531,plain,(
    ! [E_72,F_70,C_75,C_74,A_73,B_71,D_76] : k2_xboole_0(k1_enumset1(A_73,B_71,C_74),k2_xboole_0(k1_enumset1(D_76,E_72,F_70),C_75)) = k2_xboole_0(k4_enumset1(A_73,B_71,C_74,D_76,E_72,F_70),C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_570,plain,(
    ! [C_11,E_13,C_74,B_10,F_14,A_73,B_71,D_12,A_9] : k2_xboole_0(k4_enumset1(A_73,B_71,C_74,A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k2_xboole_0(k1_enumset1(A_73,B_71,C_74),k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_531])).

tff(c_579,plain,(
    ! [C_11,E_13,C_74,B_10,F_14,A_73,B_71,D_12,A_9] : k2_xboole_0(k4_enumset1(A_73,B_71,C_74,A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k7_enumset1(A_73,B_71,C_74,A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_570])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_enumset1('#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.81  
% 3.84/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.81  %$ k7_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.84/1.81  
% 3.84/1.81  %Foreground sorts:
% 3.84/1.81  
% 3.84/1.81  
% 3.84/1.81  %Background operators:
% 3.84/1.81  
% 3.84/1.81  
% 3.84/1.81  %Foreground operators:
% 3.84/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.81  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.84/1.81  tff('#skF_7', type, '#skF_7': $i).
% 3.84/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.84/1.81  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.81  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.84/1.81  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.81  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.81  tff('#skF_1', type, '#skF_1': $i).
% 3.84/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.84/1.81  tff('#skF_9', type, '#skF_9': $i).
% 3.84/1.81  tff('#skF_8', type, '#skF_8': $i).
% 3.84/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.81  tff('#skF_4', type, '#skF_4': $i).
% 3.84/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.84/1.81  
% 3.98/1.82  tff(f_35, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 3.98/1.82  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 3.98/1.82  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.98/1.82  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 3.98/1.82  tff(c_10, plain, (![B_16, A_15, D_18, G_21, E_19, H_22, F_20, C_17, I_23]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k4_enumset1(D_18, E_19, F_20, G_21, H_22, I_23))=k7_enumset1(A_15, B_16, C_17, D_18, E_19, F_20, G_21, H_22, I_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.98/1.82  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.82  tff(c_161, plain, (![D_41, F_38, B_39, E_42, A_43, C_40]: (k2_xboole_0(k1_enumset1(A_43, B_39, C_40), k1_enumset1(D_41, E_42, F_38))=k4_enumset1(A_43, B_39, C_40, D_41, E_42, F_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.82  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.82  tff(c_531, plain, (![E_72, F_70, C_75, C_74, A_73, B_71, D_76]: (k2_xboole_0(k1_enumset1(A_73, B_71, C_74), k2_xboole_0(k1_enumset1(D_76, E_72, F_70), C_75))=k2_xboole_0(k4_enumset1(A_73, B_71, C_74, D_76, E_72, F_70), C_75))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 3.98/1.82  tff(c_570, plain, (![C_11, E_13, C_74, B_10, F_14, A_73, B_71, D_12, A_9]: (k2_xboole_0(k4_enumset1(A_73, B_71, C_74, A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k2_xboole_0(k1_enumset1(A_73, B_71, C_74), k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_531])).
% 3.98/1.82  tff(c_579, plain, (![C_11, E_13, C_74, B_10, F_14, A_73, B_71, D_12, A_9]: (k2_xboole_0(k4_enumset1(A_73, B_71, C_74, A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k7_enumset1(A_73, B_71, C_74, A_9, B_10, C_11, D_12, E_13, F_14))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_570])).
% 3.98/1.82  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_enumset1('#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.82  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_579, c_12])).
% 3.98/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.82  
% 3.98/1.82  Inference rules
% 3.98/1.82  ----------------------
% 3.98/1.82  #Ref     : 0
% 3.98/1.82  #Sup     : 350
% 3.98/1.82  #Fact    : 0
% 3.98/1.82  #Define  : 0
% 3.98/1.82  #Split   : 0
% 3.98/1.82  #Chain   : 0
% 3.98/1.82  #Close   : 0
% 3.98/1.82  
% 3.98/1.82  Ordering : KBO
% 3.98/1.82  
% 3.98/1.82  Simplification rules
% 3.98/1.82  ----------------------
% 3.98/1.82  #Subsume      : 0
% 3.98/1.82  #Demod        : 848
% 3.98/1.82  #Tautology    : 166
% 3.98/1.82  #SimpNegUnit  : 0
% 3.98/1.82  #BackRed      : 1
% 3.98/1.82  
% 3.98/1.82  #Partial instantiations: 0
% 3.98/1.82  #Strategies tried      : 1
% 3.98/1.82  
% 3.98/1.82  Timing (in seconds)
% 3.98/1.82  ----------------------
% 3.98/1.82  Preprocessing        : 0.36
% 3.98/1.82  Parsing              : 0.21
% 3.98/1.82  CNF conversion       : 0.02
% 3.98/1.82  Main loop            : 0.63
% 3.98/1.82  Inferencing          : 0.23
% 3.98/1.82  Reduction            : 0.28
% 3.98/1.82  Demodulation         : 0.24
% 3.98/1.82  BG Simplification    : 0.04
% 3.98/1.82  Subsumption          : 0.06
% 3.98/1.83  Abstraction          : 0.06
% 3.98/1.83  MUC search           : 0.00
% 3.98/1.83  Cooper               : 0.00
% 3.98/1.83  Total                : 1.01
% 3.98/1.83  Index Insertion      : 0.00
% 3.98/1.83  Index Deletion       : 0.00
% 3.98/1.83  Index Matching       : 0.00
% 3.98/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

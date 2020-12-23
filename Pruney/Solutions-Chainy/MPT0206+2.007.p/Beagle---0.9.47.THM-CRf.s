%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:13 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,H_13,I_14,F_11,G_12,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k4_enumset1(D_9,E_10,F_11,G_12,H_13,I_14)) = k7_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12,H_13,I_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_enumset1(D_18,E_19,F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_37,D_33,E_36,C_32,B_34,F_35] : k2_xboole_0(k1_enumset1(A_37,B_34,C_32),k1_enumset1(D_33,E_36,F_35)) = k4_enumset1(A_37,B_34,C_32,D_33,E_36,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_50,D_55,F_52,C_51,B_53,C_54,E_49] : k2_xboole_0(k1_enumset1(A_50,B_53,C_51),k2_xboole_0(k1_enumset1(D_55,E_49,F_52),C_54)) = k2_xboole_0(k4_enumset1(A_50,B_53,C_51,D_55,E_49,F_52),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_137,plain,(
    ! [A_50,B_16,A_15,D_18,C_51,E_19,B_53,F_20,C_17] : k2_xboole_0(k4_enumset1(A_50,B_53,C_51,A_15,B_16,C_17),k1_enumset1(D_18,E_19,F_20)) = k2_xboole_0(k1_enumset1(A_50,B_53,C_51),k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_141,plain,(
    ! [A_50,B_16,A_15,D_18,C_51,E_19,B_53,F_20,C_17] : k2_xboole_0(k4_enumset1(A_50,B_53,C_51,A_15,B_16,C_17),k1_enumset1(D_18,E_19,F_20)) = k7_enumset1(A_50,B_53,C_51,A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_enumset1('#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.02/1.23  
% 2.02/1.23  %Foreground sorts:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Background operators:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Foreground operators:
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.23  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.23  tff('#skF_7', type, '#skF_7': $i).
% 2.02/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.23  tff('#skF_9', type, '#skF_9': $i).
% 2.02/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.23  tff('#skF_8', type, '#skF_8': $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.23  
% 2.02/1.24  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 2.02/1.24  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 2.02/1.24  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.02/1.24  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 2.02/1.24  tff(c_6, plain, (![B_7, D_9, C_8, H_13, I_14, F_11, G_12, E_10, A_6]: (k2_xboole_0(k1_enumset1(A_6, B_7, C_8), k4_enumset1(D_9, E_10, F_11, G_12, H_13, I_14))=k7_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12, H_13, I_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.24  tff(c_8, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_enumset1(D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.24  tff(c_54, plain, (![A_37, D_33, E_36, C_32, B_34, F_35]: (k2_xboole_0(k1_enumset1(A_37, B_34, C_32), k1_enumset1(D_33, E_36, F_35))=k4_enumset1(A_37, B_34, C_32, D_33, E_36, F_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.24  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.24  tff(c_113, plain, (![A_50, D_55, F_52, C_51, B_53, C_54, E_49]: (k2_xboole_0(k1_enumset1(A_50, B_53, C_51), k2_xboole_0(k1_enumset1(D_55, E_49, F_52), C_54))=k2_xboole_0(k4_enumset1(A_50, B_53, C_51, D_55, E_49, F_52), C_54))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.02/1.24  tff(c_137, plain, (![A_50, B_16, A_15, D_18, C_51, E_19, B_53, F_20, C_17]: (k2_xboole_0(k4_enumset1(A_50, B_53, C_51, A_15, B_16, C_17), k1_enumset1(D_18, E_19, F_20))=k2_xboole_0(k1_enumset1(A_50, B_53, C_51), k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_113])).
% 2.02/1.24  tff(c_141, plain, (![A_50, B_16, A_15, D_18, C_51, E_19, B_53, F_20, C_17]: (k2_xboole_0(k4_enumset1(A_50, B_53, C_51, A_15, B_16, C_17), k1_enumset1(D_18, E_19, F_20))=k7_enumset1(A_50, B_53, C_51, A_15, B_16, C_17, D_18, E_19, F_20))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_137])).
% 2.02/1.24  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_enumset1('#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.24  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_12])).
% 2.02/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  Inference rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Ref     : 0
% 2.02/1.24  #Sup     : 38
% 2.02/1.24  #Fact    : 0
% 2.02/1.24  #Define  : 0
% 2.02/1.24  #Split   : 0
% 2.02/1.24  #Chain   : 0
% 2.02/1.24  #Close   : 0
% 2.02/1.24  
% 2.02/1.24  Ordering : KBO
% 2.02/1.24  
% 2.02/1.24  Simplification rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Subsume      : 0
% 2.02/1.24  #Demod        : 24
% 2.02/1.24  #Tautology    : 21
% 2.02/1.24  #SimpNegUnit  : 0
% 2.02/1.24  #BackRed      : 1
% 2.02/1.24  
% 2.02/1.24  #Partial instantiations: 0
% 2.02/1.24  #Strategies tried      : 1
% 2.02/1.24  
% 2.02/1.24  Timing (in seconds)
% 2.02/1.24  ----------------------
% 2.02/1.25  Preprocessing        : 0.30
% 2.02/1.25  Parsing              : 0.16
% 2.02/1.25  CNF conversion       : 0.02
% 2.02/1.25  Main loop            : 0.16
% 2.02/1.25  Inferencing          : 0.07
% 2.02/1.25  Reduction            : 0.05
% 2.02/1.25  Demodulation         : 0.05
% 2.02/1.25  BG Simplification    : 0.02
% 2.02/1.25  Subsumption          : 0.02
% 2.02/1.25  Abstraction          : 0.02
% 2.02/1.25  MUC search           : 0.00
% 2.02/1.25  Cooper               : 0.00
% 2.02/1.25  Total                : 0.49
% 2.02/1.25  Index Insertion      : 0.00
% 2.02/1.25  Index Deletion       : 0.00
% 2.02/1.25  Index Matching       : 0.00
% 2.02/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

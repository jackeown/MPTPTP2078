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
% DateTime   : Thu Dec  3 09:47:12 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

tff(c_8,plain,(
    ! [E_16,D_15,I_20,H_19,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k4_enumset1(D_15,E_16,F_17,G_18,H_19,I_20)) = k7_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18,H_19,I_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k1_enumset1(D_9,E_10,F_11)) = k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_35,C_33,E_36,F_37,B_34,D_32] : k2_xboole_0(k1_enumset1(A_35,B_34,C_33),k1_enumset1(D_32,E_36,F_37)) = k4_enumset1(A_35,B_34,C_33,D_32,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [F_41,C_42,B_43,D_40,A_38,E_39,C_44] : k2_xboole_0(k1_enumset1(A_38,B_43,C_42),k2_xboole_0(k1_enumset1(D_40,E_39,F_41),C_44)) = k2_xboole_0(k4_enumset1(A_38,B_43,C_42,D_40,E_39,F_41),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_78,plain,(
    ! [B_7,C_42,D_9,B_43,C_8,F_11,E_10,A_38,A_6] : k2_xboole_0(k4_enumset1(A_38,B_43,C_42,A_6,B_7,C_8),k1_enumset1(D_9,E_10,F_11)) = k2_xboole_0(k1_enumset1(A_38,B_43,C_42),k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_110,plain,(
    ! [B_7,C_42,D_9,B_43,C_8,F_11,E_10,A_38,A_6] : k2_xboole_0(k4_enumset1(A_38,B_43,C_42,A_6,B_7,C_8),k1_enumset1(D_9,E_10,F_11)) = k7_enumset1(A_38,B_43,C_42,A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_enumset1('#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_12])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.16  
% 1.88/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  %$ k7_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.17  tff('#skF_7', type, '#skF_7': $i).
% 1.88/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.17  tff('#skF_9', type, '#skF_9': $i).
% 1.88/1.17  tff('#skF_8', type, '#skF_8': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.17  
% 1.88/1.17  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 1.88/1.17  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 1.88/1.17  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.88/1.17  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 1.88/1.17  tff(c_8, plain, (![E_16, D_15, I_20, H_19, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k4_enumset1(D_15, E_16, F_17, G_18, H_19, I_20))=k7_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18, H_19, I_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.17  tff(c_6, plain, (![B_7, D_9, C_8, F_11, E_10, A_6]: (k2_xboole_0(k1_enumset1(A_6, B_7, C_8), k1_enumset1(D_9, E_10, F_11))=k4_enumset1(A_6, B_7, C_8, D_9, E_10, F_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.17  tff(c_48, plain, (![A_35, C_33, E_36, F_37, B_34, D_32]: (k2_xboole_0(k1_enumset1(A_35, B_34, C_33), k1_enumset1(D_32, E_36, F_37))=k4_enumset1(A_35, B_34, C_33, D_32, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.17  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.17  tff(c_60, plain, (![F_41, C_42, B_43, D_40, A_38, E_39, C_44]: (k2_xboole_0(k1_enumset1(A_38, B_43, C_42), k2_xboole_0(k1_enumset1(D_40, E_39, F_41), C_44))=k2_xboole_0(k4_enumset1(A_38, B_43, C_42, D_40, E_39, F_41), C_44))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 1.88/1.17  tff(c_78, plain, (![B_7, C_42, D_9, B_43, C_8, F_11, E_10, A_38, A_6]: (k2_xboole_0(k4_enumset1(A_38, B_43, C_42, A_6, B_7, C_8), k1_enumset1(D_9, E_10, F_11))=k2_xboole_0(k1_enumset1(A_38, B_43, C_42), k4_enumset1(A_6, B_7, C_8, D_9, E_10, F_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 1.88/1.17  tff(c_110, plain, (![B_7, C_42, D_9, B_43, C_8, F_11, E_10, A_38, A_6]: (k2_xboole_0(k4_enumset1(A_38, B_43, C_42, A_6, B_7, C_8), k1_enumset1(D_9, E_10, F_11))=k7_enumset1(A_38, B_43, C_42, A_6, B_7, C_8, D_9, E_10, F_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 1.88/1.17  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_enumset1('#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.17  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_12])).
% 1.88/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  Inference rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Ref     : 0
% 1.88/1.17  #Sup     : 24
% 1.88/1.17  #Fact    : 0
% 1.88/1.17  #Define  : 0
% 1.88/1.17  #Split   : 0
% 1.88/1.17  #Chain   : 0
% 1.88/1.17  #Close   : 0
% 1.88/1.17  
% 1.88/1.17  Ordering : KBO
% 1.88/1.17  
% 1.88/1.17  Simplification rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Subsume      : 0
% 1.88/1.17  #Demod        : 12
% 1.88/1.17  #Tautology    : 17
% 1.88/1.17  #SimpNegUnit  : 0
% 1.88/1.17  #BackRed      : 1
% 1.88/1.17  
% 1.88/1.17  #Partial instantiations: 0
% 1.88/1.17  #Strategies tried      : 1
% 1.88/1.17  
% 1.88/1.17  Timing (in seconds)
% 1.88/1.17  ----------------------
% 1.88/1.18  Preprocessing        : 0.27
% 1.88/1.18  Parsing              : 0.14
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.11
% 1.88/1.18  Inferencing          : 0.05
% 1.88/1.18  Reduction            : 0.04
% 1.88/1.18  Demodulation         : 0.03
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.18  Subsumption          : 0.01
% 1.88/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.41
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

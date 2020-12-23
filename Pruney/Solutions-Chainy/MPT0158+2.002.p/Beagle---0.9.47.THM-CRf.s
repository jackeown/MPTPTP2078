%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] : k2_xboole_0(k1_tarski(A_6),k3_enumset1(B_7,C_8,D_9,E_10,F_11)) = k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_451,plain,(
    ! [D_63,F_68,A_66,C_64,E_67,B_65] : k2_xboole_0(k1_tarski(A_66),k3_enumset1(B_65,C_64,D_63,E_67,F_68)) = k4_enumset1(A_66,B_65,C_64,D_63,E_67,F_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k2_xboole_0(A_41,B_42),C_43) = k2_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1,C_43] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_43)) = k2_xboole_0(A_1,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_57])).

tff(c_469,plain,(
    ! [D_63,F_68,A_66,C_64,E_67,B_65] : k2_xboole_0(k1_tarski(A_66),k4_enumset1(A_66,B_65,C_64,D_63,E_67,F_68)) = k2_xboole_0(k1_tarski(A_66),k3_enumset1(B_65,C_64,D_63,E_67,F_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_76])).

tff(c_5792,plain,(
    ! [B_215,C_216,A_217,F_219,D_218,E_214] : k2_xboole_0(k1_tarski(A_217),k4_enumset1(A_217,B_215,C_216,D_218,E_214,F_219)) = k4_enumset1(A_217,B_215,C_216,D_218,E_214,F_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_469])).

tff(c_8,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k1_tarski(A_12),k4_enumset1(B_13,C_14,D_15,E_16,F_17,G_18)) = k5_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5830,plain,(
    ! [B_215,C_216,A_217,F_219,D_218,E_214] : k5_enumset1(A_217,A_217,B_215,C_216,D_218,E_214,F_219) = k4_enumset1(A_217,B_215,C_216,D_218,E_214,F_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_5792,c_8])).

tff(c_20,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5830,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.39  
% 6.87/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.39  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.87/2.39  
% 6.87/2.39  %Foreground sorts:
% 6.87/2.39  
% 6.87/2.39  
% 6.87/2.39  %Background operators:
% 6.87/2.39  
% 6.87/2.39  
% 6.87/2.39  %Foreground operators:
% 6.87/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.87/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.87/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.87/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.87/2.39  tff('#skF_6', type, '#skF_6': $i).
% 6.87/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.87/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.87/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.87/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.87/2.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.87/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.87/2.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.39  
% 6.87/2.40  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 6.87/2.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.87/2.40  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.87/2.40  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 6.87/2.40  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.87/2.40  tff(c_6, plain, (![B_7, D_9, C_8, F_11, E_10, A_6]: (k2_xboole_0(k1_tarski(A_6), k3_enumset1(B_7, C_8, D_9, E_10, F_11))=k4_enumset1(A_6, B_7, C_8, D_9, E_10, F_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.40  tff(c_451, plain, (![D_63, F_68, A_66, C_64, E_67, B_65]: (k2_xboole_0(k1_tarski(A_66), k3_enumset1(B_65, C_64, D_63, E_67, F_68))=k4_enumset1(A_66, B_65, C_64, D_63, E_67, F_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.40  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.87/2.40  tff(c_57, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k2_xboole_0(A_41, B_42), C_43)=k2_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.87/2.40  tff(c_76, plain, (![A_1, C_43]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_43))=k2_xboole_0(A_1, C_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_57])).
% 6.87/2.40  tff(c_469, plain, (![D_63, F_68, A_66, C_64, E_67, B_65]: (k2_xboole_0(k1_tarski(A_66), k4_enumset1(A_66, B_65, C_64, D_63, E_67, F_68))=k2_xboole_0(k1_tarski(A_66), k3_enumset1(B_65, C_64, D_63, E_67, F_68)))), inference(superposition, [status(thm), theory('equality')], [c_451, c_76])).
% 6.87/2.40  tff(c_5792, plain, (![B_215, C_216, A_217, F_219, D_218, E_214]: (k2_xboole_0(k1_tarski(A_217), k4_enumset1(A_217, B_215, C_216, D_218, E_214, F_219))=k4_enumset1(A_217, B_215, C_216, D_218, E_214, F_219))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_469])).
% 6.87/2.40  tff(c_8, plain, (![E_16, D_15, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k1_tarski(A_12), k4_enumset1(B_13, C_14, D_15, E_16, F_17, G_18))=k5_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.87/2.40  tff(c_5830, plain, (![B_215, C_216, A_217, F_219, D_218, E_214]: (k5_enumset1(A_217, A_217, B_215, C_216, D_218, E_214, F_219)=k4_enumset1(A_217, B_215, C_216, D_218, E_214, F_219))), inference(superposition, [status(thm), theory('equality')], [c_5792, c_8])).
% 6.87/2.40  tff(c_20, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.87/2.40  tff(c_5912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5830, c_20])).
% 6.87/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.40  
% 6.87/2.40  Inference rules
% 6.87/2.40  ----------------------
% 6.87/2.40  #Ref     : 0
% 6.87/2.40  #Sup     : 1418
% 6.87/2.40  #Fact    : 0
% 6.87/2.40  #Define  : 0
% 6.87/2.40  #Split   : 0
% 6.87/2.40  #Chain   : 0
% 6.87/2.40  #Close   : 0
% 6.87/2.40  
% 6.87/2.40  Ordering : KBO
% 6.87/2.40  
% 6.87/2.40  Simplification rules
% 6.87/2.40  ----------------------
% 6.87/2.40  #Subsume      : 37
% 6.87/2.40  #Demod        : 2721
% 6.87/2.40  #Tautology    : 863
% 6.87/2.40  #SimpNegUnit  : 0
% 6.87/2.40  #BackRed      : 1
% 6.87/2.40  
% 6.87/2.40  #Partial instantiations: 0
% 6.87/2.40  #Strategies tried      : 1
% 6.87/2.40  
% 6.87/2.40  Timing (in seconds)
% 6.87/2.40  ----------------------
% 6.87/2.40  Preprocessing        : 0.31
% 6.87/2.40  Parsing              : 0.16
% 6.87/2.40  CNF conversion       : 0.02
% 6.87/2.40  Main loop            : 1.28
% 6.87/2.40  Inferencing          : 0.42
% 6.87/2.40  Reduction            : 0.67
% 6.87/2.40  Demodulation         : 0.59
% 6.87/2.40  BG Simplification    : 0.05
% 6.87/2.40  Subsumption          : 0.10
% 6.87/2.40  Abstraction          : 0.10
% 6.87/2.40  MUC search           : 0.00
% 6.87/2.40  Cooper               : 0.00
% 6.87/2.40  Total                : 1.62
% 6.87/2.40  Index Insertion      : 0.00
% 6.87/2.40  Index Deletion       : 0.00
% 6.87/2.40  Index Matching       : 0.00
% 6.87/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

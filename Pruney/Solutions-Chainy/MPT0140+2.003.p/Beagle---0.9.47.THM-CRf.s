%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:47 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(c_6,plain,(
    ! [B_11,A_10,C_12,G_16,F_15,E_14,D_13] : k2_xboole_0(k2_enumset1(A_10,B_11,C_12,D_13),k1_enumset1(E_14,F_15,G_16)) = k5_enumset1(A_10,B_11,C_12,D_13,E_14,F_15,G_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_34,B_35,C_36,D_37] : k2_xboole_0(k1_tarski(A_34),k1_enumset1(B_35,C_36,D_37)) = k2_enumset1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [C_70,A_66,D_67,B_68,C_69] : k2_xboole_0(k1_tarski(A_66),k2_xboole_0(k1_enumset1(B_68,C_70,D_67),C_69)) = k2_xboole_0(k2_enumset1(A_66,B_68,C_70,D_67),C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_223,plain,(
    ! [B_5,A_66,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_66,A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k2_xboole_0(k1_tarski(A_66),k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_433,plain,(
    ! [B_5,A_66,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_tarski(A_66),k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9)) = k5_enumset1(A_66,A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_223])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.30  
% 2.28/1.30  %Foreground sorts:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Background operators:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Foreground operators:
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.30  
% 2.28/1.31  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.28/1.31  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.28/1.31  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.28/1.31  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.28/1.31  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.28/1.31  tff(c_6, plain, (![B_11, A_10, C_12, G_16, F_15, E_14, D_13]: (k2_xboole_0(k2_enumset1(A_10, B_11, C_12, D_13), k1_enumset1(E_14, F_15, G_16))=k5_enumset1(A_10, B_11, C_12, D_13, E_14, F_15, G_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.31  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.31  tff(c_56, plain, (![A_34, B_35, C_36, D_37]: (k2_xboole_0(k1_tarski(A_34), k1_enumset1(B_35, C_36, D_37))=k2_enumset1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.31  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.31  tff(c_202, plain, (![C_70, A_66, D_67, B_68, C_69]: (k2_xboole_0(k1_tarski(A_66), k2_xboole_0(k1_enumset1(B_68, C_70, D_67), C_69))=k2_xboole_0(k2_enumset1(A_66, B_68, C_70, D_67), C_69))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.28/1.31  tff(c_223, plain, (![B_5, A_66, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_66, A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k2_xboole_0(k1_tarski(A_66), k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 2.28/1.31  tff(c_433, plain, (![B_5, A_66, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_tarski(A_66), k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))=k5_enumset1(A_66, A_4, B_5, C_6, D_7, E_8, F_9))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_223])).
% 2.28/1.31  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.31  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_433, c_14])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 107
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 0
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 0
% 2.28/1.31  #Demod        : 61
% 2.28/1.31  #Tautology    : 60
% 2.28/1.31  #SimpNegUnit  : 0
% 2.28/1.31  #BackRed      : 1
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.28/1.31  Preprocessing        : 0.26
% 2.28/1.31  Parsing              : 0.15
% 2.28/1.31  CNF conversion       : 0.02
% 2.28/1.31  Main loop            : 0.29
% 2.28/1.31  Inferencing          : 0.13
% 2.28/1.31  Reduction            : 0.09
% 2.28/1.31  Demodulation         : 0.08
% 2.28/1.31  BG Simplification    : 0.02
% 2.28/1.31  Subsumption          : 0.04
% 2.28/1.31  Abstraction          : 0.02
% 2.28/1.31  MUC search           : 0.00
% 2.28/1.31  Cooper               : 0.00
% 2.28/1.31  Total                : 0.57
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

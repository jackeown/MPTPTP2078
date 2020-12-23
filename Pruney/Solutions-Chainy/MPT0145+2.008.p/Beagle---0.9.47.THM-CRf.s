%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k2_enumset1(D_22,E_23,F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_tarski(D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [A_46,D_44,C_43,F_42,E_45,B_41] : k2_xboole_0(k1_enumset1(A_46,B_41,C_43),k1_enumset1(D_44,E_45,F_42)) = k4_enumset1(A_46,B_41,C_43,D_44,E_45,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_426,plain,(
    ! [C_126,A_130,F_127,B_131,E_125,D_128,C_129] : k2_xboole_0(k1_enumset1(A_130,B_131,C_126),k2_xboole_0(k1_enumset1(D_128,E_125,F_127),C_129)) = k2_xboole_0(k4_enumset1(A_130,B_131,C_126,D_128,E_125,F_127),C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_459,plain,(
    ! [B_16,C_126,A_15,D_18,A_130,B_131,C_17] : k2_xboole_0(k4_enumset1(A_130,B_131,C_126,A_15,B_16,C_17),k1_tarski(D_18)) = k2_xboole_0(k1_enumset1(A_130,B_131,C_126),k2_enumset1(A_15,B_16,C_17,D_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_426])).

tff(c_464,plain,(
    ! [B_16,C_126,A_15,D_18,A_130,B_131,C_17] : k2_xboole_0(k4_enumset1(A_130,B_131,C_126,A_15,B_16,C_17),k1_tarski(D_18)) = k5_enumset1(A_130,B_131,C_126,A_15,B_16,C_17,D_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_459])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:42:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.41  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.41  
% 2.63/1.41  %Foreground sorts:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Background operators:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Foreground operators:
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.41  
% 2.63/1.41  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.63/1.41  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.63/1.41  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.63/1.41  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.63/1.41  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.63/1.41  tff(c_12, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k2_enumset1(D_22, E_23, F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.41  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_tarski(D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.41  tff(c_94, plain, (![A_46, D_44, C_43, F_42, E_45, B_41]: (k2_xboole_0(k1_enumset1(A_46, B_41, C_43), k1_enumset1(D_44, E_45, F_42))=k4_enumset1(A_46, B_41, C_43, D_44, E_45, F_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.41  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.41  tff(c_426, plain, (![C_126, A_130, F_127, B_131, E_125, D_128, C_129]: (k2_xboole_0(k1_enumset1(A_130, B_131, C_126), k2_xboole_0(k1_enumset1(D_128, E_125, F_127), C_129))=k2_xboole_0(k4_enumset1(A_130, B_131, C_126, D_128, E_125, F_127), C_129))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2])).
% 2.63/1.41  tff(c_459, plain, (![B_16, C_126, A_15, D_18, A_130, B_131, C_17]: (k2_xboole_0(k4_enumset1(A_130, B_131, C_126, A_15, B_16, C_17), k1_tarski(D_18))=k2_xboole_0(k1_enumset1(A_130, B_131, C_126), k2_enumset1(A_15, B_16, C_17, D_18)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_426])).
% 2.63/1.41  tff(c_464, plain, (![B_16, C_126, A_15, D_18, A_130, B_131, C_17]: (k2_xboole_0(k4_enumset1(A_130, B_131, C_126, A_15, B_16, C_17), k1_tarski(D_18))=k5_enumset1(A_130, B_131, C_126, A_15, B_16, C_17, D_18))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_459])).
% 2.63/1.41  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.41  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_464, c_14])).
% 2.63/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  Inference rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Ref     : 0
% 2.63/1.41  #Sup     : 125
% 2.63/1.41  #Fact    : 0
% 2.63/1.41  #Define  : 0
% 2.63/1.41  #Split   : 0
% 2.63/1.41  #Chain   : 0
% 2.63/1.41  #Close   : 0
% 2.63/1.41  
% 2.63/1.41  Ordering : KBO
% 2.63/1.41  
% 2.63/1.41  Simplification rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Subsume      : 0
% 2.63/1.41  #Demod        : 72
% 2.63/1.41  #Tautology    : 69
% 2.63/1.41  #SimpNegUnit  : 0
% 2.63/1.41  #BackRed      : 3
% 2.63/1.41  
% 2.63/1.41  #Partial instantiations: 0
% 2.63/1.41  #Strategies tried      : 1
% 2.63/1.41  
% 2.63/1.41  Timing (in seconds)
% 2.63/1.41  ----------------------
% 2.63/1.42  Preprocessing        : 0.29
% 2.63/1.42  Parsing              : 0.16
% 2.63/1.42  CNF conversion       : 0.02
% 2.63/1.42  Main loop            : 0.32
% 2.63/1.42  Inferencing          : 0.15
% 2.63/1.42  Reduction            : 0.10
% 2.63/1.42  Demodulation         : 0.09
% 2.63/1.42  BG Simplification    : 0.02
% 2.63/1.42  Subsumption          : 0.04
% 2.63/1.42  Abstraction          : 0.03
% 2.63/1.42  MUC search           : 0.00
% 2.63/1.42  Cooper               : 0.00
% 2.63/1.42  Total                : 0.64
% 2.63/1.42  Index Insertion      : 0.00
% 2.63/1.42  Index Deletion       : 0.00
% 2.63/1.42  Index Matching       : 0.00
% 2.63/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

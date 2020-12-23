%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:53 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k2_xboole_0(k1_tarski(A_30),k4_enumset1(B_31,C_32,D_33,E_34,F_35,G_36)) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k2_xboole_0(k2_enumset1(A_24,B_25,C_26,D_27),k2_tarski(E_28,F_29)) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [E_61,D_59,C_63,A_62,B_60] : k2_xboole_0(k1_tarski(A_62),k2_enumset1(B_60,C_63,D_59,E_61)) = k3_enumset1(A_62,B_60,C_63,D_59,E_61) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_460,plain,(
    ! [E_151,D_155,B_152,A_154,C_156,C_153] : k2_xboole_0(k1_tarski(A_154),k2_xboole_0(k2_enumset1(B_152,C_153,D_155,E_151),C_156)) = k2_xboole_0(k3_enumset1(A_154,B_152,C_153,D_155,E_151),C_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_487,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,A_154,E_28] : k2_xboole_0(k3_enumset1(A_154,A_24,B_25,C_26,D_27),k2_tarski(E_28,F_29)) = k2_xboole_0(k1_tarski(A_154),k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_460])).

tff(c_492,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,A_154,E_28] : k2_xboole_0(k3_enumset1(A_154,A_24,B_25,C_26,D_27),k2_tarski(E_28,F_29)) = k5_enumset1(A_154,A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_487])).

tff(c_20,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.38  
% 2.68/1.38  %Foreground sorts:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Background operators:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Foreground operators:
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.68/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.38  
% 2.68/1.39  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.68/1.39  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 2.68/1.39  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.68/1.39  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.68/1.39  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.68/1.39  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k2_xboole_0(k1_tarski(A_30), k4_enumset1(B_31, C_32, D_33, E_34, F_35, G_36))=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.39  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k2_xboole_0(k2_enumset1(A_24, B_25, C_26, D_27), k2_tarski(E_28, F_29))=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.39  tff(c_101, plain, (![E_61, D_59, C_63, A_62, B_60]: (k2_xboole_0(k1_tarski(A_62), k2_enumset1(B_60, C_63, D_59, E_61))=k3_enumset1(A_62, B_60, C_63, D_59, E_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.39  tff(c_460, plain, (![E_151, D_155, B_152, A_154, C_156, C_153]: (k2_xboole_0(k1_tarski(A_154), k2_xboole_0(k2_enumset1(B_152, C_153, D_155, E_151), C_156))=k2_xboole_0(k3_enumset1(A_154, B_152, C_153, D_155, E_151), C_156))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2])).
% 2.68/1.39  tff(c_487, plain, (![A_24, B_25, F_29, D_27, C_26, A_154, E_28]: (k2_xboole_0(k3_enumset1(A_154, A_24, B_25, C_26, D_27), k2_tarski(E_28, F_29))=k2_xboole_0(k1_tarski(A_154), k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_460])).
% 2.68/1.39  tff(c_492, plain, (![A_24, B_25, F_29, D_27, C_26, A_154, E_28]: (k2_xboole_0(k3_enumset1(A_154, A_24, B_25, C_26, D_27), k2_tarski(E_28, F_29))=k5_enumset1(A_154, A_24, B_25, C_26, D_27, E_28, F_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_487])).
% 2.68/1.39  tff(c_20, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.39  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_20])).
% 2.68/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  Inference rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Ref     : 0
% 2.68/1.39  #Sup     : 137
% 2.68/1.39  #Fact    : 0
% 2.68/1.39  #Define  : 0
% 2.68/1.40  #Split   : 0
% 2.68/1.40  #Chain   : 0
% 2.68/1.40  #Close   : 0
% 2.68/1.40  
% 2.68/1.40  Ordering : KBO
% 2.68/1.40  
% 2.68/1.40  Simplification rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Subsume      : 0
% 2.68/1.40  #Demod        : 63
% 2.68/1.40  #Tautology    : 72
% 2.68/1.40  #SimpNegUnit  : 0
% 2.68/1.40  #BackRed      : 1
% 2.68/1.40  
% 2.68/1.40  #Partial instantiations: 0
% 2.68/1.40  #Strategies tried      : 1
% 2.68/1.40  
% 2.68/1.40  Timing (in seconds)
% 2.68/1.40  ----------------------
% 2.68/1.40  Preprocessing        : 0.29
% 2.68/1.40  Parsing              : 0.16
% 2.68/1.40  CNF conversion       : 0.02
% 2.68/1.40  Main loop            : 0.34
% 2.68/1.40  Inferencing          : 0.16
% 2.68/1.40  Reduction            : 0.11
% 2.68/1.40  Demodulation         : 0.09
% 2.68/1.40  BG Simplification    : 0.03
% 2.68/1.40  Subsumption          : 0.04
% 2.68/1.40  Abstraction          : 0.03
% 2.68/1.40  MUC search           : 0.00
% 2.68/1.40  Cooper               : 0.00
% 2.68/1.40  Total                : 0.65
% 2.68/1.40  Index Insertion      : 0.00
% 2.68/1.40  Index Deletion       : 0.00
% 2.68/1.40  Index Matching       : 0.00
% 2.68/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

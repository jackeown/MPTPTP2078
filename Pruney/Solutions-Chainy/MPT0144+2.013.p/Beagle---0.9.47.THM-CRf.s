%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_10,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k1_enumset1(E_15,F_16,G_17)) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k1_tarski(A_20),k2_tarski(B_21,C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_267,plain,(
    ! [B_70,C_67,D_68,E_69,A_71] : k2_xboole_0(k2_enumset1(A_71,B_70,C_67,D_68),k1_tarski(E_69)) = k3_enumset1(A_71,B_70,C_67,D_68,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_677,plain,(
    ! [C_115,A_113,B_110,D_111,C_112,E_114] : k2_xboole_0(k2_enumset1(A_113,B_110,C_112,D_111),k2_xboole_0(k1_tarski(E_114),C_115)) = k2_xboole_0(k3_enumset1(A_113,B_110,C_112,D_111,E_114),C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_4])).

tff(c_707,plain,(
    ! [A_113,B_110,C_22,D_111,A_20,B_21,C_112] : k2_xboole_0(k3_enumset1(A_113,B_110,C_112,D_111,A_20),k2_tarski(B_21,C_22)) = k2_xboole_0(k2_enumset1(A_113,B_110,C_112,D_111),k1_enumset1(A_20,B_21,C_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_677])).

tff(c_715,plain,(
    ! [A_113,B_110,C_22,D_111,A_20,B_21,C_112] : k2_xboole_0(k3_enumset1(A_113,B_110,C_112,D_111,A_20),k2_tarski(B_21,C_22)) = k5_enumset1(A_113,B_110,C_112,D_111,A_20,B_21,C_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_707])).

tff(c_20,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.71  
% 4.13/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.71  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.13/1.71  
% 4.13/1.71  %Foreground sorts:
% 4.13/1.71  
% 4.13/1.71  
% 4.13/1.71  %Background operators:
% 4.13/1.71  
% 4.13/1.71  
% 4.13/1.71  %Foreground operators:
% 4.13/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.71  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.13/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.13/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.13/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.13/1.71  
% 4.13/1.72  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 4.13/1.72  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 4.13/1.72  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 4.13/1.72  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.13/1.72  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 4.13/1.72  tff(c_10, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k1_enumset1(E_15, F_16, G_17))=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.72  tff(c_14, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k1_tarski(A_20), k2_tarski(B_21, C_22))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.72  tff(c_267, plain, (![B_70, C_67, D_68, E_69, A_71]: (k2_xboole_0(k2_enumset1(A_71, B_70, C_67, D_68), k1_tarski(E_69))=k3_enumset1(A_71, B_70, C_67, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.72  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.13/1.72  tff(c_677, plain, (![C_115, A_113, B_110, D_111, C_112, E_114]: (k2_xboole_0(k2_enumset1(A_113, B_110, C_112, D_111), k2_xboole_0(k1_tarski(E_114), C_115))=k2_xboole_0(k3_enumset1(A_113, B_110, C_112, D_111, E_114), C_115))), inference(superposition, [status(thm), theory('equality')], [c_267, c_4])).
% 4.13/1.72  tff(c_707, plain, (![A_113, B_110, C_22, D_111, A_20, B_21, C_112]: (k2_xboole_0(k3_enumset1(A_113, B_110, C_112, D_111, A_20), k2_tarski(B_21, C_22))=k2_xboole_0(k2_enumset1(A_113, B_110, C_112, D_111), k1_enumset1(A_20, B_21, C_22)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_677])).
% 4.13/1.72  tff(c_715, plain, (![A_113, B_110, C_22, D_111, A_20, B_21, C_112]: (k2_xboole_0(k3_enumset1(A_113, B_110, C_112, D_111, A_20), k2_tarski(B_21, C_22))=k5_enumset1(A_113, B_110, C_112, D_111, A_20, B_21, C_22))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_707])).
% 4.13/1.72  tff(c_20, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.13/1.72  tff(c_1957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_715, c_20])).
% 4.13/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  Inference rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Ref     : 0
% 4.13/1.72  #Sup     : 487
% 4.13/1.72  #Fact    : 0
% 4.13/1.72  #Define  : 0
% 4.13/1.72  #Split   : 0
% 4.13/1.72  #Chain   : 0
% 4.13/1.72  #Close   : 0
% 4.13/1.72  
% 4.13/1.72  Ordering : KBO
% 4.13/1.72  
% 4.13/1.72  Simplification rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Subsume      : 0
% 4.13/1.72  #Demod        : 648
% 4.13/1.72  #Tautology    : 205
% 4.13/1.72  #SimpNegUnit  : 0
% 4.13/1.72  #BackRed      : 1
% 4.13/1.72  
% 4.13/1.72  #Partial instantiations: 0
% 4.13/1.72  #Strategies tried      : 1
% 4.13/1.72  
% 4.13/1.72  Timing (in seconds)
% 4.13/1.72  ----------------------
% 4.13/1.72  Preprocessing        : 0.27
% 4.13/1.72  Parsing              : 0.15
% 4.13/1.72  CNF conversion       : 0.02
% 4.13/1.72  Main loop            : 0.68
% 4.13/1.72  Inferencing          : 0.25
% 4.13/1.72  Reduction            : 0.29
% 4.13/1.72  Demodulation         : 0.25
% 4.13/1.72  BG Simplification    : 0.04
% 4.13/1.72  Subsumption          : 0.07
% 4.13/1.72  Abstraction          : 0.06
% 4.13/1.72  MUC search           : 0.00
% 4.13/1.72  Cooper               : 0.00
% 4.13/1.72  Total                : 0.97
% 4.13/1.72  Index Insertion      : 0.00
% 4.13/1.72  Index Deletion       : 0.00
% 4.13/1.73  Index Matching       : 0.00
% 4.13/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

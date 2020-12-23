%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_10,plain,(
    ! [A_21,B_22,D_24,C_23,G_27,F_26,E_25] : k2_xboole_0(k1_tarski(A_21),k4_enumset1(B_22,C_23,D_24,E_25,F_26,G_27)) = k5_enumset1(A_21,B_22,C_23,D_24,E_25,F_26,G_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k3_enumset1(A_15,B_16,C_17,D_18,E_19),k1_tarski(F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [D_39,E_40,F_36,A_41,C_38,B_37] : k2_xboole_0(k1_tarski(A_41),k3_enumset1(B_37,C_38,D_39,E_40,F_36)) = k4_enumset1(A_41,B_37,C_38,D_39,E_40,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [D_70,C_73,E_74,C_72,B_71,F_69,A_68] : k2_xboole_0(k1_tarski(A_68),k2_xboole_0(k3_enumset1(B_71,C_73,D_70,E_74,F_69),C_72)) = k2_xboole_0(k4_enumset1(A_68,B_71,C_73,D_70,E_74,F_69),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_134,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17,A_68] : k2_xboole_0(k4_enumset1(A_68,A_15,B_16,C_17,D_18,E_19),k1_tarski(F_20)) = k2_xboole_0(k1_tarski(A_68),k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_116])).

tff(c_138,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17,A_68] : k2_xboole_0(k4_enumset1(A_68,A_15,B_16,C_17,D_18,E_19),k1_tarski(F_20)) = k5_enumset1(A_68,A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_134])).

tff(c_12,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.94/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.20  
% 1.94/1.21  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 1.94/1.21  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.94/1.21  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.94/1.21  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.94/1.21  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 1.94/1.21  tff(c_10, plain, (![A_21, B_22, D_24, C_23, G_27, F_26, E_25]: (k2_xboole_0(k1_tarski(A_21), k4_enumset1(B_22, C_23, D_24, E_25, F_26, G_27))=k5_enumset1(A_21, B_22, C_23, D_24, E_25, F_26, G_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.21  tff(c_8, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k3_enumset1(A_15, B_16, C_17, D_18, E_19), k1_tarski(F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.21  tff(c_42, plain, (![D_39, E_40, F_36, A_41, C_38, B_37]: (k2_xboole_0(k1_tarski(A_41), k3_enumset1(B_37, C_38, D_39, E_40, F_36))=k4_enumset1(A_41, B_37, C_38, D_39, E_40, F_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.21  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.21  tff(c_116, plain, (![D_70, C_73, E_74, C_72, B_71, F_69, A_68]: (k2_xboole_0(k1_tarski(A_68), k2_xboole_0(k3_enumset1(B_71, C_73, D_70, E_74, F_69), C_72))=k2_xboole_0(k4_enumset1(A_68, B_71, C_73, D_70, E_74, F_69), C_72))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.94/1.21  tff(c_134, plain, (![B_16, A_15, D_18, E_19, F_20, C_17, A_68]: (k2_xboole_0(k4_enumset1(A_68, A_15, B_16, C_17, D_18, E_19), k1_tarski(F_20))=k2_xboole_0(k1_tarski(A_68), k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_116])).
% 1.94/1.21  tff(c_138, plain, (![B_16, A_15, D_18, E_19, F_20, C_17, A_68]: (k2_xboole_0(k4_enumset1(A_68, A_15, B_16, C_17, D_18, E_19), k1_tarski(F_20))=k5_enumset1(A_68, A_15, B_16, C_17, D_18, E_19, F_20))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_134])).
% 1.94/1.21  tff(c_12, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.21  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 36
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 0
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 0
% 1.94/1.21  #Demod        : 20
% 1.94/1.21  #Tautology    : 24
% 1.94/1.21  #SimpNegUnit  : 0
% 1.94/1.21  #BackRed      : 1
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.28
% 1.94/1.21  Parsing              : 0.15
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.17
% 1.94/1.21  Inferencing          : 0.08
% 1.94/1.21  Reduction            : 0.05
% 1.94/1.21  Demodulation         : 0.05
% 1.94/1.21  BG Simplification    : 0.02
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.02
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.47
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

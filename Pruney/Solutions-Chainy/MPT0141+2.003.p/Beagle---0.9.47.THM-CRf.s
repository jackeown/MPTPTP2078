%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
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
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k4_enumset1(B_21,C_22,D_23,E_24,F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,(
    ! [A_76,B_75,D_73,C_74,F_72,E_71] : k2_xboole_0(k1_tarski(A_76),k3_enumset1(B_75,C_74,D_73,E_71,F_72)) = k4_enumset1(A_76,B_75,C_74,D_73,E_71,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_xboole_0(A_32,B_33),C_34) = k2_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_9,B_10,C_34] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_34)) = k2_xboole_0(k2_tarski(A_9,B_10),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_224,plain,(
    ! [A_76,B_75,D_73,C_74,F_72,E_71,A_9] : k2_xboole_0(k2_tarski(A_9,A_76),k3_enumset1(B_75,C_74,D_73,E_71,F_72)) = k2_xboole_0(k1_tarski(A_9),k4_enumset1(A_76,B_75,C_74,D_73,E_71,F_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_51])).

tff(c_463,plain,(
    ! [A_76,B_75,D_73,C_74,F_72,E_71,A_9] : k2_xboole_0(k2_tarski(A_9,A_76),k3_enumset1(B_75,C_74,D_73,E_71,F_72)) = k5_enumset1(A_9,A_76,B_75,C_74,D_73,E_71,F_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_224])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:47:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.76/1.46  
% 2.76/1.46  %Foreground sorts:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Background operators:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Foreground operators:
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.46  
% 2.76/1.47  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.76/1.47  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.76/1.47  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.76/1.47  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.76/1.47  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.76/1.47  tff(c_12, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k4_enumset1(B_21, C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.47  tff(c_215, plain, (![A_76, B_75, D_73, C_74, F_72, E_71]: (k2_xboole_0(k1_tarski(A_76), k3_enumset1(B_75, C_74, D_73, E_71, F_72))=k4_enumset1(A_76, B_75, C_74, D_73, E_71, F_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.47  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.47  tff(c_33, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_xboole_0(A_32, B_33), C_34)=k2_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.47  tff(c_51, plain, (![A_9, B_10, C_34]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_34))=k2_xboole_0(k2_tarski(A_9, B_10), C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.76/1.47  tff(c_224, plain, (![A_76, B_75, D_73, C_74, F_72, E_71, A_9]: (k2_xboole_0(k2_tarski(A_9, A_76), k3_enumset1(B_75, C_74, D_73, E_71, F_72))=k2_xboole_0(k1_tarski(A_9), k4_enumset1(A_76, B_75, C_74, D_73, E_71, F_72)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_51])).
% 2.76/1.47  tff(c_463, plain, (![A_76, B_75, D_73, C_74, F_72, E_71, A_9]: (k2_xboole_0(k2_tarski(A_9, A_76), k3_enumset1(B_75, C_74, D_73, E_71, F_72))=k5_enumset1(A_9, A_76, B_75, C_74, D_73, E_71, F_72))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_224])).
% 2.76/1.47  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.47  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_14])).
% 2.76/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.47  
% 2.76/1.47  Inference rules
% 2.76/1.47  ----------------------
% 2.76/1.47  #Ref     : 0
% 2.76/1.47  #Sup     : 115
% 2.76/1.47  #Fact    : 0
% 2.76/1.47  #Define  : 0
% 2.76/1.47  #Split   : 0
% 2.76/1.47  #Chain   : 0
% 2.76/1.47  #Close   : 0
% 2.76/1.47  
% 2.76/1.47  Ordering : KBO
% 2.76/1.47  
% 2.76/1.47  Simplification rules
% 2.76/1.47  ----------------------
% 2.76/1.47  #Subsume      : 0
% 2.76/1.47  #Demod        : 78
% 2.76/1.47  #Tautology    : 65
% 2.76/1.47  #SimpNegUnit  : 0
% 2.76/1.47  #BackRed      : 4
% 2.76/1.47  
% 2.76/1.47  #Partial instantiations: 0
% 2.76/1.47  #Strategies tried      : 1
% 2.76/1.47  
% 2.76/1.47  Timing (in seconds)
% 2.76/1.47  ----------------------
% 2.76/1.48  Preprocessing        : 0.32
% 2.76/1.48  Parsing              : 0.18
% 2.76/1.48  CNF conversion       : 0.02
% 2.76/1.48  Main loop            : 0.35
% 2.76/1.48  Inferencing          : 0.16
% 2.76/1.48  Reduction            : 0.12
% 2.76/1.48  Demodulation         : 0.10
% 2.76/1.48  BG Simplification    : 0.02
% 2.76/1.48  Subsumption          : 0.04
% 2.76/1.48  Abstraction          : 0.03
% 2.76/1.48  MUC search           : 0.00
% 2.76/1.48  Cooper               : 0.00
% 2.76/1.48  Total                : 0.69
% 2.76/1.48  Index Insertion      : 0.00
% 2.76/1.48  Index Deletion       : 0.00
% 2.76/1.48  Index Matching       : 0.00
% 2.76/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

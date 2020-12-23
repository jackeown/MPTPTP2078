%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.48s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k4_enumset1(B_21,C_22,D_23,E_24,F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [C_70,F_68,A_72,B_71,E_67,D_69] : k2_xboole_0(k1_tarski(A_72),k3_enumset1(B_71,C_70,D_69,E_67,F_68)) = k4_enumset1(A_72,B_71,C_70,D_69,E_67,F_68) ),
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

tff(c_210,plain,(
    ! [C_70,F_68,A_72,B_71,E_67,D_69,A_9] : k2_xboole_0(k2_tarski(A_9,A_72),k3_enumset1(B_71,C_70,D_69,E_67,F_68)) = k2_xboole_0(k1_tarski(A_9),k4_enumset1(A_72,B_71,C_70,D_69,E_67,F_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_51])).

tff(c_447,plain,(
    ! [C_70,F_68,A_72,B_71,E_67,D_69,A_9] : k2_xboole_0(k2_tarski(A_9,A_72),k3_enumset1(B_71,C_70,D_69,E_67,F_68)) = k5_enumset1(A_9,A_72,B_71,C_70,D_69,E_67,F_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_210])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n011.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 10:13:27 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.23  
% 2.48/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.23  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.48/1.23  
% 2.48/1.23  %Foreground sorts:
% 2.48/1.23  
% 2.48/1.23  
% 2.48/1.23  %Background operators:
% 2.48/1.23  
% 2.48/1.23  
% 2.48/1.23  %Foreground operators:
% 2.48/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.23  tff('#skF_7', type, '#skF_7': $i).
% 2.48/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.23  
% 2.48/1.24  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.48/1.24  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.48/1.24  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.48/1.24  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.48/1.24  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 2.48/1.24  tff(c_12, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k4_enumset1(B_21, C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.24  tff(c_201, plain, (![C_70, F_68, A_72, B_71, E_67, D_69]: (k2_xboole_0(k1_tarski(A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k4_enumset1(A_72, B_71, C_70, D_69, E_67, F_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.24  tff(c_6, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.24  tff(c_33, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_xboole_0(A_32, B_33), C_34)=k2_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.24  tff(c_51, plain, (![A_9, B_10, C_34]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_34))=k2_xboole_0(k2_tarski(A_9, B_10), C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.48/1.24  tff(c_210, plain, (![C_70, F_68, A_72, B_71, E_67, D_69, A_9]: (k2_xboole_0(k2_tarski(A_9, A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k2_xboole_0(k1_tarski(A_9), k4_enumset1(A_72, B_71, C_70, D_69, E_67, F_68)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_51])).
% 2.48/1.24  tff(c_447, plain, (![C_70, F_68, A_72, B_71, E_67, D_69, A_9]: (k2_xboole_0(k2_tarski(A_9, A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k5_enumset1(A_9, A_72, B_71, C_70, D_69, E_67, F_68))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_210])).
% 2.48/1.24  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.24  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_14])).
% 2.48/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.24  
% 2.48/1.24  Inference rules
% 2.48/1.24  ----------------------
% 2.48/1.24  #Ref     : 0
% 2.48/1.24  #Sup     : 111
% 2.48/1.24  #Fact    : 0
% 2.48/1.24  #Define  : 0
% 2.48/1.24  #Split   : 0
% 2.48/1.24  #Chain   : 0
% 2.48/1.24  #Close   : 0
% 2.48/1.24  
% 2.48/1.24  Ordering : KBO
% 2.48/1.24  
% 2.48/1.24  Simplification rules
% 2.48/1.24  ----------------------
% 2.48/1.24  #Subsume      : 0
% 2.48/1.24  #Demod        : 79
% 2.48/1.24  #Tautology    : 64
% 2.48/1.24  #SimpNegUnit  : 0
% 2.48/1.24  #BackRed      : 1
% 2.48/1.24  
% 2.48/1.24  #Partial instantiations: 0
% 2.48/1.24  #Strategies tried      : 1
% 2.48/1.24  
% 2.48/1.24  Timing (in seconds)
% 2.48/1.24  ----------------------
% 2.48/1.24  Preprocessing        : 0.27
% 2.48/1.24  Parsing              : 0.15
% 2.48/1.24  CNF conversion       : 0.02
% 2.48/1.24  Main loop            : 0.29
% 2.48/1.24  Inferencing          : 0.13
% 2.48/1.24  Reduction            : 0.10
% 2.48/1.24  Demodulation         : 0.09
% 2.48/1.24  BG Simplification    : 0.02
% 2.48/1.24  Subsumption          : 0.03
% 2.48/1.24  Abstraction          : 0.02
% 2.48/1.24  MUC search           : 0.00
% 2.48/1.24  Cooper               : 0.00
% 2.48/1.24  Total                : 0.59
% 2.48/1.24  Index Insertion      : 0.00
% 2.48/1.24  Index Deletion       : 0.00
% 2.48/1.24  Index Matching       : 0.00
% 2.48/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

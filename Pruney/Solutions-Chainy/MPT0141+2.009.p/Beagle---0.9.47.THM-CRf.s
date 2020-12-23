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
% DateTime   : Thu Dec  3 09:45:49 EST 2020

% Result     : Theorem 2.48s
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

tff(f_29,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k2_xboole_0(A_29,B_30),C_31) = k2_xboole_0(A_29,k2_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_4,B_5,C_31] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_31)) = k2_xboole_0(k2_tarski(A_4,B_5),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_210,plain,(
    ! [C_70,F_68,A_4,A_72,B_71,E_67,D_69] : k2_xboole_0(k2_tarski(A_4,A_72),k3_enumset1(B_71,C_70,D_69,E_67,F_68)) = k2_xboole_0(k1_tarski(A_4),k4_enumset1(A_72,B_71,C_70,D_69,E_67,F_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_39])).

tff(c_439,plain,(
    ! [C_70,F_68,A_4,A_72,B_71,E_67,D_69] : k2_xboole_0(k2_tarski(A_4,A_72),k3_enumset1(B_71,C_70,D_69,E_67,F_68)) = k5_enumset1(A_4,A_72,B_71,C_70,D_69,E_67,F_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_210])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.48/1.34  
% 2.48/1.34  %Foreground sorts:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Background operators:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Foreground operators:
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.48/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.34  
% 2.48/1.35  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.48/1.35  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.48/1.35  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.48/1.35  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.48/1.35  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 2.48/1.35  tff(c_12, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k4_enumset1(B_21, C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.35  tff(c_201, plain, (![C_70, F_68, A_72, B_71, E_67, D_69]: (k2_xboole_0(k1_tarski(A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k4_enumset1(A_72, B_71, C_70, D_69, E_67, F_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.35  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.35  tff(c_24, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k2_xboole_0(A_29, B_30), C_31)=k2_xboole_0(A_29, k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.35  tff(c_39, plain, (![A_4, B_5, C_31]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_31))=k2_xboole_0(k2_tarski(A_4, B_5), C_31))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 2.48/1.35  tff(c_210, plain, (![C_70, F_68, A_4, A_72, B_71, E_67, D_69]: (k2_xboole_0(k2_tarski(A_4, A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k2_xboole_0(k1_tarski(A_4), k4_enumset1(A_72, B_71, C_70, D_69, E_67, F_68)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_39])).
% 2.48/1.35  tff(c_439, plain, (![C_70, F_68, A_4, A_72, B_71, E_67, D_69]: (k2_xboole_0(k2_tarski(A_4, A_72), k3_enumset1(B_71, C_70, D_69, E_67, F_68))=k5_enumset1(A_4, A_72, B_71, C_70, D_69, E_67, F_68))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_210])).
% 2.48/1.35  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.35  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_14])).
% 2.48/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  Inference rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Ref     : 0
% 2.48/1.35  #Sup     : 108
% 2.48/1.35  #Fact    : 0
% 2.48/1.35  #Define  : 0
% 2.48/1.35  #Split   : 0
% 2.48/1.35  #Chain   : 0
% 2.48/1.35  #Close   : 0
% 2.48/1.35  
% 2.48/1.35  Ordering : KBO
% 2.48/1.35  
% 2.48/1.35  Simplification rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Subsume      : 0
% 2.48/1.35  #Demod        : 84
% 2.48/1.35  #Tautology    : 63
% 2.48/1.35  #SimpNegUnit  : 0
% 2.48/1.35  #BackRed      : 1
% 2.48/1.35  
% 2.48/1.35  #Partial instantiations: 0
% 2.48/1.35  #Strategies tried      : 1
% 2.48/1.35  
% 2.48/1.35  Timing (in seconds)
% 2.48/1.35  ----------------------
% 2.48/1.35  Preprocessing        : 0.27
% 2.48/1.35  Parsing              : 0.15
% 2.48/1.35  CNF conversion       : 0.02
% 2.48/1.35  Main loop            : 0.29
% 2.48/1.35  Inferencing          : 0.13
% 2.48/1.35  Reduction            : 0.10
% 2.48/1.35  Demodulation         : 0.08
% 2.48/1.35  BG Simplification    : 0.02
% 2.48/1.35  Subsumption          : 0.03
% 2.48/1.35  Abstraction          : 0.02
% 2.48/1.35  MUC search           : 0.00
% 2.48/1.35  Cooper               : 0.00
% 2.48/1.35  Total                : 0.58
% 2.48/1.35  Index Insertion      : 0.00
% 2.48/1.35  Index Deletion       : 0.00
% 2.48/1.35  Index Matching       : 0.00
% 2.48/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

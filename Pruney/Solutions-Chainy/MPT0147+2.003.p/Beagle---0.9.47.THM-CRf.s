%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:55 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_12,plain,(
    ! [A_23,B_24,F_28,D_26,G_29,C_25,H_30,E_27] : k2_xboole_0(k1_tarski(A_23),k5_enumset1(B_24,C_25,D_26,E_27,F_28,G_29,H_30)) = k6_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,G_29,H_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [G_68,C_73,F_67,E_70,D_72,B_69,A_71] : k2_xboole_0(k1_tarski(A_71),k4_enumset1(B_69,C_73,D_72,E_70,F_67,G_68)) = k5_enumset1(A_71,B_69,C_73,D_72,E_70,F_67,G_68) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k2_xboole_0(A_33,B_34),C_35) = k2_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_8,B_9,C_35] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k1_tarski(B_9),C_35)) = k2_xboole_0(k2_tarski(A_8,B_9),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_179,plain,(
    ! [G_68,A_8,C_73,F_67,E_70,D_72,B_69,A_71] : k2_xboole_0(k2_tarski(A_8,A_71),k4_enumset1(B_69,C_73,D_72,E_70,F_67,G_68)) = k2_xboole_0(k1_tarski(A_8),k5_enumset1(A_71,B_69,C_73,D_72,E_70,F_67,G_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_39])).

tff(c_449,plain,(
    ! [G_68,A_8,C_73,F_67,E_70,D_72,B_69,A_71] : k2_xboole_0(k2_tarski(A_8,A_71),k4_enumset1(B_69,C_73,D_72,E_70,F_67,G_68)) = k6_enumset1(A_8,A_71,B_69,C_73,D_72,E_70,F_67,G_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.45  
% 2.50/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.45  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.50/1.45  
% 2.50/1.45  %Foreground sorts:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Background operators:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Foreground operators:
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.50/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.45  
% 2.93/1.46  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 2.93/1.46  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.93/1.46  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.93/1.46  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.93/1.46  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 2.93/1.46  tff(c_12, plain, (![A_23, B_24, F_28, D_26, G_29, C_25, H_30, E_27]: (k2_xboole_0(k1_tarski(A_23), k5_enumset1(B_24, C_25, D_26, E_27, F_28, G_29, H_30))=k6_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, G_29, H_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.46  tff(c_170, plain, (![G_68, C_73, F_67, E_70, D_72, B_69, A_71]: (k2_xboole_0(k1_tarski(A_71), k4_enumset1(B_69, C_73, D_72, E_70, F_67, G_68))=k5_enumset1(A_71, B_69, C_73, D_72, E_70, F_67, G_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.46  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.46  tff(c_24, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k2_xboole_0(A_33, B_34), C_35)=k2_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.46  tff(c_39, plain, (![A_8, B_9, C_35]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k1_tarski(B_9), C_35))=k2_xboole_0(k2_tarski(A_8, B_9), C_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_24])).
% 2.93/1.46  tff(c_179, plain, (![G_68, A_8, C_73, F_67, E_70, D_72, B_69, A_71]: (k2_xboole_0(k2_tarski(A_8, A_71), k4_enumset1(B_69, C_73, D_72, E_70, F_67, G_68))=k2_xboole_0(k1_tarski(A_8), k5_enumset1(A_71, B_69, C_73, D_72, E_70, F_67, G_68)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_39])).
% 2.93/1.46  tff(c_449, plain, (![G_68, A_8, C_73, F_67, E_70, D_72, B_69, A_71]: (k2_xboole_0(k2_tarski(A_8, A_71), k4_enumset1(B_69, C_73, D_72, E_70, F_67, G_68))=k6_enumset1(A_8, A_71, B_69, C_73, D_72, E_70, F_67, G_68))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.93/1.46  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.93/1.46  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_14])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 0
% 2.93/1.46  #Sup     : 111
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 0
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 0
% 2.93/1.46  #Demod        : 85
% 2.93/1.46  #Tautology    : 67
% 2.93/1.46  #SimpNegUnit  : 0
% 2.93/1.46  #BackRed      : 2
% 2.93/1.46  
% 2.93/1.46  #Partial instantiations: 0
% 2.93/1.46  #Strategies tried      : 1
% 2.93/1.46  
% 2.93/1.46  Timing (in seconds)
% 2.93/1.46  ----------------------
% 2.93/1.47  Preprocessing        : 0.28
% 2.93/1.47  Parsing              : 0.15
% 2.93/1.47  CNF conversion       : 0.02
% 2.93/1.47  Main loop            : 0.42
% 2.93/1.47  Inferencing          : 0.19
% 2.93/1.47  Reduction            : 0.14
% 2.93/1.47  Demodulation         : 0.12
% 2.93/1.47  BG Simplification    : 0.03
% 2.93/1.47  Subsumption          : 0.05
% 2.93/1.47  Abstraction          : 0.03
% 2.93/1.47  MUC search           : 0.00
% 2.93/1.47  Cooper               : 0.00
% 2.93/1.47  Total                : 0.73
% 2.93/1.47  Index Insertion      : 0.00
% 2.93/1.47  Index Deletion       : 0.00
% 2.93/1.47  Index Matching       : 0.00
% 2.93/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_14,plain,(
    ! [A_24,H_31,B_25,F_29,D_27,C_26,E_28,G_30] : k2_xboole_0(k1_tarski(A_24),k5_enumset1(B_25,C_26,D_27,E_28,F_29,G_30,H_31)) = k6_enumset1(A_24,B_25,C_26,D_27,E_28,F_29,G_30,H_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [C_74,G_80,D_78,E_79,F_77,A_75,B_76] : k2_xboole_0(k1_tarski(A_75),k4_enumset1(B_76,C_74,D_78,E_79,F_77,G_80)) = k5_enumset1(A_75,B_76,C_74,D_78,E_79,F_77,G_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_39,B_40,C_41] : k2_xboole_0(k2_xboole_0(A_39,B_40),C_41) = k2_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_12,B_13,C_41] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k1_tarski(B_13),C_41)) = k2_xboole_0(k2_tarski(A_12,B_13),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_219,plain,(
    ! [C_74,G_80,D_78,A_12,E_79,F_77,A_75,B_76] : k2_xboole_0(k2_tarski(A_12,A_75),k4_enumset1(B_76,C_74,D_78,E_79,F_77,G_80)) = k2_xboole_0(k1_tarski(A_12),k5_enumset1(A_75,B_76,C_74,D_78,E_79,F_77,G_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_62])).

tff(c_459,plain,(
    ! [C_74,G_80,D_78,A_12,E_79,F_77,A_75,B_76] : k2_xboole_0(k2_tarski(A_12,A_75),k4_enumset1(B_76,C_74,D_78,E_79,F_77,G_80)) = k6_enumset1(A_12,A_75,B_76,C_74,D_78,E_79,F_77,G_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_219])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:49:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.70/1.40  
% 2.70/1.40  %Foreground sorts:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Background operators:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Foreground operators:
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.40  
% 2.70/1.41  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 2.70/1.41  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.70/1.41  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.70/1.41  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.70/1.41  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 2.70/1.41  tff(c_14, plain, (![A_24, H_31, B_25, F_29, D_27, C_26, E_28, G_30]: (k2_xboole_0(k1_tarski(A_24), k5_enumset1(B_25, C_26, D_27, E_28, F_29, G_30, H_31))=k6_enumset1(A_24, B_25, C_26, D_27, E_28, F_29, G_30, H_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.41  tff(c_210, plain, (![C_74, G_80, D_78, E_79, F_77, A_75, B_76]: (k2_xboole_0(k1_tarski(A_75), k4_enumset1(B_76, C_74, D_78, E_79, F_77, G_80))=k5_enumset1(A_75, B_76, C_74, D_78, E_79, F_77, G_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.41  tff(c_8, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.41  tff(c_44, plain, (![A_39, B_40, C_41]: (k2_xboole_0(k2_xboole_0(A_39, B_40), C_41)=k2_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.41  tff(c_62, plain, (![A_12, B_13, C_41]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k1_tarski(B_13), C_41))=k2_xboole_0(k2_tarski(A_12, B_13), C_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 2.70/1.41  tff(c_219, plain, (![C_74, G_80, D_78, A_12, E_79, F_77, A_75, B_76]: (k2_xboole_0(k2_tarski(A_12, A_75), k4_enumset1(B_76, C_74, D_78, E_79, F_77, G_80))=k2_xboole_0(k1_tarski(A_12), k5_enumset1(A_75, B_76, C_74, D_78, E_79, F_77, G_80)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_62])).
% 2.70/1.41  tff(c_459, plain, (![C_74, G_80, D_78, A_12, E_79, F_77, A_75, B_76]: (k2_xboole_0(k2_tarski(A_12, A_75), k4_enumset1(B_76, C_74, D_78, E_79, F_77, G_80))=k6_enumset1(A_12, A_75, B_76, C_74, D_78, E_79, F_77, G_80))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_219])).
% 2.70/1.41  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.70/1.41  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_16])).
% 2.70/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  Inference rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Ref     : 0
% 2.70/1.41  #Sup     : 111
% 2.70/1.41  #Fact    : 0
% 2.70/1.41  #Define  : 0
% 2.70/1.41  #Split   : 0
% 2.70/1.41  #Chain   : 0
% 2.70/1.41  #Close   : 0
% 2.70/1.41  
% 2.70/1.41  Ordering : KBO
% 2.70/1.41  
% 2.70/1.41  Simplification rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Subsume      : 0
% 2.70/1.41  #Demod        : 105
% 2.70/1.41  #Tautology    : 75
% 2.70/1.41  #SimpNegUnit  : 0
% 2.70/1.41  #BackRed      : 3
% 2.70/1.41  
% 2.70/1.41  #Partial instantiations: 0
% 2.70/1.41  #Strategies tried      : 1
% 2.70/1.41  
% 2.70/1.41  Timing (in seconds)
% 2.70/1.41  ----------------------
% 2.70/1.42  Preprocessing        : 0.30
% 2.70/1.42  Parsing              : 0.17
% 2.70/1.42  CNF conversion       : 0.02
% 2.70/1.42  Main loop            : 0.31
% 2.70/1.42  Inferencing          : 0.14
% 2.70/1.42  Reduction            : 0.11
% 2.70/1.42  Demodulation         : 0.09
% 2.70/1.42  BG Simplification    : 0.02
% 2.70/1.42  Subsumption          : 0.04
% 2.70/1.42  Abstraction          : 0.03
% 2.70/1.42  MUC search           : 0.00
% 2.70/1.42  Cooper               : 0.00
% 2.70/1.42  Total                : 0.64
% 2.70/1.42  Index Insertion      : 0.00
% 2.70/1.42  Index Deletion       : 0.00
% 2.70/1.42  Index Matching       : 0.00
% 2.70/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

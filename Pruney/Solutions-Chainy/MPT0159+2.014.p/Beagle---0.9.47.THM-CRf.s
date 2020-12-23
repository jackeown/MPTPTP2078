%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:23 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,G_9,E_7,B_4] : k2_xboole_0(k3_enumset1(A_3,B_4,C_5,D_6,E_7),k2_tarski(F_8,G_9)) = k5_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [H_75,F_79,A_77,C_80,B_74,D_78,E_76,G_73] : k2_xboole_0(k4_enumset1(A_77,B_74,C_80,D_78,E_76,F_79),k2_tarski(G_73,H_75)) = k6_enumset1(A_77,B_74,C_80,D_78,E_76,F_79,G_73,H_75) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [H_75,C_29,D_30,B_28,G_73,A_27,E_31] : k6_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,G_73,H_75) = k2_xboole_0(k3_enumset1(A_27,B_28,C_29,D_30,E_31),k2_tarski(G_73,H_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_111,plain,(
    ! [H_75,C_29,D_30,B_28,G_73,A_27,E_31] : k6_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,G_73,H_75) = k5_enumset1(A_27,B_28,C_29,D_30,E_31,G_73,H_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_108])).

tff(c_18,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:22:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.12  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.77/1.12  
% 1.77/1.12  %Foreground sorts:
% 1.77/1.12  
% 1.77/1.12  
% 1.77/1.12  %Background operators:
% 1.77/1.12  
% 1.77/1.12  
% 1.77/1.12  %Foreground operators:
% 1.77/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.77/1.12  tff('#skF_7', type, '#skF_7': $i).
% 1.77/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.77/1.12  tff('#skF_6', type, '#skF_6': $i).
% 1.77/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.12  
% 1.77/1.12  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 1.77/1.12  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.77/1.12  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 1.77/1.12  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.77/1.12  tff(c_4, plain, (![A_3, F_8, D_6, C_5, G_9, E_7, B_4]: (k2_xboole_0(k3_enumset1(A_3, B_4, C_5, D_6, E_7), k2_tarski(F_8, G_9))=k5_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.12  tff(c_14, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.12  tff(c_99, plain, (![H_75, F_79, A_77, C_80, B_74, D_78, E_76, G_73]: (k2_xboole_0(k4_enumset1(A_77, B_74, C_80, D_78, E_76, F_79), k2_tarski(G_73, H_75))=k6_enumset1(A_77, B_74, C_80, D_78, E_76, F_79, G_73, H_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.12  tff(c_108, plain, (![H_75, C_29, D_30, B_28, G_73, A_27, E_31]: (k6_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, G_73, H_75)=k2_xboole_0(k3_enumset1(A_27, B_28, C_29, D_30, E_31), k2_tarski(G_73, H_75)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 1.77/1.12  tff(c_111, plain, (![H_75, C_29, D_30, B_28, G_73, A_27, E_31]: (k6_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, G_73, H_75)=k5_enumset1(A_27, B_28, C_29, D_30, E_31, G_73, H_75))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_108])).
% 1.77/1.12  tff(c_18, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.77/1.12  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_18])).
% 1.77/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.12  
% 1.77/1.12  Inference rules
% 1.77/1.12  ----------------------
% 1.77/1.12  #Ref     : 0
% 1.77/1.12  #Sup     : 26
% 1.77/1.12  #Fact    : 0
% 1.77/1.12  #Define  : 0
% 1.77/1.12  #Split   : 0
% 1.77/1.12  #Chain   : 0
% 1.77/1.12  #Close   : 0
% 1.77/1.12  
% 1.77/1.12  Ordering : KBO
% 1.77/1.12  
% 1.77/1.12  Simplification rules
% 1.77/1.12  ----------------------
% 1.77/1.12  #Subsume      : 0
% 1.77/1.12  #Demod        : 5
% 1.77/1.12  #Tautology    : 22
% 1.77/1.12  #SimpNegUnit  : 0
% 1.77/1.12  #BackRed      : 1
% 1.77/1.12  
% 1.77/1.12  #Partial instantiations: 0
% 1.77/1.12  #Strategies tried      : 1
% 1.77/1.12  
% 1.77/1.12  Timing (in seconds)
% 1.77/1.12  ----------------------
% 1.77/1.13  Preprocessing        : 0.28
% 1.77/1.13  Parsing              : 0.15
% 1.77/1.13  CNF conversion       : 0.02
% 1.77/1.13  Main loop            : 0.11
% 1.77/1.13  Inferencing          : 0.05
% 1.77/1.13  Reduction            : 0.03
% 1.77/1.13  Demodulation         : 0.03
% 1.77/1.13  BG Simplification    : 0.01
% 1.77/1.13  Subsumption          : 0.01
% 1.77/1.13  Abstraction          : 0.01
% 1.77/1.13  MUC search           : 0.00
% 1.77/1.13  Cooper               : 0.00
% 1.77/1.13  Total                : 0.41
% 1.77/1.13  Index Insertion      : 0.00
% 1.77/1.13  Index Deletion       : 0.00
% 1.77/1.13  Index Matching       : 0.00
% 1.77/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

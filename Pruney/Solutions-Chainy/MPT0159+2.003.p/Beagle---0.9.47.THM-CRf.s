%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:21 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  24 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_12,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,G_14] : k2_xboole_0(k1_tarski(A_8),k4_enumset1(B_9,C_10,D_11,E_12,F_13,G_14)) = k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_482,plain,(
    ! [F_84,A_85,B_87,G_89,E_86,C_88,D_90] : k2_xboole_0(k1_tarski(A_85),k4_enumset1(B_87,C_88,D_90,E_86,F_84,G_89)) = k5_enumset1(A_85,B_87,C_88,D_90,E_86,F_84,G_89) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_79,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k2_xboole_0(A_56,B_57),C_58) = k2_xboole_0(A_56,k2_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [B_2,C_58] : k2_xboole_0(B_2,k2_xboole_0(B_2,C_58)) = k2_xboole_0(B_2,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_79])).

tff(c_500,plain,(
    ! [F_84,A_85,B_87,G_89,E_86,C_88,D_90] : k2_xboole_0(k1_tarski(A_85),k5_enumset1(A_85,B_87,C_88,D_90,E_86,F_84,G_89)) = k2_xboole_0(k1_tarski(A_85),k4_enumset1(B_87,C_88,D_90,E_86,F_84,G_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_98])).

tff(c_11888,plain,(
    ! [D_372,A_378,G_376,E_377,C_374,B_373,F_375] : k2_xboole_0(k1_tarski(A_378),k5_enumset1(A_378,B_373,C_374,D_372,E_377,F_375,G_376)) = k5_enumset1(A_378,B_373,C_374,D_372,E_377,F_375,G_376) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_500])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,G_21,E_19,H_22,F_20,C_17] : k2_xboole_0(k1_tarski(A_15),k5_enumset1(B_16,C_17,D_18,E_19,F_20,G_21,H_22)) = k6_enumset1(A_15,B_16,C_17,D_18,E_19,F_20,G_21,H_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11926,plain,(
    ! [D_372,A_378,G_376,E_377,C_374,B_373,F_375] : k6_enumset1(A_378,A_378,B_373,C_374,D_372,E_377,F_375,G_376) = k5_enumset1(A_378,B_373,C_374,D_372,E_377,F_375,G_376) ),
    inference(superposition,[status(thm),theory(equality)],[c_11888,c_14])).

tff(c_28,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11926,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:25:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.74/4.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.60  
% 11.74/4.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.60  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.74/4.60  
% 11.74/4.60  %Foreground sorts:
% 11.74/4.60  
% 11.74/4.60  
% 11.74/4.60  %Background operators:
% 11.74/4.60  
% 11.74/4.60  
% 11.74/4.60  %Foreground operators:
% 11.74/4.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.74/4.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.74/4.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.74/4.60  tff('#skF_7', type, '#skF_7': $i).
% 11.74/4.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.74/4.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.74/4.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.74/4.60  tff('#skF_5', type, '#skF_5': $i).
% 11.74/4.60  tff('#skF_6', type, '#skF_6': $i).
% 11.74/4.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.74/4.60  tff('#skF_2', type, '#skF_2': $i).
% 11.74/4.60  tff('#skF_3', type, '#skF_3': $i).
% 11.74/4.60  tff('#skF_1', type, '#skF_1': $i).
% 11.74/4.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.74/4.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.74/4.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.74/4.61  tff('#skF_4', type, '#skF_4': $i).
% 11.74/4.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.74/4.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.74/4.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.74/4.61  
% 11.74/4.62  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 11.74/4.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.74/4.62  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.74/4.62  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.74/4.62  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 11.74/4.62  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 11.74/4.62  tff(c_12, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, G_14]: (k2_xboole_0(k1_tarski(A_8), k4_enumset1(B_9, C_10, D_11, E_12, F_13, G_14))=k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.74/4.62  tff(c_482, plain, (![F_84, A_85, B_87, G_89, E_86, C_88, D_90]: (k2_xboole_0(k1_tarski(A_85), k4_enumset1(B_87, C_88, D_90, E_86, F_84, G_89))=k5_enumset1(A_85, B_87, C_88, D_90, E_86, F_84, G_89))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.74/4.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.74/4.62  tff(c_40, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.74/4.62  tff(c_44, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_40])).
% 11.74/4.62  tff(c_79, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k2_xboole_0(A_56, B_57), C_58)=k2_xboole_0(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.74/4.62  tff(c_98, plain, (![B_2, C_58]: (k2_xboole_0(B_2, k2_xboole_0(B_2, C_58))=k2_xboole_0(B_2, C_58))), inference(superposition, [status(thm), theory('equality')], [c_44, c_79])).
% 11.74/4.62  tff(c_500, plain, (![F_84, A_85, B_87, G_89, E_86, C_88, D_90]: (k2_xboole_0(k1_tarski(A_85), k5_enumset1(A_85, B_87, C_88, D_90, E_86, F_84, G_89))=k2_xboole_0(k1_tarski(A_85), k4_enumset1(B_87, C_88, D_90, E_86, F_84, G_89)))), inference(superposition, [status(thm), theory('equality')], [c_482, c_98])).
% 11.74/4.62  tff(c_11888, plain, (![D_372, A_378, G_376, E_377, C_374, B_373, F_375]: (k2_xboole_0(k1_tarski(A_378), k5_enumset1(A_378, B_373, C_374, D_372, E_377, F_375, G_376))=k5_enumset1(A_378, B_373, C_374, D_372, E_377, F_375, G_376))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_500])).
% 11.74/4.62  tff(c_14, plain, (![B_16, A_15, D_18, G_21, E_19, H_22, F_20, C_17]: (k2_xboole_0(k1_tarski(A_15), k5_enumset1(B_16, C_17, D_18, E_19, F_20, G_21, H_22))=k6_enumset1(A_15, B_16, C_17, D_18, E_19, F_20, G_21, H_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.74/4.62  tff(c_11926, plain, (![D_372, A_378, G_376, E_377, C_374, B_373, F_375]: (k6_enumset1(A_378, A_378, B_373, C_374, D_372, E_377, F_375, G_376)=k5_enumset1(A_378, B_373, C_374, D_372, E_377, F_375, G_376))), inference(superposition, [status(thm), theory('equality')], [c_11888, c_14])).
% 11.74/4.62  tff(c_28, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.74/4.62  tff(c_12027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11926, c_28])).
% 11.74/4.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.62  
% 11.74/4.62  Inference rules
% 11.74/4.62  ----------------------
% 11.74/4.62  #Ref     : 0
% 11.74/4.62  #Sup     : 2892
% 11.74/4.62  #Fact    : 0
% 11.74/4.62  #Define  : 0
% 11.74/4.62  #Split   : 0
% 11.74/4.62  #Chain   : 0
% 11.74/4.62  #Close   : 0
% 11.74/4.62  
% 11.74/4.62  Ordering : KBO
% 11.74/4.62  
% 11.74/4.62  Simplification rules
% 11.74/4.62  ----------------------
% 11.74/4.62  #Subsume      : 145
% 11.74/4.62  #Demod        : 5494
% 11.74/4.62  #Tautology    : 1649
% 11.74/4.62  #SimpNegUnit  : 0
% 11.74/4.62  #BackRed      : 1
% 11.74/4.62  
% 11.74/4.62  #Partial instantiations: 0
% 11.74/4.62  #Strategies tried      : 1
% 11.74/4.62  
% 11.74/4.62  Timing (in seconds)
% 11.74/4.62  ----------------------
% 11.90/4.62  Preprocessing        : 0.51
% 11.90/4.62  Parsing              : 0.28
% 11.90/4.62  CNF conversion       : 0.03
% 11.90/4.62  Main loop            : 3.13
% 11.90/4.62  Inferencing          : 0.92
% 11.90/4.62  Reduction            : 1.77
% 11.90/4.62  Demodulation         : 1.60
% 11.90/4.62  BG Simplification    : 0.12
% 11.90/4.62  Subsumption          : 0.23
% 11.90/4.62  Abstraction          : 0.24
% 11.90/4.62  MUC search           : 0.00
% 11.90/4.62  Cooper               : 0.00
% 11.90/4.62  Total                : 3.67
% 11.90/4.62  Index Insertion      : 0.00
% 11.90/4.62  Index Deletion       : 0.00
% 11.90/4.62  Index Matching       : 0.00
% 11.90/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

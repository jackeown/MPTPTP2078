%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_4,plain,(
    ! [C_11,E_13,B_10,F_14,G_15,D_12,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k2_enumset1(D_12,E_13,F_14,G_15)) = k5_enumset1(A_9,B_10,C_11,D_12,E_13,F_14,G_15) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [F_74,B_78,D_77,G_75,C_79,E_76,H_81,A_80] : k2_xboole_0(k2_enumset1(A_80,B_78,C_79,D_77),k2_enumset1(E_76,F_74,G_75,H_81)) = k6_enumset1(A_80,B_78,C_79,D_77,E_76,F_74,G_75,H_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [F_74,C_18,G_75,B_17,A_16,E_76,H_81] : k6_enumset1(A_16,A_16,B_17,C_18,E_76,F_74,G_75,H_81) = k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k2_enumset1(E_76,F_74,G_75,H_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_155])).

tff(c_170,plain,(
    ! [F_74,C_18,G_75,B_17,A_16,E_76,H_81] : k6_enumset1(A_16,A_16,B_17,C_18,E_76,F_74,G_75,H_81) = k5_enumset1(A_16,B_17,C_18,E_76,F_74,G_75,H_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_164])).

tff(c_14,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.50  
% 1.99/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.50  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.50  
% 1.99/1.50  %Foreground sorts:
% 1.99/1.50  
% 1.99/1.50  
% 1.99/1.50  %Background operators:
% 1.99/1.50  
% 1.99/1.50  
% 1.99/1.50  %Foreground operators:
% 1.99/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.50  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.50  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.50  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.50  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.50  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.50  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.50  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.50  
% 1.99/1.51  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 1.99/1.51  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.99/1.51  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 1.99/1.51  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.99/1.51  tff(c_4, plain, (![C_11, E_13, B_10, F_14, G_15, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k2_enumset1(D_12, E_13, F_14, G_15))=k5_enumset1(A_9, B_10, C_11, D_12, E_13, F_14, G_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.51  tff(c_6, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.51  tff(c_155, plain, (![F_74, B_78, D_77, G_75, C_79, E_76, H_81, A_80]: (k2_xboole_0(k2_enumset1(A_80, B_78, C_79, D_77), k2_enumset1(E_76, F_74, G_75, H_81))=k6_enumset1(A_80, B_78, C_79, D_77, E_76, F_74, G_75, H_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.51  tff(c_164, plain, (![F_74, C_18, G_75, B_17, A_16, E_76, H_81]: (k6_enumset1(A_16, A_16, B_17, C_18, E_76, F_74, G_75, H_81)=k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k2_enumset1(E_76, F_74, G_75, H_81)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_155])).
% 1.99/1.51  tff(c_170, plain, (![F_74, C_18, G_75, B_17, A_16, E_76, H_81]: (k6_enumset1(A_16, A_16, B_17, C_18, E_76, F_74, G_75, H_81)=k5_enumset1(A_16, B_17, C_18, E_76, F_74, G_75, H_81))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_164])).
% 1.99/1.51  tff(c_14, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.51  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_14])).
% 1.99/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.51  
% 1.99/1.51  Inference rules
% 1.99/1.51  ----------------------
% 1.99/1.51  #Ref     : 0
% 1.99/1.51  #Sup     : 43
% 1.99/1.51  #Fact    : 0
% 1.99/1.51  #Define  : 0
% 1.99/1.51  #Split   : 0
% 1.99/1.51  #Chain   : 0
% 1.99/1.51  #Close   : 0
% 1.99/1.51  
% 1.99/1.51  Ordering : KBO
% 1.99/1.51  
% 1.99/1.51  Simplification rules
% 1.99/1.51  ----------------------
% 1.99/1.51  #Subsume      : 4
% 1.99/1.51  #Demod        : 9
% 1.99/1.51  #Tautology    : 33
% 1.99/1.51  #SimpNegUnit  : 0
% 1.99/1.51  #BackRed      : 1
% 1.99/1.51  
% 1.99/1.51  #Partial instantiations: 0
% 1.99/1.51  #Strategies tried      : 1
% 1.99/1.51  
% 1.99/1.51  Timing (in seconds)
% 1.99/1.51  ----------------------
% 1.99/1.51  Preprocessing        : 0.45
% 1.99/1.51  Parsing              : 0.24
% 1.99/1.51  CNF conversion       : 0.03
% 1.99/1.51  Main loop            : 0.15
% 1.99/1.51  Inferencing          : 0.07
% 1.99/1.51  Reduction            : 0.05
% 1.99/1.52  Demodulation         : 0.04
% 1.99/1.52  BG Simplification    : 0.02
% 1.99/1.52  Subsumption          : 0.01
% 1.99/1.52  Abstraction          : 0.01
% 1.99/1.52  MUC search           : 0.00
% 1.99/1.52  Cooper               : 0.00
% 1.99/1.52  Total                : 0.62
% 1.99/1.52  Index Insertion      : 0.00
% 1.99/1.52  Index Deletion       : 0.00
% 1.99/1.52  Index Matching       : 0.00
% 1.99/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

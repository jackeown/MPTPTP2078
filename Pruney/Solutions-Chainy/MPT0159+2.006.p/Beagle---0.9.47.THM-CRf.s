%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.43s
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
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_8,plain,(
    ! [A_23,B_24,F_28,D_26,G_29,C_25,E_27] : k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k2_enumset1(D_26,E_27,F_28,G_29)) = k5_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,G_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [B_111,F_108,A_109,H_114,D_115,G_113,E_110,C_112] : k2_xboole_0(k2_enumset1(A_109,B_111,C_112,D_115),k2_enumset1(E_110,F_108,G_113,H_114)) = k6_enumset1(A_109,B_111,C_112,D_115,E_110,F_108,G_113,H_114) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_338,plain,(
    ! [F_108,B_39,H_114,G_113,E_110,A_38,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,E_110,F_108,G_113,H_114) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k2_enumset1(E_110,F_108,G_113,H_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_329])).

tff(c_344,plain,(
    ! [F_108,B_39,H_114,G_113,E_110,A_38,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,E_110,F_108,G_113,H_114) = k5_enumset1(A_38,B_39,C_40,E_110,F_108,G_113,H_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_338])).

tff(c_16,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.51  
% 3.43/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.51  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.51  
% 3.43/1.51  %Foreground sorts:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Background operators:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Foreground operators:
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.43/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.43/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.43/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.43/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.51  
% 3.43/1.52  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 3.43/1.52  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.43/1.52  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 3.43/1.52  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.43/1.52  tff(c_8, plain, (![A_23, B_24, F_28, D_26, G_29, C_25, E_27]: (k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k2_enumset1(D_26, E_27, F_28, G_29))=k5_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, G_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.52  tff(c_12, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.52  tff(c_329, plain, (![B_111, F_108, A_109, H_114, D_115, G_113, E_110, C_112]: (k2_xboole_0(k2_enumset1(A_109, B_111, C_112, D_115), k2_enumset1(E_110, F_108, G_113, H_114))=k6_enumset1(A_109, B_111, C_112, D_115, E_110, F_108, G_113, H_114))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.52  tff(c_338, plain, (![F_108, B_39, H_114, G_113, E_110, A_38, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, E_110, F_108, G_113, H_114)=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k2_enumset1(E_110, F_108, G_113, H_114)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_329])).
% 3.43/1.52  tff(c_344, plain, (![F_108, B_39, H_114, G_113, E_110, A_38, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, E_110, F_108, G_113, H_114)=k5_enumset1(A_38, B_39, C_40, E_110, F_108, G_113, H_114))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_338])).
% 3.43/1.52  tff(c_16, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.43/1.52  tff(c_868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_16])).
% 3.43/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.52  
% 3.43/1.52  Inference rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Ref     : 0
% 3.43/1.52  #Sup     : 219
% 3.43/1.52  #Fact    : 0
% 3.43/1.52  #Define  : 0
% 3.43/1.52  #Split   : 0
% 3.43/1.52  #Chain   : 0
% 3.43/1.52  #Close   : 0
% 3.43/1.52  
% 3.43/1.52  Ordering : KBO
% 3.43/1.52  
% 3.43/1.52  Simplification rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Subsume      : 71
% 3.43/1.52  #Demod        : 18
% 3.43/1.52  #Tautology    : 64
% 3.43/1.52  #SimpNegUnit  : 0
% 3.43/1.52  #BackRed      : 1
% 3.43/1.52  
% 3.43/1.52  #Partial instantiations: 0
% 3.43/1.52  #Strategies tried      : 1
% 3.43/1.52  
% 3.43/1.52  Timing (in seconds)
% 3.43/1.52  ----------------------
% 3.43/1.52  Preprocessing        : 0.31
% 3.43/1.52  Parsing              : 0.16
% 3.43/1.52  CNF conversion       : 0.02
% 3.43/1.52  Main loop            : 0.45
% 3.43/1.52  Inferencing          : 0.18
% 3.43/1.52  Reduction            : 0.17
% 3.43/1.52  Demodulation         : 0.15
% 3.43/1.52  BG Simplification    : 0.03
% 3.43/1.52  Subsumption          : 0.05
% 3.43/1.52  Abstraction          : 0.03
% 3.43/1.52  MUC search           : 0.00
% 3.43/1.52  Cooper               : 0.00
% 3.43/1.52  Total                : 0.78
% 3.43/1.53  Index Insertion      : 0.00
% 3.43/1.53  Index Deletion       : 0.00
% 3.43/1.53  Index Matching       : 0.00
% 3.43/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

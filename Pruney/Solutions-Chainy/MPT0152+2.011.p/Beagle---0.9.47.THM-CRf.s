%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
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
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36),k2_tarski(G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_246,plain,(
    ! [G_89,D_95,C_90,B_91,E_92,F_93,A_94] : k2_xboole_0(k4_enumset1(A_94,B_91,C_90,D_95,E_92,F_93),k1_tarski(G_89)) = k5_enumset1(A_94,B_91,C_90,D_95,E_92,F_93,G_89) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_717,plain,(
    ! [C_211,D_209,F_206,C_210,A_205,G_212,E_208,B_207] : k2_xboole_0(k4_enumset1(A_205,B_207,C_210,D_209,E_208,F_206),k2_xboole_0(k1_tarski(G_212),C_211)) = k2_xboole_0(k5_enumset1(A_205,B_207,C_210,D_209,E_208,F_206,G_212),C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_2])).

tff(c_756,plain,(
    ! [B_5,D_209,A_4,F_206,C_210,A_205,E_208,B_207] : k2_xboole_0(k5_enumset1(A_205,B_207,C_210,D_209,E_208,F_206,A_4),k1_tarski(B_5)) = k2_xboole_0(k4_enumset1(A_205,B_207,C_210,D_209,E_208,F_206),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_717])).

tff(c_760,plain,(
    ! [B_5,D_209,A_4,F_206,C_210,A_205,E_208,B_207] : k2_xboole_0(k5_enumset1(A_205,B_207,C_210,D_209,E_208,F_206,A_4),k1_tarski(B_5)) = k6_enumset1(A_205,B_207,C_210,D_209,E_208,F_206,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_756])).

tff(c_18,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.50  
% 3.13/1.51  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.13/1.51  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.13/1.51  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 3.13/1.51  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.13/1.51  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 3.13/1.51  tff(c_16, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36), k2_tarski(G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.51  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.51  tff(c_246, plain, (![G_89, D_95, C_90, B_91, E_92, F_93, A_94]: (k2_xboole_0(k4_enumset1(A_94, B_91, C_90, D_95, E_92, F_93), k1_tarski(G_89))=k5_enumset1(A_94, B_91, C_90, D_95, E_92, F_93, G_89))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.51  tff(c_717, plain, (![C_211, D_209, F_206, C_210, A_205, G_212, E_208, B_207]: (k2_xboole_0(k4_enumset1(A_205, B_207, C_210, D_209, E_208, F_206), k2_xboole_0(k1_tarski(G_212), C_211))=k2_xboole_0(k5_enumset1(A_205, B_207, C_210, D_209, E_208, F_206, G_212), C_211))), inference(superposition, [status(thm), theory('equality')], [c_246, c_2])).
% 3.13/1.51  tff(c_756, plain, (![B_5, D_209, A_4, F_206, C_210, A_205, E_208, B_207]: (k2_xboole_0(k5_enumset1(A_205, B_207, C_210, D_209, E_208, F_206, A_4), k1_tarski(B_5))=k2_xboole_0(k4_enumset1(A_205, B_207, C_210, D_209, E_208, F_206), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_717])).
% 3.13/1.51  tff(c_760, plain, (![B_5, D_209, A_4, F_206, C_210, A_205, E_208, B_207]: (k2_xboole_0(k5_enumset1(A_205, B_207, C_210, D_209, E_208, F_206, A_4), k1_tarski(B_5))=k6_enumset1(A_205, B_207, C_210, D_209, E_208, F_206, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_756])).
% 3.13/1.51  tff(c_18, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.51  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_760, c_18])).
% 3.13/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  Inference rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Ref     : 0
% 3.13/1.51  #Sup     : 199
% 3.13/1.51  #Fact    : 0
% 3.13/1.51  #Define  : 0
% 3.13/1.51  #Split   : 0
% 3.13/1.51  #Chain   : 0
% 3.13/1.51  #Close   : 0
% 3.13/1.51  
% 3.13/1.51  Ordering : KBO
% 3.13/1.51  
% 3.13/1.51  Simplification rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Subsume      : 0
% 3.13/1.51  #Demod        : 92
% 3.13/1.51  #Tautology    : 96
% 3.13/1.51  #SimpNegUnit  : 0
% 3.13/1.51  #BackRed      : 1
% 3.13/1.51  
% 3.13/1.51  #Partial instantiations: 0
% 3.13/1.51  #Strategies tried      : 1
% 3.13/1.51  
% 3.13/1.51  Timing (in seconds)
% 3.13/1.51  ----------------------
% 3.13/1.52  Preprocessing        : 0.30
% 3.13/1.52  Parsing              : 0.17
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.40
% 3.13/1.52  Inferencing          : 0.18
% 3.13/1.52  Reduction            : 0.13
% 3.13/1.52  Demodulation         : 0.10
% 3.13/1.52  BG Simplification    : 0.03
% 3.13/1.52  Subsumption          : 0.04
% 3.13/1.52  Abstraction          : 0.03
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.72
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

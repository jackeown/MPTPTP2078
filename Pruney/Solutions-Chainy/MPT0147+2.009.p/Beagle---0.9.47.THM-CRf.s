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
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_20,plain,(
    ! [D_36,G_39,F_38,E_37,A_33,B_34,H_40,C_35] : k2_xboole_0(k1_tarski(A_33),k5_enumset1(B_34,C_35,D_36,E_37,F_38,G_39,H_40)) = k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,H_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [B_27,D_29,G_32,A_26,E_30,F_31,C_28] : k2_xboole_0(k2_tarski(A_26,B_27),k3_enumset1(C_28,D_29,E_30,F_31,G_32)) = k5_enumset1(A_26,B_27,C_28,D_29,E_30,F_31,G_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_436,plain,(
    ! [C_78,A_82,D_80,B_79,E_81,F_83] : k2_xboole_0(k1_tarski(A_82),k3_enumset1(B_79,C_78,D_80,E_81,F_83)) = k4_enumset1(A_82,B_79,C_78,D_80,E_81,F_83) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k2_xboole_0(A_47,B_48),C_49) = k2_xboole_0(A_47,k2_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_15,B_16,C_49] : k2_xboole_0(k1_tarski(A_15),k2_xboole_0(k1_tarski(B_16),C_49)) = k2_xboole_0(k2_tarski(A_15,B_16),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_442,plain,(
    ! [A_15,C_78,A_82,D_80,B_79,E_81,F_83] : k2_xboole_0(k2_tarski(A_15,A_82),k3_enumset1(B_79,C_78,D_80,E_81,F_83)) = k2_xboole_0(k1_tarski(A_15),k4_enumset1(A_82,B_79,C_78,D_80,E_81,F_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_66])).

tff(c_2335,plain,(
    ! [C_200,F_199,A_203,D_198,B_202,E_204,A_201] : k2_xboole_0(k1_tarski(A_201),k4_enumset1(A_203,B_202,C_200,D_198,E_204,F_199)) = k5_enumset1(A_201,A_203,B_202,C_200,D_198,E_204,F_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_442])).

tff(c_2377,plain,(
    ! [C_200,A_15,F_199,A_203,D_198,B_202,E_204,A_201] : k2_xboole_0(k2_tarski(A_15,A_201),k4_enumset1(A_203,B_202,C_200,D_198,E_204,F_199)) = k2_xboole_0(k1_tarski(A_15),k5_enumset1(A_201,A_203,B_202,C_200,D_198,E_204,F_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2335,c_66])).

tff(c_2390,plain,(
    ! [C_200,A_15,F_199,A_203,D_198,B_202,E_204,A_201] : k2_xboole_0(k2_tarski(A_15,A_201),k4_enumset1(A_203,B_202,C_200,D_198,E_204,F_199)) = k6_enumset1(A_15,A_201,A_203,B_202,C_200,D_198,E_204,F_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2377])).

tff(c_22,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.64  
% 7.57/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.65  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 7.57/2.65  
% 7.57/2.65  %Foreground sorts:
% 7.57/2.65  
% 7.57/2.65  
% 7.57/2.65  %Background operators:
% 7.57/2.65  
% 7.57/2.65  
% 7.57/2.65  %Foreground operators:
% 7.57/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.57/2.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.57/2.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.57/2.65  tff('#skF_7', type, '#skF_7': $i).
% 7.57/2.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.57/2.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.57/2.65  tff('#skF_5', type, '#skF_5': $i).
% 7.57/2.65  tff('#skF_6', type, '#skF_6': $i).
% 7.57/2.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.57/2.65  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.65  tff('#skF_3', type, '#skF_3': $i).
% 7.57/2.65  tff('#skF_1', type, '#skF_1': $i).
% 7.57/2.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.65  tff('#skF_8', type, '#skF_8': $i).
% 7.57/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.65  tff('#skF_4', type, '#skF_4': $i).
% 7.57/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.57/2.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.57/2.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.65  
% 7.81/2.66  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 7.81/2.66  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 7.81/2.66  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 7.81/2.66  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 7.81/2.66  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.81/2.66  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 7.81/2.66  tff(c_20, plain, (![D_36, G_39, F_38, E_37, A_33, B_34, H_40, C_35]: (k2_xboole_0(k1_tarski(A_33), k5_enumset1(B_34, C_35, D_36, E_37, F_38, G_39, H_40))=k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, H_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.81/2.66  tff(c_18, plain, (![B_27, D_29, G_32, A_26, E_30, F_31, C_28]: (k2_xboole_0(k2_tarski(A_26, B_27), k3_enumset1(C_28, D_29, E_30, F_31, G_32))=k5_enumset1(A_26, B_27, C_28, D_29, E_30, F_31, G_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.81/2.66  tff(c_436, plain, (![C_78, A_82, D_80, B_79, E_81, F_83]: (k2_xboole_0(k1_tarski(A_82), k3_enumset1(B_79, C_78, D_80, E_81, F_83))=k4_enumset1(A_82, B_79, C_78, D_80, E_81, F_83))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.66  tff(c_12, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.81/2.66  tff(c_51, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k2_xboole_0(A_47, B_48), C_49)=k2_xboole_0(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/2.66  tff(c_66, plain, (![A_15, B_16, C_49]: (k2_xboole_0(k1_tarski(A_15), k2_xboole_0(k1_tarski(B_16), C_49))=k2_xboole_0(k2_tarski(A_15, B_16), C_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 7.81/2.66  tff(c_442, plain, (![A_15, C_78, A_82, D_80, B_79, E_81, F_83]: (k2_xboole_0(k2_tarski(A_15, A_82), k3_enumset1(B_79, C_78, D_80, E_81, F_83))=k2_xboole_0(k1_tarski(A_15), k4_enumset1(A_82, B_79, C_78, D_80, E_81, F_83)))), inference(superposition, [status(thm), theory('equality')], [c_436, c_66])).
% 7.81/2.66  tff(c_2335, plain, (![C_200, F_199, A_203, D_198, B_202, E_204, A_201]: (k2_xboole_0(k1_tarski(A_201), k4_enumset1(A_203, B_202, C_200, D_198, E_204, F_199))=k5_enumset1(A_201, A_203, B_202, C_200, D_198, E_204, F_199))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_442])).
% 7.81/2.66  tff(c_2377, plain, (![C_200, A_15, F_199, A_203, D_198, B_202, E_204, A_201]: (k2_xboole_0(k2_tarski(A_15, A_201), k4_enumset1(A_203, B_202, C_200, D_198, E_204, F_199))=k2_xboole_0(k1_tarski(A_15), k5_enumset1(A_201, A_203, B_202, C_200, D_198, E_204, F_199)))), inference(superposition, [status(thm), theory('equality')], [c_2335, c_66])).
% 7.81/2.66  tff(c_2390, plain, (![C_200, A_15, F_199, A_203, D_198, B_202, E_204, A_201]: (k2_xboole_0(k2_tarski(A_15, A_201), k4_enumset1(A_203, B_202, C_200, D_198, E_204, F_199))=k6_enumset1(A_15, A_201, A_203, B_202, C_200, D_198, E_204, F_199))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2377])).
% 7.81/2.66  tff(c_22, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.81/2.66  tff(c_5272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2390, c_22])).
% 7.81/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.66  
% 7.81/2.66  Inference rules
% 7.81/2.66  ----------------------
% 7.81/2.66  #Ref     : 0
% 7.81/2.66  #Sup     : 1282
% 7.81/2.66  #Fact    : 0
% 7.81/2.66  #Define  : 0
% 7.81/2.66  #Split   : 0
% 7.81/2.66  #Chain   : 0
% 7.81/2.66  #Close   : 0
% 7.81/2.66  
% 7.81/2.66  Ordering : KBO
% 7.81/2.66  
% 7.81/2.66  Simplification rules
% 7.81/2.66  ----------------------
% 7.81/2.66  #Subsume      : 0
% 7.81/2.66  #Demod        : 2889
% 7.81/2.66  #Tautology    : 582
% 7.81/2.66  #SimpNegUnit  : 0
% 7.81/2.66  #BackRed      : 1
% 7.81/2.66  
% 7.81/2.66  #Partial instantiations: 0
% 7.81/2.66  #Strategies tried      : 1
% 7.81/2.66  
% 7.81/2.66  Timing (in seconds)
% 7.81/2.66  ----------------------
% 7.81/2.66  Preprocessing        : 0.30
% 7.81/2.66  Parsing              : 0.17
% 7.81/2.66  CNF conversion       : 0.02
% 7.81/2.66  Main loop            : 1.59
% 7.81/2.66  Inferencing          : 0.49
% 7.81/2.66  Reduction            : 0.83
% 7.81/2.66  Demodulation         : 0.74
% 7.81/2.66  BG Simplification    : 0.08
% 7.81/2.66  Subsumption          : 0.14
% 7.81/2.66  Abstraction          : 0.15
% 7.81/2.66  MUC search           : 0.00
% 7.81/2.66  Cooper               : 0.00
% 7.81/2.66  Total                : 1.92
% 7.81/2.66  Index Insertion      : 0.00
% 7.81/2.66  Index Deletion       : 0.00
% 7.81/2.66  Index Matching       : 0.00
% 7.81/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

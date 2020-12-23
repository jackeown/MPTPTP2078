%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:55 EST 2020

% Result     : Theorem 41.60s
% Output     : CNFRefutation 41.60s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,G_21,E_19,H_22,F_20,C_17] : k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k2_enumset1(E_19,F_20,G_21,H_22)) = k6_enumset1(A_15,B_16,C_17,D_18,E_19,F_20,G_21,H_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_tarski(A_28),k1_enumset1(B_29,C_30,D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_361,plain,(
    ! [E_87,D_86,B_85,A_84,C_88] : k2_xboole_0(k2_enumset1(A_84,B_85,C_88,D_86),k1_tarski(E_87)) = k3_enumset1(A_84,B_85,C_88,D_86,E_87) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3767,plain,(
    ! [B_251,D_254,E_252,C_253,C_250,A_249] : k2_xboole_0(k2_enumset1(A_249,B_251,C_250,D_254),k2_xboole_0(k1_tarski(E_252),C_253)) = k2_xboole_0(k3_enumset1(A_249,B_251,C_250,D_254,E_252),C_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_2])).

tff(c_3874,plain,(
    ! [C_30,B_251,D_254,D_31,B_29,C_250,A_28,A_249] : k2_xboole_0(k3_enumset1(A_249,B_251,C_250,D_254,A_28),k1_enumset1(B_29,C_30,D_31)) = k2_xboole_0(k2_enumset1(A_249,B_251,C_250,D_254),k2_enumset1(A_28,B_29,C_30,D_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3767])).

tff(c_3914,plain,(
    ! [C_30,B_251,D_254,D_31,B_29,C_250,A_28,A_249] : k2_xboole_0(k3_enumset1(A_249,B_251,C_250,D_254,A_28),k1_enumset1(B_29,C_30,D_31)) = k6_enumset1(A_249,B_251,C_250,D_254,A_28,B_29,C_30,D_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3874])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,G_14] : k2_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11),k1_enumset1(E_12,F_13,G_14)) = k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_280,plain,(
    ! [B_75,A_77,D_78,E_74,C_76] : k2_xboole_0(k1_tarski(A_77),k2_enumset1(B_75,C_76,D_78,E_74)) = k3_enumset1(A_77,B_75,C_76,D_78,E_74) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5253,plain,(
    ! [B_301,C_302,D_299,E_298,C_300,A_297] : k2_xboole_0(k1_tarski(A_297),k2_xboole_0(k2_enumset1(B_301,C_300,D_299,E_298),C_302)) = k2_xboole_0(k3_enumset1(A_297,B_301,C_300,D_299,E_298),C_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_2])).

tff(c_5352,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,A_297,G_14] : k2_xboole_0(k3_enumset1(A_297,A_8,B_9,C_10,D_11),k1_enumset1(E_12,F_13,G_14)) = k2_xboole_0(k1_tarski(A_297),k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5253])).

tff(c_93587,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,A_297,G_14] : k2_xboole_0(k1_tarski(A_297),k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14)) = k6_enumset1(A_297,A_8,B_9,C_10,D_11,E_12,F_13,G_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3914,c_5352])).

tff(c_22,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k5_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93587,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.60/30.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.60/30.81  
% 41.60/30.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.60/30.81  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 41.60/30.81  
% 41.60/30.81  %Foreground sorts:
% 41.60/30.81  
% 41.60/30.81  
% 41.60/30.81  %Background operators:
% 41.60/30.81  
% 41.60/30.81  
% 41.60/30.81  %Foreground operators:
% 41.60/30.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.60/30.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 41.60/30.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 41.60/30.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 41.60/30.81  tff('#skF_7', type, '#skF_7': $i).
% 41.60/30.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 41.60/30.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 41.60/30.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 41.60/30.81  tff('#skF_5', type, '#skF_5': $i).
% 41.60/30.81  tff('#skF_6', type, '#skF_6': $i).
% 41.60/30.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 41.60/30.81  tff('#skF_2', type, '#skF_2': $i).
% 41.60/30.81  tff('#skF_3', type, '#skF_3': $i).
% 41.60/30.81  tff('#skF_1', type, '#skF_1': $i).
% 41.60/30.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 41.60/30.81  tff('#skF_8', type, '#skF_8': $i).
% 41.60/30.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.60/30.81  tff('#skF_4', type, '#skF_4': $i).
% 41.60/30.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.60/30.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.60/30.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 41.60/30.81  
% 41.60/30.82  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 41.60/30.82  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 41.60/30.82  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 41.60/30.82  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 41.60/30.82  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 41.60/30.82  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 41.60/30.82  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 41.60/30.82  tff(c_10, plain, (![B_16, A_15, D_18, G_21, E_19, H_22, F_20, C_17]: (k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k2_enumset1(E_19, F_20, G_21, H_22))=k6_enumset1(A_15, B_16, C_17, D_18, E_19, F_20, G_21, H_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 41.60/30.82  tff(c_16, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_tarski(A_28), k1_enumset1(B_29, C_30, D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.60/30.82  tff(c_361, plain, (![E_87, D_86, B_85, A_84, C_88]: (k2_xboole_0(k2_enumset1(A_84, B_85, C_88, D_86), k1_tarski(E_87))=k3_enumset1(A_84, B_85, C_88, D_86, E_87))), inference(cnfTransformation, [status(thm)], [f_45])).
% 41.60/30.82  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.60/30.82  tff(c_3767, plain, (![B_251, D_254, E_252, C_253, C_250, A_249]: (k2_xboole_0(k2_enumset1(A_249, B_251, C_250, D_254), k2_xboole_0(k1_tarski(E_252), C_253))=k2_xboole_0(k3_enumset1(A_249, B_251, C_250, D_254, E_252), C_253))), inference(superposition, [status(thm), theory('equality')], [c_361, c_2])).
% 41.60/30.82  tff(c_3874, plain, (![C_30, B_251, D_254, D_31, B_29, C_250, A_28, A_249]: (k2_xboole_0(k3_enumset1(A_249, B_251, C_250, D_254, A_28), k1_enumset1(B_29, C_30, D_31))=k2_xboole_0(k2_enumset1(A_249, B_251, C_250, D_254), k2_enumset1(A_28, B_29, C_30, D_31)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3767])).
% 41.60/30.82  tff(c_3914, plain, (![C_30, B_251, D_254, D_31, B_29, C_250, A_28, A_249]: (k2_xboole_0(k3_enumset1(A_249, B_251, C_250, D_254, A_28), k1_enumset1(B_29, C_30, D_31))=k6_enumset1(A_249, B_251, C_250, D_254, A_28, B_29, C_30, D_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3874])).
% 41.60/30.82  tff(c_8, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, G_14]: (k2_xboole_0(k2_enumset1(A_8, B_9, C_10, D_11), k1_enumset1(E_12, F_13, G_14))=k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 41.60/30.82  tff(c_280, plain, (![B_75, A_77, D_78, E_74, C_76]: (k2_xboole_0(k1_tarski(A_77), k2_enumset1(B_75, C_76, D_78, E_74))=k3_enumset1(A_77, B_75, C_76, D_78, E_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.60/30.82  tff(c_5253, plain, (![B_301, C_302, D_299, E_298, C_300, A_297]: (k2_xboole_0(k1_tarski(A_297), k2_xboole_0(k2_enumset1(B_301, C_300, D_299, E_298), C_302))=k2_xboole_0(k3_enumset1(A_297, B_301, C_300, D_299, E_298), C_302))), inference(superposition, [status(thm), theory('equality')], [c_280, c_2])).
% 41.60/30.82  tff(c_5352, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, A_297, G_14]: (k2_xboole_0(k3_enumset1(A_297, A_8, B_9, C_10, D_11), k1_enumset1(E_12, F_13, G_14))=k2_xboole_0(k1_tarski(A_297), k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5253])).
% 41.60/30.82  tff(c_93587, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, A_297, G_14]: (k2_xboole_0(k1_tarski(A_297), k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14))=k6_enumset1(A_297, A_8, B_9, C_10, D_11, E_12, F_13, G_14))), inference(demodulation, [status(thm), theory('equality')], [c_3914, c_5352])).
% 41.60/30.82  tff(c_22, plain, (k2_xboole_0(k1_tarski('#skF_1'), k5_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 41.60/30.82  tff(c_93590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93587, c_22])).
% 41.60/30.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.60/30.82  
% 41.60/30.82  Inference rules
% 41.60/30.82  ----------------------
% 41.60/30.82  #Ref     : 0
% 41.60/30.82  #Sup     : 21170
% 41.60/30.82  #Fact    : 0
% 41.60/30.82  #Define  : 0
% 41.60/30.82  #Split   : 0
% 41.60/30.82  #Chain   : 0
% 41.60/30.82  #Close   : 0
% 41.60/30.82  
% 41.60/30.82  Ordering : KBO
% 41.60/30.82  
% 41.60/30.82  Simplification rules
% 41.60/30.82  ----------------------
% 41.60/30.82  #Subsume      : 26
% 41.60/30.82  #Demod        : 59915
% 41.60/30.82  #Tautology    : 13839
% 41.60/30.82  #SimpNegUnit  : 0
% 41.60/30.82  #BackRed      : 2
% 41.60/30.82  
% 41.60/30.82  #Partial instantiations: 0
% 41.60/30.82  #Strategies tried      : 1
% 41.60/30.82  
% 41.60/30.82  Timing (in seconds)
% 41.60/30.82  ----------------------
% 41.60/30.82  Preprocessing        : 0.29
% 41.60/30.82  Parsing              : 0.16
% 41.60/30.82  CNF conversion       : 0.02
% 41.60/30.82  Main loop            : 29.75
% 41.60/30.82  Inferencing          : 3.65
% 41.60/30.82  Reduction            : 23.27
% 41.60/30.82  Demodulation         : 22.38
% 41.60/30.82  BG Simplification    : 0.47
% 41.60/30.82  Subsumption          : 1.93
% 41.60/30.82  Abstraction          : 1.22
% 41.60/30.82  MUC search           : 0.00
% 41.60/30.82  Cooper               : 0.00
% 41.60/30.82  Total                : 30.07
% 41.60/30.82  Index Insertion      : 0.00
% 41.60/30.82  Index Deletion       : 0.00
% 41.60/30.82  Index Matching       : 0.00
% 41.60/30.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

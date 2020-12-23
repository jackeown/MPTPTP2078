%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   23 (  35 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_6,plain,(
    ! [G_13,D_10,A_7,F_12,B_8,E_11,C_9] : k2_xboole_0(k2_enumset1(A_7,B_8,C_9,D_10),k1_enumset1(E_11,F_12,G_13)) = k5_enumset1(A_7,B_8,C_9,D_10,E_11,F_12,G_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k2_xboole_0(k2_enumset1(A_23,B_24,C_25,D_26),k1_tarski(E_27)) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_39,B_40),C_41),D_42) = k2_xboole_0(A_39,k2_xboole_0(k2_xboole_0(B_40,C_41),D_42)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_330,plain,(
    ! [A_76,C_78,D_77,B_75,C_74] : k2_xboole_0(k2_tarski(A_76,B_75),k2_xboole_0(k2_xboole_0(k1_tarski(C_78),C_74),D_77)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_76,B_75,C_78),C_74),D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_367,plain,(
    ! [A_76,D_77,B_75,A_14,B_15] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_76,B_75,A_14),k1_tarski(B_15)),D_77) = k2_xboole_0(k2_tarski(A_76,B_75),k2_xboole_0(k2_tarski(A_14,B_15),D_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_330])).

tff(c_377,plain,(
    ! [A_82,B_81,D_79,A_83,B_80] : k2_xboole_0(k2_tarski(A_82,B_80),k2_xboole_0(k2_tarski(A_83,B_81),D_79)) = k2_xboole_0(k2_enumset1(A_82,B_80,A_83,B_81),D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_407,plain,(
    ! [C_18,A_82,B_17,A_16,B_80] : k2_xboole_0(k2_enumset1(A_82,B_80,A_16,B_17),k1_tarski(C_18)) = k2_xboole_0(k2_tarski(A_82,B_80),k1_enumset1(A_16,B_17,C_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_377])).

tff(c_413,plain,(
    ! [A_87,A_85,B_84,C_88,B_86] : k2_xboole_0(k2_tarski(A_87,B_86),k1_enumset1(A_85,B_84,C_88)) = k3_enumset1(A_87,B_86,A_85,B_84,C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_407])).

tff(c_375,plain,(
    ! [A_76,D_77,B_75,A_14,B_15] : k2_xboole_0(k2_tarski(A_76,B_75),k2_xboole_0(k2_tarski(A_14,B_15),D_77)) = k2_xboole_0(k2_enumset1(A_76,B_75,A_14,B_15),D_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_419,plain,(
    ! [A_87,A_85,A_76,B_75,B_84,C_88,B_86] : k2_xboole_0(k2_enumset1(A_76,B_75,A_87,B_86),k1_enumset1(A_85,B_84,C_88)) = k2_xboole_0(k2_tarski(A_76,B_75),k3_enumset1(A_87,B_86,A_85,B_84,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_375])).

tff(c_436,plain,(
    ! [A_87,A_85,A_76,B_75,B_84,C_88,B_86] : k2_xboole_0(k2_tarski(A_76,B_75),k3_enumset1(A_87,B_86,A_85,B_84,C_88)) = k5_enumset1(A_76,B_75,A_87,B_86,A_85,B_84,C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_419])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.40  
% 2.67/1.41  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.67/1.41  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.67/1.41  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.67/1.41  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.67/1.41  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.67/1.41  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 2.67/1.41  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.67/1.41  tff(c_6, plain, (![G_13, D_10, A_7, F_12, B_8, E_11, C_9]: (k2_xboole_0(k2_enumset1(A_7, B_8, C_9, D_10), k1_enumset1(E_11, F_12, G_13))=k5_enumset1(A_7, B_8, C_9, D_10, E_11, F_12, G_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.41  tff(c_14, plain, (![A_23, B_24, D_26, C_25, E_27]: (k2_xboole_0(k2_enumset1(A_23, B_24, C_25, D_26), k1_tarski(E_27))=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.41  tff(c_10, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.41  tff(c_12, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.41  tff(c_8, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.41  tff(c_59, plain, (![A_39, B_40, C_41, D_42]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_39, B_40), C_41), D_42)=k2_xboole_0(A_39, k2_xboole_0(k2_xboole_0(B_40, C_41), D_42)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.41  tff(c_330, plain, (![A_76, C_78, D_77, B_75, C_74]: (k2_xboole_0(k2_tarski(A_76, B_75), k2_xboole_0(k2_xboole_0(k1_tarski(C_78), C_74), D_77))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_76, B_75, C_78), C_74), D_77))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 2.67/1.41  tff(c_367, plain, (![A_76, D_77, B_75, A_14, B_15]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_76, B_75, A_14), k1_tarski(B_15)), D_77)=k2_xboole_0(k2_tarski(A_76, B_75), k2_xboole_0(k2_tarski(A_14, B_15), D_77)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_330])).
% 2.67/1.41  tff(c_377, plain, (![A_82, B_81, D_79, A_83, B_80]: (k2_xboole_0(k2_tarski(A_82, B_80), k2_xboole_0(k2_tarski(A_83, B_81), D_79))=k2_xboole_0(k2_enumset1(A_82, B_80, A_83, B_81), D_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_367])).
% 2.67/1.41  tff(c_407, plain, (![C_18, A_82, B_17, A_16, B_80]: (k2_xboole_0(k2_enumset1(A_82, B_80, A_16, B_17), k1_tarski(C_18))=k2_xboole_0(k2_tarski(A_82, B_80), k1_enumset1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_377])).
% 2.67/1.41  tff(c_413, plain, (![A_87, A_85, B_84, C_88, B_86]: (k2_xboole_0(k2_tarski(A_87, B_86), k1_enumset1(A_85, B_84, C_88))=k3_enumset1(A_87, B_86, A_85, B_84, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_407])).
% 2.67/1.41  tff(c_375, plain, (![A_76, D_77, B_75, A_14, B_15]: (k2_xboole_0(k2_tarski(A_76, B_75), k2_xboole_0(k2_tarski(A_14, B_15), D_77))=k2_xboole_0(k2_enumset1(A_76, B_75, A_14, B_15), D_77))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_367])).
% 2.67/1.41  tff(c_419, plain, (![A_87, A_85, A_76, B_75, B_84, C_88, B_86]: (k2_xboole_0(k2_enumset1(A_76, B_75, A_87, B_86), k1_enumset1(A_85, B_84, C_88))=k2_xboole_0(k2_tarski(A_76, B_75), k3_enumset1(A_87, B_86, A_85, B_84, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_413, c_375])).
% 2.67/1.41  tff(c_436, plain, (![A_87, A_85, A_76, B_75, B_84, C_88, B_86]: (k2_xboole_0(k2_tarski(A_76, B_75), k3_enumset1(A_87, B_86, A_85, B_84, C_88))=k5_enumset1(A_76, B_75, A_87, B_86, A_85, B_84, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_419])).
% 2.67/1.41  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.41  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_436, c_16])).
% 2.67/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  Inference rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Ref     : 0
% 2.67/1.41  #Sup     : 110
% 2.67/1.41  #Fact    : 0
% 2.67/1.41  #Define  : 0
% 2.67/1.41  #Split   : 0
% 2.67/1.41  #Chain   : 0
% 2.67/1.41  #Close   : 0
% 2.67/1.41  
% 2.67/1.41  Ordering : KBO
% 2.67/1.41  
% 2.67/1.41  Simplification rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Subsume      : 0
% 2.67/1.41  #Demod        : 91
% 2.67/1.41  #Tautology    : 50
% 2.67/1.41  #SimpNegUnit  : 0
% 2.67/1.41  #BackRed      : 1
% 2.67/1.41  
% 2.67/1.41  #Partial instantiations: 0
% 2.67/1.41  #Strategies tried      : 1
% 2.67/1.41  
% 2.67/1.41  Timing (in seconds)
% 2.67/1.41  ----------------------
% 2.67/1.41  Preprocessing        : 0.28
% 2.67/1.41  Parsing              : 0.16
% 2.67/1.41  CNF conversion       : 0.02
% 2.67/1.41  Main loop            : 0.31
% 2.67/1.41  Inferencing          : 0.13
% 2.67/1.41  Reduction            : 0.12
% 2.67/1.41  Demodulation         : 0.10
% 2.67/1.41  BG Simplification    : 0.02
% 2.67/1.41  Subsumption          : 0.03
% 2.67/1.41  Abstraction          : 0.03
% 2.67/1.41  MUC search           : 0.00
% 2.67/1.41  Cooper               : 0.00
% 2.67/1.41  Total                : 0.62
% 2.67/1.41  Index Insertion      : 0.00
% 2.67/1.41  Index Deletion       : 0.00
% 2.67/1.41  Index Matching       : 0.00
% 2.67/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

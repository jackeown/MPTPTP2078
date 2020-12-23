%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(c_6,plain,(
    ! [D_10,A_7,F_12,B_8,E_11,C_9] : k2_xboole_0(k1_enumset1(A_7,B_8,C_9),k1_enumset1(D_10,E_11,F_12)) = k4_enumset1(A_7,B_8,C_9,D_10,E_11,F_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k1_tarski(E_26)) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k1_tarski(D_21)) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_38,B_39,C_40,D_41] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_38,B_39),C_40),D_41) = k2_xboole_0(A_38,k2_xboole_0(k2_xboole_0(B_39,C_40),D_41)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_226,plain,(
    ! [C_67,A_70,B_68,C_69,D_71] : k2_xboole_0(k2_tarski(A_70,B_68),k2_xboole_0(k2_xboole_0(k1_tarski(C_67),C_69),D_71)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_70,B_68,C_67),C_69),D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_253,plain,(
    ! [A_13,A_70,B_68,B_14,D_71] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_70,B_68,A_13),k1_tarski(B_14)),D_71) = k2_xboole_0(k2_tarski(A_70,B_68),k2_xboole_0(k2_tarski(A_13,B_14),D_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_226])).

tff(c_260,plain,(
    ! [A_74,A_76,B_73,B_72,D_75] : k2_xboole_0(k2_tarski(A_74,B_72),k2_xboole_0(k2_tarski(A_76,B_73),D_75)) = k2_xboole_0(k2_enumset1(A_74,B_72,A_76,B_73),D_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_253])).

tff(c_287,plain,(
    ! [B_16,A_15,A_74,B_72,C_17] : k2_xboole_0(k2_enumset1(A_74,B_72,A_15,B_16),k1_tarski(C_17)) = k2_xboole_0(k2_tarski(A_74,B_72),k1_enumset1(A_15,B_16,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_260])).

tff(c_292,plain,(
    ! [B_78,A_81,B_79,A_80,C_77] : k2_xboole_0(k2_tarski(A_80,B_79),k1_enumset1(A_81,B_78,C_77)) = k3_enumset1(A_80,B_79,A_81,B_78,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_115,plain,(
    ! [A_53,B_54,C_55,D_56] : k2_xboole_0(k1_tarski(A_53),k2_xboole_0(k2_xboole_0(k1_tarski(B_54),C_55),D_56)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_53,B_54),C_55),D_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_133,plain,(
    ! [A_53,A_13,B_14,D_56] : k2_xboole_0(k2_xboole_0(k2_tarski(A_53,A_13),k1_tarski(B_14)),D_56) = k2_xboole_0(k1_tarski(A_53),k2_xboole_0(k2_tarski(A_13,B_14),D_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_139,plain,(
    ! [A_53,A_13,B_14,D_56] : k2_xboole_0(k1_tarski(A_53),k2_xboole_0(k2_tarski(A_13,B_14),D_56)) = k2_xboole_0(k1_enumset1(A_53,A_13,B_14),D_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_133])).

tff(c_301,plain,(
    ! [B_78,A_53,A_81,B_79,A_80,C_77] : k2_xboole_0(k1_enumset1(A_53,A_80,B_79),k1_enumset1(A_81,B_78,C_77)) = k2_xboole_0(k1_tarski(A_53),k3_enumset1(A_80,B_79,A_81,B_78,C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_139])).

tff(c_312,plain,(
    ! [B_78,A_53,A_81,B_79,A_80,C_77] : k2_xboole_0(k1_tarski(A_53),k3_enumset1(A_80,B_79,A_81,B_78,C_77)) = k4_enumset1(A_53,A_80,B_79,A_81,B_78,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_301])).

tff(c_16,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k3_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.33  
% 2.15/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.34  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.34  
% 2.15/1.34  %Foreground sorts:
% 2.15/1.34  
% 2.15/1.34  
% 2.15/1.34  %Background operators:
% 2.15/1.34  
% 2.15/1.34  
% 2.15/1.34  %Foreground operators:
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.34  
% 2.42/1.35  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.42/1.35  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.42/1.35  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.42/1.35  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.42/1.35  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.42/1.35  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 2.42/1.35  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.42/1.35  tff(c_6, plain, (![D_10, A_7, F_12, B_8, E_11, C_9]: (k2_xboole_0(k1_enumset1(A_7, B_8, C_9), k1_enumset1(D_10, E_11, F_12))=k4_enumset1(A_7, B_8, C_9, D_10, E_11, F_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.35  tff(c_14, plain, (![E_26, A_22, B_23, D_25, C_24]: (k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k1_tarski(E_26))=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.35  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.35  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k1_tarski(D_21))=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.35  tff(c_8, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.35  tff(c_59, plain, (![A_38, B_39, C_40, D_41]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_38, B_39), C_40), D_41)=k2_xboole_0(A_38, k2_xboole_0(k2_xboole_0(B_39, C_40), D_41)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.35  tff(c_226, plain, (![C_67, A_70, B_68, C_69, D_71]: (k2_xboole_0(k2_tarski(A_70, B_68), k2_xboole_0(k2_xboole_0(k1_tarski(C_67), C_69), D_71))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_70, B_68, C_67), C_69), D_71))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 2.42/1.35  tff(c_253, plain, (![A_13, A_70, B_68, B_14, D_71]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_70, B_68, A_13), k1_tarski(B_14)), D_71)=k2_xboole_0(k2_tarski(A_70, B_68), k2_xboole_0(k2_tarski(A_13, B_14), D_71)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_226])).
% 2.42/1.35  tff(c_260, plain, (![A_74, A_76, B_73, B_72, D_75]: (k2_xboole_0(k2_tarski(A_74, B_72), k2_xboole_0(k2_tarski(A_76, B_73), D_75))=k2_xboole_0(k2_enumset1(A_74, B_72, A_76, B_73), D_75))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_253])).
% 2.42/1.35  tff(c_287, plain, (![B_16, A_15, A_74, B_72, C_17]: (k2_xboole_0(k2_enumset1(A_74, B_72, A_15, B_16), k1_tarski(C_17))=k2_xboole_0(k2_tarski(A_74, B_72), k1_enumset1(A_15, B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_260])).
% 2.42/1.35  tff(c_292, plain, (![B_78, A_81, B_79, A_80, C_77]: (k2_xboole_0(k2_tarski(A_80, B_79), k1_enumset1(A_81, B_78, C_77))=k3_enumset1(A_80, B_79, A_81, B_78, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_287])).
% 2.42/1.35  tff(c_115, plain, (![A_53, B_54, C_55, D_56]: (k2_xboole_0(k1_tarski(A_53), k2_xboole_0(k2_xboole_0(k1_tarski(B_54), C_55), D_56))=k2_xboole_0(k2_xboole_0(k2_tarski(A_53, B_54), C_55), D_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_59])).
% 2.42/1.35  tff(c_133, plain, (![A_53, A_13, B_14, D_56]: (k2_xboole_0(k2_xboole_0(k2_tarski(A_53, A_13), k1_tarski(B_14)), D_56)=k2_xboole_0(k1_tarski(A_53), k2_xboole_0(k2_tarski(A_13, B_14), D_56)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_115])).
% 2.42/1.35  tff(c_139, plain, (![A_53, A_13, B_14, D_56]: (k2_xboole_0(k1_tarski(A_53), k2_xboole_0(k2_tarski(A_13, B_14), D_56))=k2_xboole_0(k1_enumset1(A_53, A_13, B_14), D_56))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_133])).
% 2.42/1.35  tff(c_301, plain, (![B_78, A_53, A_81, B_79, A_80, C_77]: (k2_xboole_0(k1_enumset1(A_53, A_80, B_79), k1_enumset1(A_81, B_78, C_77))=k2_xboole_0(k1_tarski(A_53), k3_enumset1(A_80, B_79, A_81, B_78, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_139])).
% 2.42/1.35  tff(c_312, plain, (![B_78, A_53, A_81, B_79, A_80, C_77]: (k2_xboole_0(k1_tarski(A_53), k3_enumset1(A_80, B_79, A_81, B_78, C_77))=k4_enumset1(A_53, A_80, B_79, A_81, B_78, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_301])).
% 2.42/1.35  tff(c_16, plain, (k2_xboole_0(k1_tarski('#skF_1'), k3_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.42/1.35  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_16])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 79
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 0
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 0
% 2.42/1.35  #Demod        : 32
% 2.42/1.35  #Tautology    : 33
% 2.42/1.35  #SimpNegUnit  : 0
% 2.42/1.35  #BackRed      : 1
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.29
% 2.42/1.35  Parsing              : 0.16
% 2.42/1.35  CNF conversion       : 0.02
% 2.42/1.35  Main loop            : 0.25
% 2.42/1.35  Inferencing          : 0.11
% 2.42/1.35  Reduction            : 0.08
% 2.42/1.35  Demodulation         : 0.07
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.03
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.56
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

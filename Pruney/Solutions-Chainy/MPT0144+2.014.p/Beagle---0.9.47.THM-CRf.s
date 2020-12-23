%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:53 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 (  59 expanded)
%              Number of equality atoms :   34 (  58 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_18,plain,(
    ! [G_35,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_29),k4_enumset1(B_30,C_31,D_32,E_33,F_34,G_35)) = k5_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k2_xboole_0(k1_tarski(A_23),k3_enumset1(B_24,C_25,D_26,E_27,F_28)) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [B_70,C_67,A_66,E_68,D_69] : k2_xboole_0(k1_tarski(A_66),k2_enumset1(B_70,C_67,D_69,E_68)) = k3_enumset1(A_66,B_70,C_67,D_69,E_68) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k2_xboole_0(A_40,B_41),C_42) = k2_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_9,B_10,C_42] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_42)) = k2_xboole_0(k2_tarski(A_9,B_10),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_39])).

tff(c_199,plain,(
    ! [B_70,C_67,A_66,E_68,D_69,A_9] : k2_xboole_0(k2_tarski(A_9,A_66),k2_enumset1(B_70,C_67,D_69,E_68)) = k2_xboole_0(k1_tarski(A_9),k3_enumset1(A_66,B_70,C_67,D_69,E_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_54])).

tff(c_784,plain,(
    ! [D_173,C_170,A_171,A_169,B_168,E_172] : k2_xboole_0(k2_tarski(A_171,A_169),k2_enumset1(B_168,C_170,D_173,E_172)) = k4_enumset1(A_171,A_169,B_168,C_170,D_173,E_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_199])).

tff(c_79,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k1_tarski(A_46),k2_tarski(B_47,C_48)) = k1_enumset1(A_46,B_47,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_xboole_0(k2_xboole_0(A_4,B_5),C_6) = k2_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_46,B_47,C_48,C_6] : k2_xboole_0(k1_tarski(A_46),k2_xboole_0(k2_tarski(B_47,C_48),C_6)) = k2_xboole_0(k1_enumset1(A_46,B_47,C_48),C_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_796,plain,(
    ! [A_46,D_173,C_170,A_171,A_169,B_168,E_172] : k2_xboole_0(k1_enumset1(A_46,A_171,A_169),k2_enumset1(B_168,C_170,D_173,E_172)) = k2_xboole_0(k1_tarski(A_46),k4_enumset1(A_171,A_169,B_168,C_170,D_173,E_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_85])).

tff(c_807,plain,(
    ! [A_46,D_173,C_170,A_171,A_169,B_168,E_172] : k2_xboole_0(k1_enumset1(A_46,A_171,A_169),k2_enumset1(B_168,C_170,D_173,E_172)) = k5_enumset1(A_46,A_171,A_169,B_168,C_170,D_173,E_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_796])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k1_tarski(A_56),k2_xboole_0(k1_tarski(B_57),C_58)) = k2_xboole_0(k2_tarski(A_56,B_57),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_39])).

tff(c_153,plain,(
    ! [A_56,A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_56,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_tarski(A_56),k1_enumset1(A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_129])).

tff(c_161,plain,(
    ! [A_56,A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_56,A_11),k2_tarski(B_12,C_13)) = k2_enumset1(A_56,A_11,B_12,C_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_14,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k2_enumset1(B_19,C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_211,plain,(
    ! [A_71,B_72,C_73,C_74] : k2_xboole_0(k1_tarski(A_71),k2_xboole_0(k2_tarski(B_72,C_73),C_74)) = k2_xboole_0(k1_enumset1(A_71,B_72,C_73),C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_229,plain,(
    ! [A_56,A_71,B_12,A_11,C_13] : k2_xboole_0(k1_enumset1(A_71,A_56,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_tarski(A_71),k2_enumset1(A_56,A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_211])).

tff(c_314,plain,(
    ! [C_89,B_92,A_91,A_93,A_90] : k2_xboole_0(k1_enumset1(A_91,A_93,A_90),k2_tarski(B_92,C_89)) = k3_enumset1(A_91,A_93,A_90,B_92,C_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_229])).

tff(c_951,plain,(
    ! [A_209,A_210,B_206,C_207,A_211,C_208] : k2_xboole_0(k1_enumset1(A_211,A_209,A_210),k2_xboole_0(k2_tarski(B_206,C_207),C_208)) = k2_xboole_0(k3_enumset1(A_211,A_209,A_210,B_206,C_207),C_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_4])).

tff(c_993,plain,(
    ! [A_209,A_56,A_210,A_211,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_211,A_209,A_210,A_56,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_enumset1(A_211,A_209,A_210),k2_enumset1(A_56,A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_951])).

tff(c_1004,plain,(
    ! [A_209,A_56,A_210,A_211,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_211,A_209,A_210,A_56,A_11),k2_tarski(B_12,C_13)) = k5_enumset1(A_211,A_209,A_210,A_56,A_11,B_12,C_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_993])).

tff(c_20,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.54  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.54  
% 3.35/1.54  %Foreground sorts:
% 3.35/1.54  
% 3.35/1.54  
% 3.35/1.54  %Background operators:
% 3.35/1.54  
% 3.35/1.54  
% 3.35/1.54  %Foreground operators:
% 3.35/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.35/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.54  
% 3.35/1.55  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 3.35/1.55  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.35/1.55  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.35/1.55  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.35/1.55  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.35/1.55  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.35/1.55  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.35/1.55  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 3.35/1.55  tff(c_18, plain, (![G_35, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_29), k4_enumset1(B_30, C_31, D_32, E_33, F_34, G_35))=k5_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.55  tff(c_16, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k2_xboole_0(k1_tarski(A_23), k3_enumset1(B_24, C_25, D_26, E_27, F_28))=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.55  tff(c_193, plain, (![B_70, C_67, A_66, E_68, D_69]: (k2_xboole_0(k1_tarski(A_66), k2_enumset1(B_70, C_67, D_69, E_68))=k3_enumset1(A_66, B_70, C_67, D_69, E_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.55  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.55  tff(c_39, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k2_xboole_0(A_40, B_41), C_42)=k2_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.55  tff(c_54, plain, (![A_9, B_10, C_42]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_42))=k2_xboole_0(k2_tarski(A_9, B_10), C_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_39])).
% 3.35/1.55  tff(c_199, plain, (![B_70, C_67, A_66, E_68, D_69, A_9]: (k2_xboole_0(k2_tarski(A_9, A_66), k2_enumset1(B_70, C_67, D_69, E_68))=k2_xboole_0(k1_tarski(A_9), k3_enumset1(A_66, B_70, C_67, D_69, E_68)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_54])).
% 3.35/1.55  tff(c_784, plain, (![D_173, C_170, A_171, A_169, B_168, E_172]: (k2_xboole_0(k2_tarski(A_171, A_169), k2_enumset1(B_168, C_170, D_173, E_172))=k4_enumset1(A_171, A_169, B_168, C_170, D_173, E_172))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_199])).
% 3.35/1.55  tff(c_79, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(B_47, C_48))=k1_enumset1(A_46, B_47, C_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.55  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_xboole_0(k2_xboole_0(A_4, B_5), C_6)=k2_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.55  tff(c_85, plain, (![A_46, B_47, C_48, C_6]: (k2_xboole_0(k1_tarski(A_46), k2_xboole_0(k2_tarski(B_47, C_48), C_6))=k2_xboole_0(k1_enumset1(A_46, B_47, C_48), C_6))), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 3.35/1.55  tff(c_796, plain, (![A_46, D_173, C_170, A_171, A_169, B_168, E_172]: (k2_xboole_0(k1_enumset1(A_46, A_171, A_169), k2_enumset1(B_168, C_170, D_173, E_172))=k2_xboole_0(k1_tarski(A_46), k4_enumset1(A_171, A_169, B_168, C_170, D_173, E_172)))), inference(superposition, [status(thm), theory('equality')], [c_784, c_85])).
% 3.35/1.55  tff(c_807, plain, (![A_46, D_173, C_170, A_171, A_169, B_168, E_172]: (k2_xboole_0(k1_enumset1(A_46, A_171, A_169), k2_enumset1(B_168, C_170, D_173, E_172))=k5_enumset1(A_46, A_171, A_169, B_168, C_170, D_173, E_172))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_796])).
% 3.35/1.55  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.55  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(B_12, C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.55  tff(c_129, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k1_tarski(A_56), k2_xboole_0(k1_tarski(B_57), C_58))=k2_xboole_0(k2_tarski(A_56, B_57), C_58))), inference(superposition, [status(thm), theory('equality')], [c_8, c_39])).
% 3.35/1.55  tff(c_153, plain, (![A_56, A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_56, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_tarski(A_56), k1_enumset1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_129])).
% 3.35/1.55  tff(c_161, plain, (![A_56, A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_56, A_11), k2_tarski(B_12, C_13))=k2_enumset1(A_56, A_11, B_12, C_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_153])).
% 3.35/1.55  tff(c_14, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k2_enumset1(B_19, C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.55  tff(c_211, plain, (![A_71, B_72, C_73, C_74]: (k2_xboole_0(k1_tarski(A_71), k2_xboole_0(k2_tarski(B_72, C_73), C_74))=k2_xboole_0(k1_enumset1(A_71, B_72, C_73), C_74))), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 3.35/1.55  tff(c_229, plain, (![A_56, A_71, B_12, A_11, C_13]: (k2_xboole_0(k1_enumset1(A_71, A_56, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_tarski(A_71), k2_enumset1(A_56, A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_211])).
% 3.35/1.55  tff(c_314, plain, (![C_89, B_92, A_91, A_93, A_90]: (k2_xboole_0(k1_enumset1(A_91, A_93, A_90), k2_tarski(B_92, C_89))=k3_enumset1(A_91, A_93, A_90, B_92, C_89))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_229])).
% 3.35/1.55  tff(c_951, plain, (![A_209, A_210, B_206, C_207, A_211, C_208]: (k2_xboole_0(k1_enumset1(A_211, A_209, A_210), k2_xboole_0(k2_tarski(B_206, C_207), C_208))=k2_xboole_0(k3_enumset1(A_211, A_209, A_210, B_206, C_207), C_208))), inference(superposition, [status(thm), theory('equality')], [c_314, c_4])).
% 3.35/1.55  tff(c_993, plain, (![A_209, A_56, A_210, A_211, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_211, A_209, A_210, A_56, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_enumset1(A_211, A_209, A_210), k2_enumset1(A_56, A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_951])).
% 3.35/1.55  tff(c_1004, plain, (![A_209, A_56, A_210, A_211, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_211, A_209, A_210, A_56, A_11), k2_tarski(B_12, C_13))=k5_enumset1(A_211, A_209, A_210, A_56, A_11, B_12, C_13))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_993])).
% 3.35/1.55  tff(c_20, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.55  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1004, c_20])).
% 3.35/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.55  
% 3.35/1.55  Inference rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Ref     : 0
% 3.35/1.55  #Sup     : 279
% 3.35/1.55  #Fact    : 0
% 3.35/1.55  #Define  : 0
% 3.35/1.55  #Split   : 0
% 3.35/1.55  #Chain   : 0
% 3.35/1.55  #Close   : 0
% 3.35/1.55  
% 3.35/1.55  Ordering : KBO
% 3.35/1.55  
% 3.35/1.55  Simplification rules
% 3.35/1.55  ----------------------
% 3.35/1.55  #Subsume      : 0
% 3.35/1.55  #Demod        : 156
% 3.35/1.55  #Tautology    : 121
% 3.35/1.55  #SimpNegUnit  : 0
% 3.35/1.55  #BackRed      : 1
% 3.35/1.55  
% 3.35/1.55  #Partial instantiations: 0
% 3.35/1.55  #Strategies tried      : 1
% 3.35/1.55  
% 3.35/1.55  Timing (in seconds)
% 3.35/1.55  ----------------------
% 3.35/1.55  Preprocessing        : 0.28
% 3.35/1.55  Parsing              : 0.15
% 3.35/1.55  CNF conversion       : 0.02
% 3.35/1.55  Main loop            : 0.50
% 3.35/1.55  Inferencing          : 0.22
% 3.35/1.55  Reduction            : 0.17
% 3.35/1.55  Demodulation         : 0.14
% 3.35/1.55  BG Simplification    : 0.04
% 3.35/1.55  Subsumption          : 0.06
% 3.35/1.55  Abstraction          : 0.05
% 3.35/1.55  MUC search           : 0.00
% 3.35/1.55  Cooper               : 0.00
% 3.35/1.55  Total                : 0.81
% 3.35/1.56  Index Insertion      : 0.00
% 3.35/1.56  Index Deletion       : 0.00
% 3.35/1.56  Index Matching       : 0.00
% 3.35/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

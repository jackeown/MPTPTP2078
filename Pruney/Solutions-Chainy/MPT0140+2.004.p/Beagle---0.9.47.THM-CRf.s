%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:47 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  58 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(c_14,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k2_xboole_0(k1_tarski(A_26),k3_enumset1(B_27,C_28,D_29,E_30,F_31)) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k2_enumset1(A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [B_51,A_53,E_52,D_54,C_55] : k2_xboole_0(k1_tarski(A_53),k2_enumset1(B_51,C_55,D_54,E_52)) = k3_enumset1(A_53,B_51,C_55,D_54,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    ! [D_99,C_96,E_98,C_101,B_100,A_97] : k2_xboole_0(k1_tarski(A_97),k2_xboole_0(k2_enumset1(B_100,C_96,D_99,E_98),C_101)) = k2_xboole_0(k3_enumset1(A_97,B_100,C_96,D_99,E_98),C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_310,plain,(
    ! [A_21,B_22,D_24,C_23,E_25,A_97] : k2_xboole_0(k3_enumset1(A_97,A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k2_xboole_0(k1_tarski(A_97),k3_enumset1(A_21,B_22,C_23,D_24,E_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_283])).

tff(c_314,plain,(
    ! [A_21,B_22,D_24,C_23,E_25,A_97] : k2_xboole_0(k3_enumset1(A_97,A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k4_enumset1(A_97,A_21,B_22,C_23,D_24,E_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_310])).

tff(c_205,plain,(
    ! [A_74,B_73,F_75,E_77,C_76,D_72] : k2_xboole_0(k1_tarski(A_74),k3_enumset1(B_73,C_76,D_72,E_77,F_75)) = k4_enumset1(A_74,B_73,C_76,D_72,E_77,F_75) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_371,plain,(
    ! [D_130,C_132,E_133,F_128,A_131,B_127,C_129] : k2_xboole_0(k1_tarski(A_131),k2_xboole_0(k3_enumset1(B_127,C_129,D_130,E_133,F_128),C_132)) = k2_xboole_0(k4_enumset1(A_131,B_127,C_129,D_130,E_133,F_128),C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_395,plain,(
    ! [A_21,B_22,D_24,C_23,E_25,A_131,A_97] : k2_xboole_0(k4_enumset1(A_131,A_97,A_21,B_22,C_23,D_24),k1_tarski(E_25)) = k2_xboole_0(k1_tarski(A_131),k4_enumset1(A_97,A_21,B_22,C_23,D_24,E_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_371])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k2_xboole_0(A_34,B_35),C_36) = k2_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k1_tarski(A_40),k2_xboole_0(k1_tarski(B_41),C_42)) = k2_xboole_0(k2_tarski(A_40,B_41),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_26])).

tff(c_79,plain,(
    ! [A_40,A_11,B_12] : k2_xboole_0(k2_tarski(A_40,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_40),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_83,plain,(
    ! [A_40,A_11,B_12] : k2_xboole_0(k2_tarski(A_40,A_11),k1_tarski(B_12)) = k1_enumset1(A_40,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_96,plain,(
    ! [A_46,B_49,E_50,C_48,D_47] : k2_xboole_0(k2_enumset1(A_46,B_49,C_48,D_47),k1_tarski(E_50)) = k3_enumset1(A_46,B_49,C_48,D_47,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_251,plain,(
    ! [A_95,D_91,C_94,E_92,B_90,C_93] : k2_xboole_0(k2_enumset1(A_95,B_90,C_93,D_91),k2_xboole_0(k1_tarski(E_92),C_94)) = k2_xboole_0(k3_enumset1(A_95,B_90,C_93,D_91,E_92),C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_278,plain,(
    ! [A_95,D_91,B_90,C_93,B_12,A_11] : k2_xboole_0(k3_enumset1(A_95,B_90,C_93,D_91,A_11),k1_tarski(B_12)) = k2_xboole_0(k2_enumset1(A_95,B_90,C_93,D_91),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_251])).

tff(c_328,plain,(
    ! [A_110,D_108,A_111,B_109,C_113,B_112] : k2_xboole_0(k2_enumset1(A_110,B_109,C_113,D_108),k2_tarski(A_111,B_112)) = k4_enumset1(A_110,B_109,C_113,D_108,A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_278])).

tff(c_619,plain,(
    ! [D_181,B_185,A_182,C_180,C_183,A_179,B_184] : k2_xboole_0(k2_enumset1(A_179,B_184,C_180,D_181),k2_xboole_0(k2_tarski(A_182,B_185),C_183)) = k2_xboole_0(k4_enumset1(A_179,B_184,C_180,D_181,A_182,B_185),C_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_2])).

tff(c_655,plain,(
    ! [D_181,C_180,A_40,A_179,B_184,B_12,A_11] : k2_xboole_0(k4_enumset1(A_179,B_184,C_180,D_181,A_40,A_11),k1_tarski(B_12)) = k2_xboole_0(k2_enumset1(A_179,B_184,C_180,D_181),k1_enumset1(A_40,A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_619])).

tff(c_663,plain,(
    ! [D_181,C_180,A_40,A_179,B_184,B_12,A_11] : k2_xboole_0(k1_tarski(A_179),k4_enumset1(B_184,C_180,D_181,A_40,A_11,B_12)) = k5_enumset1(A_179,B_184,C_180,D_181,A_40,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_4,c_655])).

tff(c_16,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.39  
% 2.75/1.39  %Foreground sorts:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Background operators:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Foreground operators:
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.39  
% 2.99/1.40  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.99/1.40  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.99/1.40  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.99/1.40  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.99/1.40  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.99/1.40  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.99/1.40  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.99/1.40  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.99/1.40  tff(c_14, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k2_xboole_0(k1_tarski(A_26), k3_enumset1(B_27, C_28, D_29, E_30, F_31))=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.40  tff(c_12, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k2_enumset1(A_21, B_22, C_23, D_24), k1_tarski(E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.40  tff(c_108, plain, (![B_51, A_53, E_52, D_54, C_55]: (k2_xboole_0(k1_tarski(A_53), k2_enumset1(B_51, C_55, D_54, E_52))=k3_enumset1(A_53, B_51, C_55, D_54, E_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.40  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.40  tff(c_283, plain, (![D_99, C_96, E_98, C_101, B_100, A_97]: (k2_xboole_0(k1_tarski(A_97), k2_xboole_0(k2_enumset1(B_100, C_96, D_99, E_98), C_101))=k2_xboole_0(k3_enumset1(A_97, B_100, C_96, D_99, E_98), C_101))), inference(superposition, [status(thm), theory('equality')], [c_108, c_2])).
% 2.99/1.40  tff(c_310, plain, (![A_21, B_22, D_24, C_23, E_25, A_97]: (k2_xboole_0(k3_enumset1(A_97, A_21, B_22, C_23, D_24), k1_tarski(E_25))=k2_xboole_0(k1_tarski(A_97), k3_enumset1(A_21, B_22, C_23, D_24, E_25)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_283])).
% 2.99/1.40  tff(c_314, plain, (![A_21, B_22, D_24, C_23, E_25, A_97]: (k2_xboole_0(k3_enumset1(A_97, A_21, B_22, C_23, D_24), k1_tarski(E_25))=k4_enumset1(A_97, A_21, B_22, C_23, D_24, E_25))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_310])).
% 2.99/1.40  tff(c_205, plain, (![A_74, B_73, F_75, E_77, C_76, D_72]: (k2_xboole_0(k1_tarski(A_74), k3_enumset1(B_73, C_76, D_72, E_77, F_75))=k4_enumset1(A_74, B_73, C_76, D_72, E_77, F_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.40  tff(c_371, plain, (![D_130, C_132, E_133, F_128, A_131, B_127, C_129]: (k2_xboole_0(k1_tarski(A_131), k2_xboole_0(k3_enumset1(B_127, C_129, D_130, E_133, F_128), C_132))=k2_xboole_0(k4_enumset1(A_131, B_127, C_129, D_130, E_133, F_128), C_132))), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 2.99/1.40  tff(c_395, plain, (![A_21, B_22, D_24, C_23, E_25, A_131, A_97]: (k2_xboole_0(k4_enumset1(A_131, A_97, A_21, B_22, C_23, D_24), k1_tarski(E_25))=k2_xboole_0(k1_tarski(A_131), k4_enumset1(A_97, A_21, B_22, C_23, D_24, E_25)))), inference(superposition, [status(thm), theory('equality')], [c_314, c_371])).
% 2.99/1.40  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.40  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.40  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.40  tff(c_26, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k2_xboole_0(A_34, B_35), C_36)=k2_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.40  tff(c_58, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k1_tarski(A_40), k2_xboole_0(k1_tarski(B_41), C_42))=k2_xboole_0(k2_tarski(A_40, B_41), C_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_26])).
% 2.99/1.40  tff(c_79, plain, (![A_40, A_11, B_12]: (k2_xboole_0(k2_tarski(A_40, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_40), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 2.99/1.40  tff(c_83, plain, (![A_40, A_11, B_12]: (k2_xboole_0(k2_tarski(A_40, A_11), k1_tarski(B_12))=k1_enumset1(A_40, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_79])).
% 2.99/1.40  tff(c_96, plain, (![A_46, B_49, E_50, C_48, D_47]: (k2_xboole_0(k2_enumset1(A_46, B_49, C_48, D_47), k1_tarski(E_50))=k3_enumset1(A_46, B_49, C_48, D_47, E_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.40  tff(c_251, plain, (![A_95, D_91, C_94, E_92, B_90, C_93]: (k2_xboole_0(k2_enumset1(A_95, B_90, C_93, D_91), k2_xboole_0(k1_tarski(E_92), C_94))=k2_xboole_0(k3_enumset1(A_95, B_90, C_93, D_91, E_92), C_94))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.99/1.40  tff(c_278, plain, (![A_95, D_91, B_90, C_93, B_12, A_11]: (k2_xboole_0(k3_enumset1(A_95, B_90, C_93, D_91, A_11), k1_tarski(B_12))=k2_xboole_0(k2_enumset1(A_95, B_90, C_93, D_91), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_251])).
% 2.99/1.40  tff(c_328, plain, (![A_110, D_108, A_111, B_109, C_113, B_112]: (k2_xboole_0(k2_enumset1(A_110, B_109, C_113, D_108), k2_tarski(A_111, B_112))=k4_enumset1(A_110, B_109, C_113, D_108, A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_278])).
% 2.99/1.40  tff(c_619, plain, (![D_181, B_185, A_182, C_180, C_183, A_179, B_184]: (k2_xboole_0(k2_enumset1(A_179, B_184, C_180, D_181), k2_xboole_0(k2_tarski(A_182, B_185), C_183))=k2_xboole_0(k4_enumset1(A_179, B_184, C_180, D_181, A_182, B_185), C_183))), inference(superposition, [status(thm), theory('equality')], [c_328, c_2])).
% 2.99/1.40  tff(c_655, plain, (![D_181, C_180, A_40, A_179, B_184, B_12, A_11]: (k2_xboole_0(k4_enumset1(A_179, B_184, C_180, D_181, A_40, A_11), k1_tarski(B_12))=k2_xboole_0(k2_enumset1(A_179, B_184, C_180, D_181), k1_enumset1(A_40, A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_619])).
% 2.99/1.40  tff(c_663, plain, (![D_181, C_180, A_40, A_179, B_184, B_12, A_11]: (k2_xboole_0(k1_tarski(A_179), k4_enumset1(B_184, C_180, D_181, A_40, A_11, B_12))=k5_enumset1(A_179, B_184, C_180, D_181, A_40, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_4, c_655])).
% 2.99/1.40  tff(c_16, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.99/1.40  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_663, c_16])).
% 2.99/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.40  
% 2.99/1.40  Inference rules
% 2.99/1.40  ----------------------
% 2.99/1.40  #Ref     : 0
% 2.99/1.40  #Sup     : 168
% 2.99/1.40  #Fact    : 0
% 2.99/1.40  #Define  : 0
% 2.99/1.40  #Split   : 0
% 2.99/1.40  #Chain   : 0
% 2.99/1.40  #Close   : 0
% 2.99/1.40  
% 2.99/1.40  Ordering : KBO
% 2.99/1.40  
% 2.99/1.40  Simplification rules
% 2.99/1.40  ----------------------
% 2.99/1.40  #Subsume      : 0
% 2.99/1.40  #Demod        : 108
% 2.99/1.40  #Tautology    : 88
% 2.99/1.40  #SimpNegUnit  : 0
% 2.99/1.40  #BackRed      : 3
% 2.99/1.40  
% 2.99/1.40  #Partial instantiations: 0
% 2.99/1.40  #Strategies tried      : 1
% 2.99/1.40  
% 2.99/1.40  Timing (in seconds)
% 2.99/1.40  ----------------------
% 2.99/1.40  Preprocessing        : 0.28
% 2.99/1.40  Parsing              : 0.15
% 2.99/1.40  CNF conversion       : 0.02
% 2.99/1.40  Main loop            : 0.39
% 2.99/1.40  Inferencing          : 0.17
% 2.99/1.40  Reduction            : 0.14
% 2.99/1.40  Demodulation         : 0.11
% 2.99/1.40  BG Simplification    : 0.03
% 2.99/1.40  Subsumption          : 0.04
% 2.99/1.40  Abstraction          : 0.03
% 2.99/1.40  MUC search           : 0.00
% 2.99/1.40  Cooper               : 0.00
% 2.99/1.40  Total                : 0.69
% 2.99/1.40  Index Insertion      : 0.00
% 2.99/1.40  Index Deletion       : 0.00
% 2.99/1.40  Index Matching       : 0.00
% 2.99/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

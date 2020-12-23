%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   54 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   33 (  40 expanded)
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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k1_tarski(A_31),k5_enumset1(B_32,C_33,D_34,E_35,F_36,G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28,G_30] : k2_xboole_0(k1_tarski(A_24),k4_enumset1(B_25,C_26,D_27,E_28,F_29,G_30)) = k5_enumset1(A_24,B_25,C_26,D_27,E_28,F_29,G_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k1_tarski(B_52),C_53)) = k2_xboole_0(k2_tarski(A_51,B_52),C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_90,plain,(
    ! [C_11,B_10,A_51,D_12,A_9] : k2_xboole_0(k2_tarski(A_51,A_9),k1_enumset1(B_10,C_11,D_12)) = k2_xboole_0(k1_tarski(A_51),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_300,plain,(
    ! [D_109,B_107,C_108,A_110,A_106] : k2_xboole_0(k2_tarski(A_106,A_110),k1_enumset1(B_107,C_108,D_109)) = k3_enumset1(A_106,A_110,B_107,C_108,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_6,B_7,C_8,C_46] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k2_tarski(B_7,C_8),C_46)) = k2_xboole_0(k1_enumset1(A_6,B_7,C_8),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_306,plain,(
    ! [D_109,B_107,C_108,A_110,A_106,A_6] : k2_xboole_0(k1_enumset1(A_6,A_106,A_110),k1_enumset1(B_107,C_108,D_109)) = k2_xboole_0(k1_tarski(A_6),k3_enumset1(A_106,A_110,B_107,C_108,D_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_52])).

tff(c_371,plain,(
    ! [A_124,B_126,C_125,A_127,A_129,D_128] : k2_xboole_0(k1_enumset1(A_127,A_129,A_124),k1_enumset1(B_126,C_125,D_128)) = k4_enumset1(A_127,A_129,A_124,B_126,C_125,D_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_306])).

tff(c_60,plain,(
    ! [A_47,B_48,C_49,D_50] : k2_xboole_0(k1_tarski(A_47),k1_enumset1(B_48,C_49,D_50)) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_47,C_3,D_50,C_49,B_48] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k1_enumset1(B_48,C_49,D_50),C_3)) = k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_377,plain,(
    ! [A_124,B_126,A_47,C_125,A_127,A_129,D_128] : k2_xboole_0(k2_enumset1(A_47,A_127,A_129,A_124),k1_enumset1(B_126,C_125,D_128)) = k2_xboole_0(k1_tarski(A_47),k4_enumset1(A_127,A_129,A_124,B_126,C_125,D_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_66])).

tff(c_635,plain,(
    ! [A_191,A_185,D_188,A_187,B_190,A_189,C_186] : k2_xboole_0(k2_enumset1(A_185,A_191,A_189,A_187),k1_enumset1(B_190,C_186,D_188)) = k5_enumset1(A_185,A_191,A_189,A_187,B_190,C_186,D_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_377])).

tff(c_102,plain,(
    ! [A_57,C_58,D_54,E_56,B_55] : k2_xboole_0(k1_tarski(A_57),k2_enumset1(B_55,C_58,D_54,E_56)) = k3_enumset1(A_57,B_55,C_58,D_54,E_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_57,C_3,C_58,D_54,E_56,B_55] : k2_xboole_0(k1_tarski(A_57),k2_xboole_0(k2_enumset1(B_55,C_58,D_54,E_56),C_3)) = k2_xboole_0(k3_enumset1(A_57,B_55,C_58,D_54,E_56),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_641,plain,(
    ! [A_57,A_191,A_185,D_188,A_187,B_190,A_189,C_186] : k2_xboole_0(k3_enumset1(A_57,A_185,A_191,A_189,A_187),k1_enumset1(B_190,C_186,D_188)) = k2_xboole_0(k1_tarski(A_57),k5_enumset1(A_185,A_191,A_189,A_187,B_190,C_186,D_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_111])).

tff(c_649,plain,(
    ! [A_57,A_191,A_185,D_188,A_187,B_190,A_189,C_186] : k2_xboole_0(k3_enumset1(A_57,A_185,A_191,A_189,A_187),k1_enumset1(B_190,C_186,D_188)) = k6_enumset1(A_57,A_185,A_191,A_189,A_187,B_190,C_186,D_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_641])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:51:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.52  
% 3.46/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.53  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.46/1.53  
% 3.46/1.53  %Foreground sorts:
% 3.46/1.53  
% 3.46/1.53  
% 3.46/1.53  %Background operators:
% 3.46/1.53  
% 3.46/1.53  
% 3.46/1.53  %Foreground operators:
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.46/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.46/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.53  
% 3.58/1.54  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.58/1.54  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 3.58/1.54  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.58/1.54  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.58/1.54  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.58/1.54  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.58/1.54  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.58/1.54  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.58/1.54  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 3.58/1.54  tff(c_16, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k1_tarski(A_31), k5_enumset1(B_32, C_33, D_34, E_35, F_36, G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.54  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28, G_30]: (k2_xboole_0(k1_tarski(A_24), k4_enumset1(B_25, C_26, D_27, E_28, F_29, G_30))=k5_enumset1(A_24, B_25, C_26, D_27, E_28, F_29, G_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.54  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.54  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.54  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.54  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.58/1.54  tff(c_37, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.58/1.54  tff(c_72, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k1_tarski(B_52), C_53))=k2_xboole_0(k2_tarski(A_51, B_52), C_53))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 3.58/1.54  tff(c_90, plain, (![C_11, B_10, A_51, D_12, A_9]: (k2_xboole_0(k2_tarski(A_51, A_9), k1_enumset1(B_10, C_11, D_12))=k2_xboole_0(k1_tarski(A_51), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 3.58/1.54  tff(c_300, plain, (![D_109, B_107, C_108, A_110, A_106]: (k2_xboole_0(k2_tarski(A_106, A_110), k1_enumset1(B_107, C_108, D_109))=k3_enumset1(A_106, A_110, B_107, C_108, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 3.58/1.54  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.54  tff(c_52, plain, (![A_6, B_7, C_8, C_46]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k2_tarski(B_7, C_8), C_46))=k2_xboole_0(k1_enumset1(A_6, B_7, C_8), C_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 3.58/1.54  tff(c_306, plain, (![D_109, B_107, C_108, A_110, A_106, A_6]: (k2_xboole_0(k1_enumset1(A_6, A_106, A_110), k1_enumset1(B_107, C_108, D_109))=k2_xboole_0(k1_tarski(A_6), k3_enumset1(A_106, A_110, B_107, C_108, D_109)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_52])).
% 3.58/1.54  tff(c_371, plain, (![A_124, B_126, C_125, A_127, A_129, D_128]: (k2_xboole_0(k1_enumset1(A_127, A_129, A_124), k1_enumset1(B_126, C_125, D_128))=k4_enumset1(A_127, A_129, A_124, B_126, C_125, D_128))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_306])).
% 3.58/1.54  tff(c_60, plain, (![A_47, B_48, C_49, D_50]: (k2_xboole_0(k1_tarski(A_47), k1_enumset1(B_48, C_49, D_50))=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.54  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.58/1.54  tff(c_66, plain, (![A_47, C_3, D_50, C_49, B_48]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k1_enumset1(B_48, C_49, D_50), C_3))=k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), C_3))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 3.58/1.54  tff(c_377, plain, (![A_124, B_126, A_47, C_125, A_127, A_129, D_128]: (k2_xboole_0(k2_enumset1(A_47, A_127, A_129, A_124), k1_enumset1(B_126, C_125, D_128))=k2_xboole_0(k1_tarski(A_47), k4_enumset1(A_127, A_129, A_124, B_126, C_125, D_128)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_66])).
% 3.58/1.54  tff(c_635, plain, (![A_191, A_185, D_188, A_187, B_190, A_189, C_186]: (k2_xboole_0(k2_enumset1(A_185, A_191, A_189, A_187), k1_enumset1(B_190, C_186, D_188))=k5_enumset1(A_185, A_191, A_189, A_187, B_190, C_186, D_188))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_377])).
% 3.58/1.54  tff(c_102, plain, (![A_57, C_58, D_54, E_56, B_55]: (k2_xboole_0(k1_tarski(A_57), k2_enumset1(B_55, C_58, D_54, E_56))=k3_enumset1(A_57, B_55, C_58, D_54, E_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.54  tff(c_111, plain, (![A_57, C_3, C_58, D_54, E_56, B_55]: (k2_xboole_0(k1_tarski(A_57), k2_xboole_0(k2_enumset1(B_55, C_58, D_54, E_56), C_3))=k2_xboole_0(k3_enumset1(A_57, B_55, C_58, D_54, E_56), C_3))), inference(superposition, [status(thm), theory('equality')], [c_102, c_2])).
% 3.58/1.54  tff(c_641, plain, (![A_57, A_191, A_185, D_188, A_187, B_190, A_189, C_186]: (k2_xboole_0(k3_enumset1(A_57, A_185, A_191, A_189, A_187), k1_enumset1(B_190, C_186, D_188))=k2_xboole_0(k1_tarski(A_57), k5_enumset1(A_185, A_191, A_189, A_187, B_190, C_186, D_188)))), inference(superposition, [status(thm), theory('equality')], [c_635, c_111])).
% 3.58/1.54  tff(c_649, plain, (![A_57, A_191, A_185, D_188, A_187, B_190, A_189, C_186]: (k2_xboole_0(k3_enumset1(A_57, A_185, A_191, A_189, A_187), k1_enumset1(B_190, C_186, D_188))=k6_enumset1(A_57, A_185, A_191, A_189, A_187, B_190, C_186, D_188))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_641])).
% 3.58/1.54  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.58/1.54  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_649, c_18])).
% 3.58/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.54  
% 3.58/1.54  Inference rules
% 3.58/1.54  ----------------------
% 3.58/1.54  #Ref     : 0
% 3.58/1.54  #Sup     : 258
% 3.58/1.54  #Fact    : 0
% 3.58/1.54  #Define  : 0
% 3.58/1.54  #Split   : 0
% 3.58/1.54  #Chain   : 0
% 3.58/1.54  #Close   : 0
% 3.58/1.54  
% 3.58/1.54  Ordering : KBO
% 3.58/1.54  
% 3.58/1.54  Simplification rules
% 3.58/1.54  ----------------------
% 3.58/1.54  #Subsume      : 0
% 3.58/1.54  #Demod        : 140
% 3.58/1.54  #Tautology    : 129
% 3.58/1.54  #SimpNegUnit  : 0
% 3.58/1.54  #BackRed      : 1
% 3.58/1.54  
% 3.58/1.54  #Partial instantiations: 0
% 3.58/1.54  #Strategies tried      : 1
% 3.58/1.54  
% 3.58/1.54  Timing (in seconds)
% 3.58/1.54  ----------------------
% 3.58/1.54  Preprocessing        : 0.28
% 3.58/1.54  Parsing              : 0.16
% 3.58/1.54  CNF conversion       : 0.02
% 3.58/1.54  Main loop            : 0.49
% 3.58/1.54  Inferencing          : 0.22
% 3.58/1.54  Reduction            : 0.16
% 3.58/1.54  Demodulation         : 0.13
% 3.58/1.54  BG Simplification    : 0.03
% 3.58/1.54  Subsumption          : 0.05
% 3.58/1.54  Abstraction          : 0.04
% 3.58/1.54  MUC search           : 0.00
% 3.58/1.54  Cooper               : 0.00
% 3.58/1.54  Total                : 0.80
% 3.58/1.54  Index Insertion      : 0.00
% 3.58/1.54  Index Deletion       : 0.00
% 3.58/1.54  Index Matching       : 0.00
% 3.58/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 130 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   51 ( 108 expanded)
%              Number of equality atoms :   50 ( 107 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_20,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,H_43,C_38,B_37] : k2_xboole_0(k1_tarski(A_36),k5_enumset1(B_37,C_38,D_39,E_40,F_41,G_42,H_43)) = k6_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42,H_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [G_35,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_29),k4_enumset1(B_30,C_31,D_32,E_33,F_34,G_35)) = k5_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] : k2_xboole_0(k1_tarski(A_23),k3_enumset1(B_24,C_25,D_26,E_27,F_28)) = k4_enumset1(A_23,B_24,C_25,D_26,E_27,F_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [A_74,B_78,D_77,C_75,E_76] : k2_xboole_0(k1_tarski(A_74),k2_enumset1(B_78,C_75,D_77,E_76)) = k3_enumset1(A_74,B_78,C_75,D_77,E_76) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k2_xboole_0(A_48,B_49),C_50) = k2_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_9,B_10,C_50] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_50)) = k2_xboole_0(k2_tarski(A_9,B_10),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_206,plain,(
    ! [A_74,B_78,D_77,C_75,E_76,A_9] : k2_xboole_0(k2_tarski(A_9,A_74),k2_enumset1(B_78,C_75,D_77,E_76)) = k2_xboole_0(k1_tarski(A_9),k3_enumset1(A_74,B_78,C_75,D_77,E_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_56])).

tff(c_1221,plain,(
    ! [C_190,B_189,A_193,A_192,E_194,D_191] : k2_xboole_0(k2_tarski(A_193,A_192),k2_enumset1(B_189,C_190,D_191,E_194)) = k4_enumset1(A_193,A_192,B_189,C_190,D_191,E_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_206])).

tff(c_61,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k1_tarski(A_51),k2_tarski(B_52,C_53)) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_51,B_52,C_53,C_3] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k2_tarski(B_52,C_53),C_3)) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_1242,plain,(
    ! [C_190,B_189,A_193,A_192,E_194,A_51,D_191] : k2_xboole_0(k1_enumset1(A_51,A_193,A_192),k2_enumset1(B_189,C_190,D_191,E_194)) = k2_xboole_0(k1_tarski(A_51),k4_enumset1(A_193,A_192,B_189,C_190,D_191,E_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_67])).

tff(c_1252,plain,(
    ! [C_190,B_189,A_193,A_192,E_194,A_51,D_191] : k2_xboole_0(k1_enumset1(A_51,A_193,A_192),k2_enumset1(B_189,C_190,D_191,E_194)) = k5_enumset1(A_51,A_193,A_192,B_189,C_190,D_191,E_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1242])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k1_tarski(A_11),k2_tarski(B_12,C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k1_tarski(A_64),k2_xboole_0(k1_tarski(B_65),C_66)) = k2_xboole_0(k2_tarski(A_64,B_65),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_167,plain,(
    ! [A_64,A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_64,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_tarski(A_64),k1_enumset1(A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_146])).

tff(c_174,plain,(
    ! [A_64,A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_64,A_11),k2_tarski(B_12,C_13)) = k2_enumset1(A_64,A_11,B_12,C_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_6,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k2_enumset1(B_19,C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_277,plain,(
    ! [A_82,B_83,C_84,C_85] : k2_xboole_0(k1_tarski(A_82),k2_xboole_0(k2_tarski(B_83,C_84),C_85)) = k2_xboole_0(k1_enumset1(A_82,B_83,C_84),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_292,plain,(
    ! [A_82,A_64,B_12,A_11,C_13] : k2_xboole_0(k1_enumset1(A_82,A_64,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_tarski(A_82),k2_enumset1(A_64,A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_277])).

tff(c_299,plain,(
    ! [A_82,A_64,B_12,A_11,C_13] : k2_xboole_0(k1_enumset1(A_82,A_64,A_11),k2_tarski(B_12,C_13)) = k3_enumset1(A_82,A_64,A_11,B_12,C_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_73,plain,(
    ! [A_54,B_55,C_56] : k5_xboole_0(k5_xboole_0(A_54,B_55),C_56) = k5_xboole_0(A_54,k5_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_215,plain,(
    ! [A_79,B_80,B_81] : k5_xboole_0(A_79,k5_xboole_0(B_80,k4_xboole_0(B_81,k5_xboole_0(A_79,B_80)))) = k2_xboole_0(k5_xboole_0(A_79,B_80),B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_263,plain,(
    ! [A_7,B_8,B_81] : k5_xboole_0(A_7,k5_xboole_0(k4_xboole_0(B_8,A_7),k4_xboole_0(B_81,k2_xboole_0(A_7,B_8)))) = k2_xboole_0(k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)),B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_215])).

tff(c_542,plain,(
    ! [A_138,B_139,B_140] : k5_xboole_0(A_138,k5_xboole_0(k4_xboole_0(B_139,A_138),k4_xboole_0(B_140,k2_xboole_0(A_138,B_139)))) = k2_xboole_0(A_138,k2_xboole_0(B_139,B_140)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_263])).

tff(c_92,plain,(
    ! [A_7,B_8,C_56] : k5_xboole_0(A_7,k5_xboole_0(k4_xboole_0(B_8,A_7),C_56)) = k5_xboole_0(k2_xboole_0(A_7,B_8),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_641,plain,(
    ! [A_141,B_142,B_143] : k5_xboole_0(k2_xboole_0(A_141,B_142),k4_xboole_0(B_143,k2_xboole_0(A_141,B_142))) = k2_xboole_0(A_141,k2_xboole_0(B_142,B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_92])).

tff(c_695,plain,(
    ! [A_82,B_143,A_64,B_12,A_11,C_13] : k5_xboole_0(k3_enumset1(A_82,A_64,A_11,B_12,C_13),k4_xboole_0(B_143,k2_xboole_0(k1_enumset1(A_82,A_64,A_11),k2_tarski(B_12,C_13)))) = k2_xboole_0(k1_enumset1(A_82,A_64,A_11),k2_xboole_0(k2_tarski(B_12,C_13),B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_641])).

tff(c_1581,plain,(
    ! [B_209,C_206,A_210,A_208,A_211,B_207] : k2_xboole_0(k1_enumset1(A_211,A_210,A_208),k2_xboole_0(k2_tarski(B_209,C_206),B_207)) = k2_xboole_0(k3_enumset1(A_211,A_210,A_208,B_209,C_206),B_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_299,c_695])).

tff(c_1626,plain,(
    ! [A_210,A_208,A_64,A_211,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_211,A_210,A_208,A_64,A_11),k2_tarski(B_12,C_13)) = k2_xboole_0(k1_enumset1(A_211,A_210,A_208),k2_enumset1(A_64,A_11,B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_1581])).

tff(c_1839,plain,(
    ! [C_233,A_235,A_234,A_232,B_236,A_237,A_238] : k2_xboole_0(k3_enumset1(A_237,A_234,A_232,A_238,A_235),k2_tarski(B_236,C_233)) = k5_enumset1(A_237,A_234,A_232,A_238,A_235,B_236,C_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_1626])).

tff(c_301,plain,(
    ! [E_88,C_86,B_89,F_87,A_91,D_90] : k2_xboole_0(k1_tarski(A_91),k3_enumset1(B_89,C_86,D_90,E_88,F_87)) = k4_enumset1(A_91,B_89,C_86,D_90,E_88,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_310,plain,(
    ! [E_88,C_3,C_86,B_89,F_87,A_91,D_90] : k2_xboole_0(k1_tarski(A_91),k2_xboole_0(k3_enumset1(B_89,C_86,D_90,E_88,F_87),C_3)) = k2_xboole_0(k4_enumset1(A_91,B_89,C_86,D_90,E_88,F_87),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_2])).

tff(c_1851,plain,(
    ! [C_233,A_235,A_234,A_232,B_236,A_91,A_237,A_238] : k2_xboole_0(k4_enumset1(A_91,A_237,A_234,A_232,A_238,A_235),k2_tarski(B_236,C_233)) = k2_xboole_0(k1_tarski(A_91),k5_enumset1(A_237,A_234,A_232,A_238,A_235,B_236,C_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_310])).

tff(c_1873,plain,(
    ! [C_233,A_235,A_234,A_232,B_236,A_91,A_237,A_238] : k2_xboole_0(k4_enumset1(A_91,A_237,A_234,A_232,A_238,A_235),k2_tarski(B_236,C_233)) = k6_enumset1(A_91,A_237,A_234,A_232,A_238,A_235,B_236,C_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1851])).

tff(c_22,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.26  % Computer   : n023.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 13:49:20 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.09  
% 5.89/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.09  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.89/2.09  
% 5.89/2.09  %Foreground sorts:
% 5.89/2.09  
% 5.89/2.09  
% 5.89/2.09  %Background operators:
% 5.89/2.09  
% 5.89/2.09  
% 5.89/2.09  %Foreground operators:
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.89/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.89/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.89/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.89/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.89/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.89/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.89/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.89/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.89/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.89/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.89/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.09  
% 6.00/2.11  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 6.00/2.11  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 6.00/2.11  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 6.00/2.11  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 6.00/2.11  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.00/2.11  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.00/2.11  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 6.00/2.11  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 6.00/2.11  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.00/2.11  tff(f_29, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.00/2.11  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 6.00/2.11  tff(c_20, plain, (![F_41, G_42, D_39, A_36, E_40, H_43, C_38, B_37]: (k2_xboole_0(k1_tarski(A_36), k5_enumset1(B_37, C_38, D_39, E_40, F_41, G_42, H_43))=k6_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42, H_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.00/2.11  tff(c_18, plain, (![G_35, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_29), k4_enumset1(B_30, C_31, D_32, E_33, F_34, G_35))=k5_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.11  tff(c_16, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (k2_xboole_0(k1_tarski(A_23), k3_enumset1(B_24, C_25, D_26, E_27, F_28))=k4_enumset1(A_23, B_24, C_25, D_26, E_27, F_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.00/2.11  tff(c_200, plain, (![A_74, B_78, D_77, C_75, E_76]: (k2_xboole_0(k1_tarski(A_74), k2_enumset1(B_78, C_75, D_77, E_76))=k3_enumset1(A_74, B_78, C_75, D_77, E_76))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.00/2.11  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.00/2.11  tff(c_41, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k2_xboole_0(A_48, B_49), C_50)=k2_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.00/2.11  tff(c_56, plain, (![A_9, B_10, C_50]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_50))=k2_xboole_0(k2_tarski(A_9, B_10), C_50))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 6.00/2.11  tff(c_206, plain, (![A_74, B_78, D_77, C_75, E_76, A_9]: (k2_xboole_0(k2_tarski(A_9, A_74), k2_enumset1(B_78, C_75, D_77, E_76))=k2_xboole_0(k1_tarski(A_9), k3_enumset1(A_74, B_78, C_75, D_77, E_76)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_56])).
% 6.00/2.11  tff(c_1221, plain, (![C_190, B_189, A_193, A_192, E_194, D_191]: (k2_xboole_0(k2_tarski(A_193, A_192), k2_enumset1(B_189, C_190, D_191, E_194))=k4_enumset1(A_193, A_192, B_189, C_190, D_191, E_194))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_206])).
% 6.00/2.11  tff(c_61, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k1_tarski(A_51), k2_tarski(B_52, C_53))=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.00/2.11  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.00/2.11  tff(c_67, plain, (![A_51, B_52, C_53, C_3]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k2_tarski(B_52, C_53), C_3))=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), C_3))), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 6.00/2.11  tff(c_1242, plain, (![C_190, B_189, A_193, A_192, E_194, A_51, D_191]: (k2_xboole_0(k1_enumset1(A_51, A_193, A_192), k2_enumset1(B_189, C_190, D_191, E_194))=k2_xboole_0(k1_tarski(A_51), k4_enumset1(A_193, A_192, B_189, C_190, D_191, E_194)))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_67])).
% 6.00/2.11  tff(c_1252, plain, (![C_190, B_189, A_193, A_192, E_194, A_51, D_191]: (k2_xboole_0(k1_enumset1(A_51, A_193, A_192), k2_enumset1(B_189, C_190, D_191, E_194))=k5_enumset1(A_51, A_193, A_192, B_189, C_190, D_191, E_194))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1242])).
% 6.00/2.11  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.00/2.11  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(B_12, C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.00/2.11  tff(c_146, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k1_tarski(A_64), k2_xboole_0(k1_tarski(B_65), C_66))=k2_xboole_0(k2_tarski(A_64, B_65), C_66))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 6.00/2.11  tff(c_167, plain, (![A_64, A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_64, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_tarski(A_64), k1_enumset1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_146])).
% 6.00/2.11  tff(c_174, plain, (![A_64, A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_64, A_11), k2_tarski(B_12, C_13))=k2_enumset1(A_64, A_11, B_12, C_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 6.00/2.11  tff(c_6, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.00/2.11  tff(c_14, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k2_enumset1(B_19, C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.00/2.11  tff(c_277, plain, (![A_82, B_83, C_84, C_85]: (k2_xboole_0(k1_tarski(A_82), k2_xboole_0(k2_tarski(B_83, C_84), C_85))=k2_xboole_0(k1_enumset1(A_82, B_83, C_84), C_85))), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 6.00/2.11  tff(c_292, plain, (![A_82, A_64, B_12, A_11, C_13]: (k2_xboole_0(k1_enumset1(A_82, A_64, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_tarski(A_82), k2_enumset1(A_64, A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_277])).
% 6.00/2.11  tff(c_299, plain, (![A_82, A_64, B_12, A_11, C_13]: (k2_xboole_0(k1_enumset1(A_82, A_64, A_11), k2_tarski(B_12, C_13))=k3_enumset1(A_82, A_64, A_11, B_12, C_13))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 6.00/2.11  tff(c_73, plain, (![A_54, B_55, C_56]: (k5_xboole_0(k5_xboole_0(A_54, B_55), C_56)=k5_xboole_0(A_54, k5_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.00/2.11  tff(c_215, plain, (![A_79, B_80, B_81]: (k5_xboole_0(A_79, k5_xboole_0(B_80, k4_xboole_0(B_81, k5_xboole_0(A_79, B_80))))=k2_xboole_0(k5_xboole_0(A_79, B_80), B_81))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 6.00/2.11  tff(c_263, plain, (![A_7, B_8, B_81]: (k5_xboole_0(A_7, k5_xboole_0(k4_xboole_0(B_8, A_7), k4_xboole_0(B_81, k2_xboole_0(A_7, B_8))))=k2_xboole_0(k5_xboole_0(A_7, k4_xboole_0(B_8, A_7)), B_81))), inference(superposition, [status(thm), theory('equality')], [c_6, c_215])).
% 6.00/2.11  tff(c_542, plain, (![A_138, B_139, B_140]: (k5_xboole_0(A_138, k5_xboole_0(k4_xboole_0(B_139, A_138), k4_xboole_0(B_140, k2_xboole_0(A_138, B_139))))=k2_xboole_0(A_138, k2_xboole_0(B_139, B_140)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_263])).
% 6.00/2.11  tff(c_92, plain, (![A_7, B_8, C_56]: (k5_xboole_0(A_7, k5_xboole_0(k4_xboole_0(B_8, A_7), C_56))=k5_xboole_0(k2_xboole_0(A_7, B_8), C_56))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 6.00/2.11  tff(c_641, plain, (![A_141, B_142, B_143]: (k5_xboole_0(k2_xboole_0(A_141, B_142), k4_xboole_0(B_143, k2_xboole_0(A_141, B_142)))=k2_xboole_0(A_141, k2_xboole_0(B_142, B_143)))), inference(superposition, [status(thm), theory('equality')], [c_542, c_92])).
% 6.00/2.11  tff(c_695, plain, (![A_82, B_143, A_64, B_12, A_11, C_13]: (k5_xboole_0(k3_enumset1(A_82, A_64, A_11, B_12, C_13), k4_xboole_0(B_143, k2_xboole_0(k1_enumset1(A_82, A_64, A_11), k2_tarski(B_12, C_13))))=k2_xboole_0(k1_enumset1(A_82, A_64, A_11), k2_xboole_0(k2_tarski(B_12, C_13), B_143)))), inference(superposition, [status(thm), theory('equality')], [c_299, c_641])).
% 6.00/2.11  tff(c_1581, plain, (![B_209, C_206, A_210, A_208, A_211, B_207]: (k2_xboole_0(k1_enumset1(A_211, A_210, A_208), k2_xboole_0(k2_tarski(B_209, C_206), B_207))=k2_xboole_0(k3_enumset1(A_211, A_210, A_208, B_209, C_206), B_207))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_299, c_695])).
% 6.00/2.11  tff(c_1626, plain, (![A_210, A_208, A_64, A_211, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_211, A_210, A_208, A_64, A_11), k2_tarski(B_12, C_13))=k2_xboole_0(k1_enumset1(A_211, A_210, A_208), k2_enumset1(A_64, A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_1581])).
% 6.00/2.11  tff(c_1839, plain, (![C_233, A_235, A_234, A_232, B_236, A_237, A_238]: (k2_xboole_0(k3_enumset1(A_237, A_234, A_232, A_238, A_235), k2_tarski(B_236, C_233))=k5_enumset1(A_237, A_234, A_232, A_238, A_235, B_236, C_233))), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_1626])).
% 6.00/2.11  tff(c_301, plain, (![E_88, C_86, B_89, F_87, A_91, D_90]: (k2_xboole_0(k1_tarski(A_91), k3_enumset1(B_89, C_86, D_90, E_88, F_87))=k4_enumset1(A_91, B_89, C_86, D_90, E_88, F_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.00/2.11  tff(c_310, plain, (![E_88, C_3, C_86, B_89, F_87, A_91, D_90]: (k2_xboole_0(k1_tarski(A_91), k2_xboole_0(k3_enumset1(B_89, C_86, D_90, E_88, F_87), C_3))=k2_xboole_0(k4_enumset1(A_91, B_89, C_86, D_90, E_88, F_87), C_3))), inference(superposition, [status(thm), theory('equality')], [c_301, c_2])).
% 6.00/2.11  tff(c_1851, plain, (![C_233, A_235, A_234, A_232, B_236, A_91, A_237, A_238]: (k2_xboole_0(k4_enumset1(A_91, A_237, A_234, A_232, A_238, A_235), k2_tarski(B_236, C_233))=k2_xboole_0(k1_tarski(A_91), k5_enumset1(A_237, A_234, A_232, A_238, A_235, B_236, C_233)))), inference(superposition, [status(thm), theory('equality')], [c_1839, c_310])).
% 6.00/2.11  tff(c_1873, plain, (![C_233, A_235, A_234, A_232, B_236, A_91, A_237, A_238]: (k2_xboole_0(k4_enumset1(A_91, A_237, A_234, A_232, A_238, A_235), k2_tarski(B_236, C_233))=k6_enumset1(A_91, A_237, A_234, A_232, A_238, A_235, B_236, C_233))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1851])).
% 6.00/2.11  tff(c_22, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.00/2.11  tff(c_3347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1873, c_22])).
% 6.00/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.11  
% 6.00/2.11  Inference rules
% 6.00/2.11  ----------------------
% 6.00/2.11  #Ref     : 0
% 6.00/2.11  #Sup     : 851
% 6.00/2.11  #Fact    : 0
% 6.00/2.11  #Define  : 0
% 6.00/2.11  #Split   : 0
% 6.00/2.11  #Chain   : 0
% 6.00/2.11  #Close   : 0
% 6.00/2.11  
% 6.00/2.11  Ordering : KBO
% 6.00/2.11  
% 6.00/2.11  Simplification rules
% 6.00/2.11  ----------------------
% 6.00/2.11  #Subsume      : 0
% 6.00/2.11  #Demod        : 1543
% 6.00/2.11  #Tautology    : 383
% 6.00/2.11  #SimpNegUnit  : 0
% 6.00/2.11  #BackRed      : 1
% 6.00/2.11  
% 6.00/2.11  #Partial instantiations: 0
% 6.00/2.11  #Strategies tried      : 1
% 6.00/2.11  
% 6.00/2.11  Timing (in seconds)
% 6.00/2.11  ----------------------
% 6.00/2.11  Preprocessing        : 0.29
% 6.00/2.11  Parsing              : 0.16
% 6.00/2.11  CNF conversion       : 0.02
% 6.00/2.11  Main loop            : 1.14
% 6.00/2.11  Inferencing          : 0.39
% 6.00/2.11  Reduction            : 0.54
% 6.00/2.11  Demodulation         : 0.47
% 6.00/2.11  BG Simplification    : 0.07
% 6.00/2.11  Subsumption          : 0.09
% 6.00/2.11  Abstraction          : 0.11
% 6.00/2.11  MUC search           : 0.00
% 6.00/2.11  Cooper               : 0.00
% 6.00/2.11  Total                : 1.47
% 6.00/2.11  Index Insertion      : 0.00
% 6.00/2.11  Index Deletion       : 0.00
% 6.00/2.12  Index Matching       : 0.00
% 6.00/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:02 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 163 expanded)
%              Number of leaves         :   31 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :   47 ( 141 expanded)
%              Number of equality atoms :   46 ( 140 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_20,plain,(
    ! [B_43,A_42,H_49,D_45,G_48,E_46,C_44,F_47] : k2_xboole_0(k3_enumset1(A_42,B_43,C_44,D_45,E_46),k1_enumset1(F_47,G_48,H_49)) = k6_enumset1(A_42,B_43,C_44,D_45,E_46,F_47,G_48,H_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k1_tarski(E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,G_33,F_32,A_27,E_31] : k2_xboole_0(k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32),k1_tarski(G_33)) = k5_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_61,B_62,C_63,D_64] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_61,B_62),C_63),D_64) = k2_xboole_0(A_61,k2_xboole_0(k2_xboole_0(B_62,C_63),D_64)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_296,plain,(
    ! [C_103,A_104,B_101,C_100,D_102] : k2_xboole_0(k2_tarski(A_104,B_101),k2_xboole_0(k2_xboole_0(k1_tarski(C_103),C_100),D_102)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_104,B_101,C_103),C_100),D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_330,plain,(
    ! [A_7,A_104,B_101,B_8,D_102] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_104,B_101,A_7),k1_tarski(B_8)),D_102) = k2_xboole_0(k2_tarski(A_104,B_101),k2_xboole_0(k2_tarski(A_7,B_8),D_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_296])).

tff(c_339,plain,(
    ! [A_108,D_109,B_107,A_105,B_106] : k2_xboole_0(k2_tarski(A_105,B_107),k2_xboole_0(k2_tarski(A_108,B_106),D_109)) = k2_xboole_0(k2_enumset1(A_105,B_107,A_108,B_106),D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_330])).

tff(c_366,plain,(
    ! [B_107,C_11,A_105,B_10,A_9] : k2_xboole_0(k2_enumset1(A_105,B_107,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k2_tarski(A_105,B_107),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_339])).

tff(c_387,plain,(
    ! [C_121,A_122,B_119,B_120,A_118] : k2_xboole_0(k2_tarski(A_118,B_120),k1_enumset1(A_122,B_119,C_121)) = k3_enumset1(A_118,B_120,A_122,B_119,C_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_366])).

tff(c_121,plain,(
    ! [A_76,B_77,C_78,D_79] : k2_xboole_0(k1_tarski(A_76),k2_xboole_0(k2_xboole_0(k1_tarski(B_77),C_78),D_79)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_76,B_77),C_78),D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_139,plain,(
    ! [A_76,A_7,B_8,D_79] : k2_xboole_0(k2_xboole_0(k2_tarski(A_76,A_7),k1_tarski(B_8)),D_79) = k2_xboole_0(k1_tarski(A_76),k2_xboole_0(k2_tarski(A_7,B_8),D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_145,plain,(
    ! [A_76,A_7,B_8,D_79] : k2_xboole_0(k1_tarski(A_76),k2_xboole_0(k2_tarski(A_7,B_8),D_79)) = k2_xboole_0(k1_enumset1(A_76,A_7,B_8),D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_399,plain,(
    ! [C_121,A_76,A_122,B_119,B_120,A_118] : k2_xboole_0(k1_enumset1(A_76,A_118,B_120),k1_enumset1(A_122,B_119,C_121)) = k2_xboole_0(k1_tarski(A_76),k3_enumset1(A_118,B_120,A_122,B_119,C_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_145])).

tff(c_14,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k1_tarski(F_26)) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_523,plain,(
    ! [C_144,D_142,C_141,D_143,B_139,A_140] : k2_xboole_0(k1_enumset1(A_140,B_139,C_144),k2_xboole_0(k2_xboole_0(k1_tarski(D_143),C_141),D_142)) = k2_xboole_0(k2_xboole_0(k2_enumset1(A_140,B_139,C_144,D_143),C_141),D_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_560,plain,(
    ! [A_7,C_144,D_142,B_8,B_139,A_140] : k2_xboole_0(k2_xboole_0(k2_enumset1(A_140,B_139,C_144,A_7),k1_tarski(B_8)),D_142) = k2_xboole_0(k1_enumset1(A_140,B_139,C_144),k2_xboole_0(k2_tarski(A_7,B_8),D_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_523])).

tff(c_569,plain,(
    ! [B_150,D_148,A_149,B_145,A_147,C_146] : k2_xboole_0(k1_enumset1(A_149,B_150,C_146),k2_xboole_0(k2_tarski(A_147,B_145),D_148)) = k2_xboole_0(k3_enumset1(A_149,B_150,C_146,A_147,B_145),D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_560])).

tff(c_596,plain,(
    ! [B_150,C_11,B_10,A_149,C_146,A_9] : k2_xboole_0(k3_enumset1(A_149,B_150,C_146,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k1_enumset1(A_149,B_150,C_146),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_569])).

tff(c_602,plain,(
    ! [B_150,C_11,B_10,A_149,C_146,A_9] : k2_xboole_0(k1_tarski(A_149),k3_enumset1(B_150,C_146,A_9,B_10,C_11)) = k4_enumset1(A_149,B_150,C_146,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_14,c_596])).

tff(c_603,plain,(
    ! [C_121,A_76,A_122,B_119,B_120,A_118] : k2_xboole_0(k1_enumset1(A_76,A_118,B_120),k1_enumset1(A_122,B_119,C_121)) = k4_enumset1(A_76,A_118,B_120,A_122,B_119,C_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_399])).

tff(c_338,plain,(
    ! [A_7,A_104,B_101,B_8,D_102] : k2_xboole_0(k2_tarski(A_104,B_101),k2_xboole_0(k2_tarski(A_7,B_8),D_102)) = k2_xboole_0(k2_enumset1(A_104,B_101,A_7,B_8),D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_330])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_1,B_2),C_3),D_4) = k2_xboole_0(A_1,k2_xboole_0(k2_xboole_0(B_2,C_3),D_4)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_193,plain,(
    ! [D_96,A_99,D_95,B_97,C_98] : k2_xboole_0(k2_xboole_0(A_99,k2_xboole_0(k2_xboole_0(B_97,C_98),D_95)),D_96) = k2_xboole_0(k2_xboole_0(A_99,B_97),k2_xboole_0(k2_xboole_0(C_98,D_95),D_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_650,plain,(
    ! [A_163,D_166,A_165,D_167,B_164] : k2_xboole_0(k2_xboole_0(A_163,k1_tarski(A_165)),k2_xboole_0(k2_xboole_0(k1_tarski(B_164),D_166),D_167)) = k2_xboole_0(k2_xboole_0(A_163,k2_xboole_0(k2_tarski(A_165,B_164),D_166)),D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_750,plain,(
    ! [A_163,A_7,A_165,D_167,B_8] : k2_xboole_0(k2_xboole_0(A_163,k2_xboole_0(k2_tarski(A_165,A_7),k1_tarski(B_8))),D_167) = k2_xboole_0(k2_xboole_0(A_163,k1_tarski(A_165)),k2_xboole_0(k2_tarski(A_7,B_8),D_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_650])).

tff(c_775,plain,(
    ! [A_170,D_168,A_171,A_172,B_169] : k2_xboole_0(k2_xboole_0(A_171,k1_tarski(A_172)),k2_xboole_0(k2_tarski(A_170,B_169),D_168)) = k2_xboole_0(k2_xboole_0(A_171,k1_enumset1(A_172,A_170,B_169)),D_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_750])).

tff(c_877,plain,(
    ! [A_176,A_177,A_175,C_174,B_173] : k2_xboole_0(k2_xboole_0(A_176,k1_enumset1(A_175,A_177,B_173)),k1_tarski(C_174)) = k2_xboole_0(k2_xboole_0(A_176,k1_tarski(A_175)),k1_enumset1(A_177,B_173,C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_775])).

tff(c_89,plain,(
    ! [C_11,B_10,C_63,D_64,A_9] : k2_xboole_0(k2_tarski(A_9,B_10),k2_xboole_0(k2_xboole_0(k1_tarski(C_11),C_63),D_64)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_9,B_10,C_11),C_63),D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_901,plain,(
    ! [C_11,B_10,A_177,A_175,C_174,B_173,A_9] : k2_xboole_0(k2_tarski(A_9,B_10),k2_xboole_0(k2_xboole_0(k1_tarski(C_11),k1_tarski(A_175)),k1_enumset1(A_177,B_173,C_174))) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(A_175,A_177,B_173)),k1_tarski(C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_89])).

tff(c_969,plain,(
    ! [B_180,C_182,A_181,A_178,C_184,B_179,A_183] : k2_xboole_0(k2_enumset1(A_183,B_180,C_182,A_178),k1_enumset1(A_181,B_179,C_184)) = k5_enumset1(A_183,B_180,C_182,A_178,A_181,B_179,C_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_603,c_338,c_6,c_901])).

tff(c_855,plain,(
    ! [C_11,A_171,B_10,A_172,A_9] : k2_xboole_0(k2_xboole_0(A_171,k1_enumset1(A_172,A_9,B_10)),k1_tarski(C_11)) = k2_xboole_0(k2_xboole_0(A_171,k1_tarski(A_172)),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_775])).

tff(c_975,plain,(
    ! [B_180,C_182,A_181,A_178,C_11,C_184,B_179,A_183] : k2_xboole_0(k2_xboole_0(k2_enumset1(A_183,B_180,C_182,A_178),k1_tarski(A_181)),k1_enumset1(B_179,C_184,C_11)) = k2_xboole_0(k5_enumset1(A_183,B_180,C_182,A_178,A_181,B_179,C_184),k1_tarski(C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_855])).

tff(c_989,plain,(
    ! [B_180,C_182,A_181,A_178,C_11,C_184,B_179,A_183] : k2_xboole_0(k5_enumset1(A_183,B_180,C_182,A_178,A_181,B_179,C_184),k1_tarski(C_11)) = k6_enumset1(A_183,B_180,C_182,A_178,A_181,B_179,C_184,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_975])).

tff(c_22,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.81  
% 4.62/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.81  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.62/1.81  
% 4.62/1.81  %Foreground sorts:
% 4.62/1.81  
% 4.62/1.81  
% 4.62/1.81  %Background operators:
% 4.62/1.81  
% 4.62/1.81  
% 4.62/1.81  %Foreground operators:
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.62/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.62/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.81  
% 4.62/1.83  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 4.62/1.83  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 4.62/1.83  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 4.62/1.83  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 4.62/1.83  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.62/1.83  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.62/1.83  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 4.62/1.83  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 4.62/1.83  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 4.62/1.83  tff(c_20, plain, (![B_43, A_42, H_49, D_45, G_48, E_46, C_44, F_47]: (k2_xboole_0(k3_enumset1(A_42, B_43, C_44, D_45, E_46), k1_enumset1(F_47, G_48, H_49))=k6_enumset1(A_42, B_43, C_44, D_45, E_46, F_47, G_48, H_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.83  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k1_tarski(E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.83  tff(c_16, plain, (![C_29, D_30, B_28, G_33, F_32, A_27, E_31]: (k2_xboole_0(k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32), k1_tarski(G_33))=k5_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.62/1.83  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.83  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.62/1.83  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.83  tff(c_65, plain, (![A_61, B_62, C_63, D_64]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_61, B_62), C_63), D_64)=k2_xboole_0(A_61, k2_xboole_0(k2_xboole_0(B_62, C_63), D_64)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.83  tff(c_296, plain, (![C_103, A_104, B_101, C_100, D_102]: (k2_xboole_0(k2_tarski(A_104, B_101), k2_xboole_0(k2_xboole_0(k1_tarski(C_103), C_100), D_102))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_104, B_101, C_103), C_100), D_102))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 4.62/1.83  tff(c_330, plain, (![A_7, A_104, B_101, B_8, D_102]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_104, B_101, A_7), k1_tarski(B_8)), D_102)=k2_xboole_0(k2_tarski(A_104, B_101), k2_xboole_0(k2_tarski(A_7, B_8), D_102)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_296])).
% 4.62/1.83  tff(c_339, plain, (![A_108, D_109, B_107, A_105, B_106]: (k2_xboole_0(k2_tarski(A_105, B_107), k2_xboole_0(k2_tarski(A_108, B_106), D_109))=k2_xboole_0(k2_enumset1(A_105, B_107, A_108, B_106), D_109))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_330])).
% 4.62/1.83  tff(c_366, plain, (![B_107, C_11, A_105, B_10, A_9]: (k2_xboole_0(k2_enumset1(A_105, B_107, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k2_tarski(A_105, B_107), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_339])).
% 4.62/1.83  tff(c_387, plain, (![C_121, A_122, B_119, B_120, A_118]: (k2_xboole_0(k2_tarski(A_118, B_120), k1_enumset1(A_122, B_119, C_121))=k3_enumset1(A_118, B_120, A_122, B_119, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_366])).
% 4.62/1.83  tff(c_121, plain, (![A_76, B_77, C_78, D_79]: (k2_xboole_0(k1_tarski(A_76), k2_xboole_0(k2_xboole_0(k1_tarski(B_77), C_78), D_79))=k2_xboole_0(k2_xboole_0(k2_tarski(A_76, B_77), C_78), D_79))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 4.62/1.83  tff(c_139, plain, (![A_76, A_7, B_8, D_79]: (k2_xboole_0(k2_xboole_0(k2_tarski(A_76, A_7), k1_tarski(B_8)), D_79)=k2_xboole_0(k1_tarski(A_76), k2_xboole_0(k2_tarski(A_7, B_8), D_79)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 4.62/1.83  tff(c_145, plain, (![A_76, A_7, B_8, D_79]: (k2_xboole_0(k1_tarski(A_76), k2_xboole_0(k2_tarski(A_7, B_8), D_79))=k2_xboole_0(k1_enumset1(A_76, A_7, B_8), D_79))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_139])).
% 4.62/1.83  tff(c_399, plain, (![C_121, A_76, A_122, B_119, B_120, A_118]: (k2_xboole_0(k1_enumset1(A_76, A_118, B_120), k1_enumset1(A_122, B_119, C_121))=k2_xboole_0(k1_tarski(A_76), k3_enumset1(A_118, B_120, A_122, B_119, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_387, c_145])).
% 4.62/1.83  tff(c_14, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k1_tarski(F_26))=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.83  tff(c_523, plain, (![C_144, D_142, C_141, D_143, B_139, A_140]: (k2_xboole_0(k1_enumset1(A_140, B_139, C_144), k2_xboole_0(k2_xboole_0(k1_tarski(D_143), C_141), D_142))=k2_xboole_0(k2_xboole_0(k2_enumset1(A_140, B_139, C_144, D_143), C_141), D_142))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 4.62/1.83  tff(c_560, plain, (![A_7, C_144, D_142, B_8, B_139, A_140]: (k2_xboole_0(k2_xboole_0(k2_enumset1(A_140, B_139, C_144, A_7), k1_tarski(B_8)), D_142)=k2_xboole_0(k1_enumset1(A_140, B_139, C_144), k2_xboole_0(k2_tarski(A_7, B_8), D_142)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_523])).
% 4.62/1.83  tff(c_569, plain, (![B_150, D_148, A_149, B_145, A_147, C_146]: (k2_xboole_0(k1_enumset1(A_149, B_150, C_146), k2_xboole_0(k2_tarski(A_147, B_145), D_148))=k2_xboole_0(k3_enumset1(A_149, B_150, C_146, A_147, B_145), D_148))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_560])).
% 4.62/1.83  tff(c_596, plain, (![B_150, C_11, B_10, A_149, C_146, A_9]: (k2_xboole_0(k3_enumset1(A_149, B_150, C_146, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k1_enumset1(A_149, B_150, C_146), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_569])).
% 4.62/1.83  tff(c_602, plain, (![B_150, C_11, B_10, A_149, C_146, A_9]: (k2_xboole_0(k1_tarski(A_149), k3_enumset1(B_150, C_146, A_9, B_10, C_11))=k4_enumset1(A_149, B_150, C_146, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_399, c_14, c_596])).
% 4.62/1.83  tff(c_603, plain, (![C_121, A_76, A_122, B_119, B_120, A_118]: (k2_xboole_0(k1_enumset1(A_76, A_118, B_120), k1_enumset1(A_122, B_119, C_121))=k4_enumset1(A_76, A_118, B_120, A_122, B_119, C_121))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_399])).
% 4.62/1.83  tff(c_338, plain, (![A_7, A_104, B_101, B_8, D_102]: (k2_xboole_0(k2_tarski(A_104, B_101), k2_xboole_0(k2_tarski(A_7, B_8), D_102))=k2_xboole_0(k2_enumset1(A_104, B_101, A_7, B_8), D_102))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_330])).
% 4.62/1.83  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_1, B_2), C_3), D_4)=k2_xboole_0(A_1, k2_xboole_0(k2_xboole_0(B_2, C_3), D_4)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.83  tff(c_193, plain, (![D_96, A_99, D_95, B_97, C_98]: (k2_xboole_0(k2_xboole_0(A_99, k2_xboole_0(k2_xboole_0(B_97, C_98), D_95)), D_96)=k2_xboole_0(k2_xboole_0(A_99, B_97), k2_xboole_0(k2_xboole_0(C_98, D_95), D_96)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 4.62/1.83  tff(c_650, plain, (![A_163, D_166, A_165, D_167, B_164]: (k2_xboole_0(k2_xboole_0(A_163, k1_tarski(A_165)), k2_xboole_0(k2_xboole_0(k1_tarski(B_164), D_166), D_167))=k2_xboole_0(k2_xboole_0(A_163, k2_xboole_0(k2_tarski(A_165, B_164), D_166)), D_167))), inference(superposition, [status(thm), theory('equality')], [c_6, c_193])).
% 4.62/1.83  tff(c_750, plain, (![A_163, A_7, A_165, D_167, B_8]: (k2_xboole_0(k2_xboole_0(A_163, k2_xboole_0(k2_tarski(A_165, A_7), k1_tarski(B_8))), D_167)=k2_xboole_0(k2_xboole_0(A_163, k1_tarski(A_165)), k2_xboole_0(k2_tarski(A_7, B_8), D_167)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_650])).
% 4.62/1.83  tff(c_775, plain, (![A_170, D_168, A_171, A_172, B_169]: (k2_xboole_0(k2_xboole_0(A_171, k1_tarski(A_172)), k2_xboole_0(k2_tarski(A_170, B_169), D_168))=k2_xboole_0(k2_xboole_0(A_171, k1_enumset1(A_172, A_170, B_169)), D_168))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_750])).
% 4.62/1.83  tff(c_877, plain, (![A_176, A_177, A_175, C_174, B_173]: (k2_xboole_0(k2_xboole_0(A_176, k1_enumset1(A_175, A_177, B_173)), k1_tarski(C_174))=k2_xboole_0(k2_xboole_0(A_176, k1_tarski(A_175)), k1_enumset1(A_177, B_173, C_174)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_775])).
% 4.62/1.83  tff(c_89, plain, (![C_11, B_10, C_63, D_64, A_9]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_xboole_0(k2_xboole_0(k1_tarski(C_11), C_63), D_64))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_9, B_10, C_11), C_63), D_64))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 4.62/1.83  tff(c_901, plain, (![C_11, B_10, A_177, A_175, C_174, B_173, A_9]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_xboole_0(k2_xboole_0(k1_tarski(C_11), k1_tarski(A_175)), k1_enumset1(A_177, B_173, C_174)))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(A_175, A_177, B_173)), k1_tarski(C_174)))), inference(superposition, [status(thm), theory('equality')], [c_877, c_89])).
% 4.62/1.83  tff(c_969, plain, (![B_180, C_182, A_181, A_178, C_184, B_179, A_183]: (k2_xboole_0(k2_enumset1(A_183, B_180, C_182, A_178), k1_enumset1(A_181, B_179, C_184))=k5_enumset1(A_183, B_180, C_182, A_178, A_181, B_179, C_184))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_603, c_338, c_6, c_901])).
% 4.62/1.83  tff(c_855, plain, (![C_11, A_171, B_10, A_172, A_9]: (k2_xboole_0(k2_xboole_0(A_171, k1_enumset1(A_172, A_9, B_10)), k1_tarski(C_11))=k2_xboole_0(k2_xboole_0(A_171, k1_tarski(A_172)), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_775])).
% 4.62/1.83  tff(c_975, plain, (![B_180, C_182, A_181, A_178, C_11, C_184, B_179, A_183]: (k2_xboole_0(k2_xboole_0(k2_enumset1(A_183, B_180, C_182, A_178), k1_tarski(A_181)), k1_enumset1(B_179, C_184, C_11))=k2_xboole_0(k5_enumset1(A_183, B_180, C_182, A_178, A_181, B_179, C_184), k1_tarski(C_11)))), inference(superposition, [status(thm), theory('equality')], [c_969, c_855])).
% 4.62/1.83  tff(c_989, plain, (![B_180, C_182, A_181, A_178, C_11, C_184, B_179, A_183]: (k2_xboole_0(k5_enumset1(A_183, B_180, C_182, A_178, A_181, B_179, C_184), k1_tarski(C_11))=k6_enumset1(A_183, B_180, C_182, A_178, A_181, B_179, C_184, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_975])).
% 4.62/1.83  tff(c_22, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.62/1.83  tff(c_1643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_989, c_22])).
% 4.62/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.83  
% 4.62/1.83  Inference rules
% 4.62/1.83  ----------------------
% 4.62/1.83  #Ref     : 0
% 4.62/1.83  #Sup     : 408
% 4.62/1.83  #Fact    : 0
% 4.62/1.83  #Define  : 0
% 4.62/1.83  #Split   : 0
% 4.62/1.83  #Chain   : 0
% 4.62/1.83  #Close   : 0
% 4.62/1.83  
% 4.62/1.83  Ordering : KBO
% 4.62/1.83  
% 4.62/1.83  Simplification rules
% 4.62/1.83  ----------------------
% 4.62/1.83  #Subsume      : 0
% 4.62/1.83  #Demod        : 576
% 4.62/1.83  #Tautology    : 182
% 4.62/1.83  #SimpNegUnit  : 0
% 4.62/1.83  #BackRed      : 2
% 4.62/1.83  
% 4.62/1.83  #Partial instantiations: 0
% 4.62/1.83  #Strategies tried      : 1
% 4.62/1.83  
% 4.62/1.83  Timing (in seconds)
% 4.62/1.83  ----------------------
% 4.62/1.83  Preprocessing        : 0.31
% 4.62/1.83  Parsing              : 0.18
% 4.62/1.83  CNF conversion       : 0.02
% 4.62/1.83  Main loop            : 0.73
% 4.62/1.83  Inferencing          : 0.29
% 4.62/1.83  Reduction            : 0.32
% 4.62/1.83  Demodulation         : 0.28
% 4.62/1.83  BG Simplification    : 0.05
% 4.62/1.83  Subsumption          : 0.05
% 4.62/1.83  Abstraction          : 0.07
% 4.62/1.83  MUC search           : 0.00
% 4.62/1.83  Cooper               : 0.00
% 4.62/1.83  Total                : 1.08
% 4.62/1.83  Index Insertion      : 0.00
% 4.62/1.83  Index Deletion       : 0.00
% 4.62/1.83  Index Matching       : 0.00
% 4.62/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

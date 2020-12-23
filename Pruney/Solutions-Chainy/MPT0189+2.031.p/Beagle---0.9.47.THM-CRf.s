%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:54 EST 2020

% Result     : Theorem 12.22s
% Output     : CNFRefutation 12.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 852 expanded)
%              Number of leaves         :   33 ( 299 expanded)
%              Depth                    :   20
%              Number of atoms          :  100 ( 833 expanded)
%              Number of equality atoms :   99 ( 832 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [A_8,C_10,D_11,B_9] : k2_enumset1(A_8,C_10,D_11,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_57,B_58,C_59,D_60] : k3_enumset1(A_57,A_57,B_58,C_59,D_60) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_61,B_62,E_65,C_63,D_64] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,E_65) = k3_enumset1(A_61,B_62,C_63,D_64,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [B_67,A_66,F_71,C_68,E_70,D_69] : k5_enumset1(A_66,A_66,B_67,C_68,D_69,E_70,F_71) = k4_enumset1(A_66,B_67,C_68,D_69,E_70,F_71) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_375,plain,(
    ! [B_129,A_130,D_132,C_134,E_131,G_128,F_133] : k2_xboole_0(k3_enumset1(A_130,B_129,C_134,D_132,E_131),k2_tarski(F_133,G_128)) = k5_enumset1(A_130,B_129,C_134,D_132,E_131,F_133,G_128) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_384,plain,(
    ! [A_57,B_58,G_128,F_133,D_60,C_59] : k5_enumset1(A_57,A_57,B_58,C_59,D_60,F_133,G_128) = k2_xboole_0(k2_enumset1(A_57,B_58,C_59,D_60),k2_tarski(F_133,G_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_375])).

tff(c_419,plain,(
    ! [C_148,B_144,G_145,D_147,F_143,A_146] : k2_xboole_0(k2_enumset1(A_146,B_144,C_148,D_147),k2_tarski(F_143,G_145)) = k4_enumset1(A_146,B_144,C_148,D_147,F_143,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_384])).

tff(c_440,plain,(
    ! [C_56,G_145,F_143,B_55,A_54] : k4_enumset1(A_54,A_54,B_55,C_56,F_143,G_145) = k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k2_tarski(F_143,G_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_419])).

tff(c_447,plain,(
    ! [F_149,B_152,G_153,C_150,A_151] : k2_xboole_0(k1_enumset1(A_151,B_152,C_150),k2_tarski(F_149,G_153)) = k3_enumset1(A_151,B_152,C_150,F_149,G_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_440])).

tff(c_468,plain,(
    ! [A_52,B_53,F_149,G_153] : k3_enumset1(A_52,A_52,B_53,F_149,G_153) = k2_xboole_0(k2_tarski(A_52,B_53),k2_tarski(F_149,G_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_447])).

tff(c_474,plain,(
    ! [A_52,B_53,F_149,G_153] : k2_xboole_0(k2_tarski(A_52,B_53),k2_tarski(F_149,G_153)) = k2_enumset1(A_52,B_53,F_149,G_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_468])).

tff(c_20,plain,(
    ! [A_51] : k2_tarski(A_51,A_51) = k1_tarski(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_475,plain,(
    ! [A_154,B_155,F_156,G_157] : k2_xboole_0(k2_tarski(A_154,B_155),k2_tarski(F_156,G_157)) = k2_enumset1(A_154,B_155,F_156,G_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_468])).

tff(c_526,plain,(
    ! [A_171,B_172,A_173] : k2_xboole_0(k2_tarski(A_171,B_172),k1_tarski(A_173)) = k2_enumset1(A_171,B_172,A_173,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_475])).

tff(c_984,plain,(
    ! [A_207,B_208,A_209] : k2_xboole_0(k2_tarski(A_207,B_208),k1_tarski(A_209)) = k2_enumset1(A_207,A_209,A_209,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_8])).

tff(c_72,plain,(
    ! [B_86,C_87,A_88] : k1_enumset1(B_86,C_87,A_88) = k1_enumset1(A_88,B_86,C_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_86,C_87] : k1_enumset1(B_86,C_87,B_86) = k2_tarski(B_86,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_210,plain,(
    ! [A_96,C_97,D_98,B_99] : k2_enumset1(A_96,C_97,D_98,B_99) = k2_enumset1(A_96,B_99,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_226,plain,(
    ! [B_99,C_97,D_98] : k2_enumset1(B_99,C_97,D_98,B_99) = k1_enumset1(B_99,C_97,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_24])).

tff(c_543,plain,(
    ! [A_173,B_172] : k2_xboole_0(k2_tarski(A_173,B_172),k1_tarski(A_173)) = k1_enumset1(A_173,B_172,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_226])).

tff(c_586,plain,(
    ! [A_173,B_172] : k2_xboole_0(k2_tarski(A_173,B_172),k1_tarski(A_173)) = k2_tarski(A_173,B_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_543])).

tff(c_1209,plain,(
    ! [A_212,B_213] : k2_enumset1(A_212,A_212,A_212,B_213) = k2_tarski(A_212,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_586])).

tff(c_1326,plain,(
    ! [C_214,D_215] : k2_enumset1(C_214,C_214,D_215,C_214) = k2_tarski(C_214,D_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1209])).

tff(c_390,plain,(
    ! [A_57,B_58,G_128,F_133,D_60,C_59] : k2_xboole_0(k2_enumset1(A_57,B_58,C_59,D_60),k2_tarski(F_133,G_128)) = k4_enumset1(A_57,B_58,C_59,D_60,F_133,G_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_384])).

tff(c_1360,plain,(
    ! [C_214,D_215,F_133,G_128] : k4_enumset1(C_214,C_214,D_215,C_214,F_133,G_128) = k2_xboole_0(k2_tarski(C_214,D_215),k2_tarski(F_133,G_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_390])).

tff(c_5293,plain,(
    ! [C_353,D_354,F_355,G_356] : k4_enumset1(C_353,C_353,D_354,C_353,F_355,G_356) = k2_enumset1(C_353,D_354,F_355,G_356) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_1360])).

tff(c_5329,plain,(
    ! [C_353,D_354,F_355,G_356] : k3_enumset1(C_353,D_354,C_353,F_355,G_356) = k2_enumset1(C_353,D_354,F_355,G_356) ),
    inference(superposition,[status(thm),theory(equality)],[c_5293,c_28])).

tff(c_107,plain,(
    ! [B_53,A_52] : k1_enumset1(B_53,A_52,A_52) = k2_tarski(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_72])).

tff(c_484,plain,(
    ! [A_51,F_156,G_157] : k2_xboole_0(k1_tarski(A_51),k2_tarski(F_156,G_157)) = k2_enumset1(A_51,A_51,F_156,G_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_475])).

tff(c_504,plain,(
    ! [A_166,F_167,G_168] : k2_xboole_0(k1_tarski(A_166),k2_tarski(F_167,G_168)) = k1_enumset1(A_166,F_167,G_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_484])).

tff(c_513,plain,(
    ! [A_166,A_51] : k2_xboole_0(k1_tarski(A_166),k1_tarski(A_51)) = k1_enumset1(A_166,A_51,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_504])).

tff(c_516,plain,(
    ! [A_166,A_51] : k2_xboole_0(k1_tarski(A_166),k1_tarski(A_51)) = k2_tarski(A_51,A_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_513])).

tff(c_7721,plain,(
    ! [D_427,C_428,A_425,A_429,B_426] : k4_enumset1(A_429,B_426,C_428,D_427,A_425,A_425) = k2_xboole_0(k2_enumset1(A_429,B_426,C_428,D_427),k1_tarski(A_425)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_419])).

tff(c_8022,plain,(
    ! [A_435,B_436,C_437,A_438] : k4_enumset1(A_435,A_435,B_436,C_437,A_438,A_438) = k2_xboole_0(k1_enumset1(A_435,B_436,C_437),k1_tarski(A_438)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7721])).

tff(c_15042,plain,(
    ! [A_537,B_538,A_539] : k4_enumset1(A_537,A_537,A_537,B_538,A_539,A_539) = k2_xboole_0(k2_tarski(A_537,B_538),k1_tarski(A_539)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8022])).

tff(c_15279,plain,(
    ! [A_540,B_541] : k4_enumset1(A_540,A_540,A_540,B_541,A_540,A_540) = k2_tarski(A_540,B_541) ),
    inference(superposition,[status(thm),theory(equality)],[c_15042,c_586])).

tff(c_446,plain,(
    ! [C_56,G_145,F_143,B_55,A_54] : k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k2_tarski(F_143,G_145)) = k3_enumset1(A_54,B_55,C_56,F_143,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_440])).

tff(c_431,plain,(
    ! [G_145,B_99,C_97,F_143,D_98] : k4_enumset1(B_99,C_97,D_98,B_99,F_143,G_145) = k2_xboole_0(k1_enumset1(B_99,C_97,D_98),k2_tarski(F_143,G_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_419])).

tff(c_11110,plain,(
    ! [G_145,B_99,C_97,F_143,D_98] : k4_enumset1(B_99,C_97,D_98,B_99,F_143,G_145) = k3_enumset1(B_99,C_97,D_98,F_143,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_431])).

tff(c_15292,plain,(
    ! [B_541] : k3_enumset1(B_541,B_541,B_541,B_541,B_541) = k2_tarski(B_541,B_541) ),
    inference(superposition,[status(thm),theory(equality)],[c_15279,c_11110])).

tff(c_15409,plain,(
    ! [B_541] : k3_enumset1(B_541,B_541,B_541,B_541,B_541) = k1_tarski(B_541) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_15292])).

tff(c_32,plain,(
    ! [B_73,G_78,C_74,E_76,A_72,D_75,F_77] : k6_enumset1(A_72,A_72,B_73,C_74,D_75,E_76,F_77,G_78) = k5_enumset1(A_72,B_73,C_74,D_75,E_76,F_77,G_78) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_491,plain,(
    ! [A_163,E_165,C_159,D_161,F_162,H_160,B_164,G_158] : k2_xboole_0(k5_enumset1(A_163,B_164,C_159,D_161,E_165,F_162,G_158),k1_tarski(H_160)) = k6_enumset1(A_163,B_164,C_159,D_161,E_165,F_162,G_158,H_160) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_500,plain,(
    ! [B_67,A_66,F_71,C_68,E_70,H_160,D_69] : k6_enumset1(A_66,A_66,B_67,C_68,D_69,E_70,F_71,H_160) = k2_xboole_0(k4_enumset1(A_66,B_67,C_68,D_69,E_70,F_71),k1_tarski(H_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_491])).

tff(c_503,plain,(
    ! [B_67,A_66,F_71,C_68,E_70,H_160,D_69] : k2_xboole_0(k4_enumset1(A_66,B_67,C_68,D_69,E_70,F_71),k1_tarski(H_160)) = k5_enumset1(A_66,B_67,C_68,D_69,E_70,F_71,H_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_500])).

tff(c_702,plain,(
    ! [D_183,C_181,A_177,F_180,G_179,H_178,B_184,E_182] : k2_xboole_0(k4_enumset1(A_177,B_184,C_181,D_183,E_182,F_180),k2_tarski(G_179,H_178)) = k6_enumset1(A_177,B_184,C_181,D_183,E_182,F_180,G_179,H_178) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_714,plain,(
    ! [D_183,C_181,A_177,F_180,A_51,B_184,E_182] : k6_enumset1(A_177,B_184,C_181,D_183,E_182,F_180,A_51,A_51) = k2_xboole_0(k4_enumset1(A_177,B_184,C_181,D_183,E_182,F_180),k1_tarski(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_702])).

tff(c_3253,plain,(
    ! [E_305,D_303,F_304,C_307,A_306,A_302,B_308] : k6_enumset1(A_306,B_308,C_307,D_303,E_305,F_304,A_302,A_302) = k5_enumset1(A_306,B_308,C_307,D_303,E_305,F_304,A_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_714])).

tff(c_3264,plain,(
    ! [E_305,D_303,F_304,C_307,A_302,B_308] : k5_enumset1(B_308,C_307,D_303,E_305,F_304,A_302,A_302) = k5_enumset1(B_308,B_308,C_307,D_303,E_305,F_304,A_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_3253,c_32])).

tff(c_3278,plain,(
    ! [E_305,D_303,F_304,C_307,A_302,B_308] : k5_enumset1(B_308,C_307,D_303,E_305,F_304,A_302,A_302) = k4_enumset1(B_308,C_307,D_303,E_305,F_304,A_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3264])).

tff(c_387,plain,(
    ! [B_129,A_130,D_132,C_134,E_131,A_51] : k5_enumset1(A_130,B_129,C_134,D_132,E_131,A_51,A_51) = k2_xboole_0(k3_enumset1(A_130,B_129,C_134,D_132,E_131),k1_tarski(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_375])).

tff(c_17108,plain,(
    ! [C_572,B_573,A_569,E_570,A_571,D_574] : k2_xboole_0(k3_enumset1(A_569,B_573,C_572,D_574,E_570),k1_tarski(A_571)) = k4_enumset1(A_569,B_573,C_572,D_574,E_570,A_571) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3278,c_387])).

tff(c_17117,plain,(
    ! [B_541,A_571] : k4_enumset1(B_541,B_541,B_541,B_541,B_541,A_571) = k2_xboole_0(k1_tarski(B_541),k1_tarski(A_571)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15409,c_17108])).

tff(c_17236,plain,(
    ! [B_575,A_576] : k4_enumset1(B_575,B_575,B_575,B_575,B_575,A_576) = k2_tarski(A_576,B_575) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_17117])).

tff(c_490,plain,(
    ! [A_51,F_156,G_157] : k2_xboole_0(k1_tarski(A_51),k2_tarski(F_156,G_157)) = k1_enumset1(A_51,F_156,G_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_484])).

tff(c_2044,plain,(
    ! [A_266,B_267,C_268,A_269] : k3_enumset1(A_266,B_267,C_268,A_269,A_269) = k2_xboole_0(k1_enumset1(A_266,B_267,C_268),k1_tarski(A_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_447])).

tff(c_2188,plain,(
    ! [B_272,A_273,A_274] : k3_enumset1(B_272,A_273,A_273,A_274,A_274) = k2_xboole_0(k2_tarski(A_273,B_272),k1_tarski(A_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_2044])).

tff(c_2296,plain,(
    ! [B_275,A_276] : k3_enumset1(B_275,A_276,A_276,A_276,A_276) = k2_tarski(A_276,B_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_2188,c_586])).

tff(c_2335,plain,(
    ! [A_276] : k2_enumset1(A_276,A_276,A_276,A_276) = k2_tarski(A_276,A_276) ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_26])).

tff(c_2380,plain,(
    ! [A_277] : k2_enumset1(A_277,A_277,A_277,A_277) = k1_tarski(A_277) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2335])).

tff(c_2416,plain,(
    ! [A_277,F_133,G_128] : k4_enumset1(A_277,A_277,A_277,A_277,F_133,G_128) = k2_xboole_0(k1_tarski(A_277),k2_tarski(F_133,G_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2380,c_390])).

tff(c_2487,plain,(
    ! [A_277,F_133,G_128] : k4_enumset1(A_277,A_277,A_277,A_277,F_133,G_128) = k1_enumset1(A_277,F_133,G_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_2416])).

tff(c_17432,plain,(
    ! [B_577,A_578] : k1_enumset1(B_577,B_577,A_578) = k2_tarski(A_578,B_577) ),
    inference(superposition,[status(thm),theory(equality)],[c_17236,c_2487])).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_465,plain,(
    ! [B_6,C_7,F_149,G_153,A_5] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k2_tarski(F_149,G_153)) = k3_enumset1(B_6,C_7,A_5,F_149,G_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_447])).

tff(c_17471,plain,(
    ! [B_577,A_578,F_149,G_153] : k3_enumset1(B_577,A_578,B_577,F_149,G_153) = k2_xboole_0(k2_tarski(A_578,B_577),k2_tarski(F_149,G_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17432,c_465])).

tff(c_17570,plain,(
    ! [B_577,A_578,F_149,G_153] : k2_enumset1(B_577,A_578,F_149,G_153) = k2_enumset1(A_578,B_577,F_149,G_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5329,c_474,c_17471])).

tff(c_3252,plain,(
    ! [D_183,C_181,A_177,F_180,A_51,B_184,E_182] : k6_enumset1(A_177,B_184,C_181,D_183,E_182,F_180,A_51,A_51) = k5_enumset1(A_177,B_184,C_181,D_183,E_182,F_180,A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_714])).

tff(c_10,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k3_enumset1(A_12,B_13,C_14,D_15,E_16),k2_tarski(F_17,G_18)) = k5_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_721,plain,(
    ! [H_187,F_185,D_188,B_190,A_192,E_189,C_186,G_191] : k2_xboole_0(k3_enumset1(A_192,B_190,C_186,D_188,E_189),k1_enumset1(F_185,G_191,H_187)) = k6_enumset1(A_192,B_190,C_186,D_188,E_189,F_185,G_191,H_187) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6775,plain,(
    ! [C_405,B_407,C_409,A_410,E_408,A_411,D_412,B_406] : k2_xboole_0(k3_enumset1(A_411,B_407,C_405,D_412,E_408),k1_enumset1(B_406,C_409,A_410)) = k6_enumset1(A_411,B_407,C_405,D_412,E_408,A_410,B_406,C_409) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_721])).

tff(c_6877,plain,(
    ! [C_405,B_53,B_407,E_408,A_52,A_411,D_412] : k6_enumset1(A_411,B_407,C_405,D_412,E_408,B_53,A_52,A_52) = k2_xboole_0(k3_enumset1(A_411,B_407,C_405,D_412,E_408),k2_tarski(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6775])).

tff(c_14950,plain,(
    ! [D_533,E_532,C_536,A_530,A_535,B_531,B_534] : k5_enumset1(A_535,B_534,C_536,D_533,E_532,B_531,A_530) = k5_enumset1(A_535,B_534,C_536,D_533,E_532,A_530,B_531) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_10,c_6877])).

tff(c_22120,plain,(
    ! [B_653,F_651,D_655,A_650,E_652,C_654] : k5_enumset1(A_650,A_650,B_653,C_654,D_655,F_651,E_652) = k4_enumset1(A_650,B_653,C_654,D_655,E_652,F_651) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_14950])).

tff(c_23502,plain,(
    ! [D_667,C_666,F_663,B_665,A_662,E_664] : k4_enumset1(A_662,B_665,C_666,D_667,F_663,E_664) = k4_enumset1(A_662,B_665,C_666,D_667,E_664,F_663) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_22120])).

tff(c_24146,plain,(
    ! [C_670,E_674,F_671,D_673,B_672] : k4_enumset1(B_672,B_672,C_670,D_673,E_674,F_671) = k3_enumset1(B_672,C_670,D_673,F_671,E_674) ),
    inference(superposition,[status(thm),theory(equality)],[c_23502,c_28])).

tff(c_24885,plain,(
    ! [D_684,F_687,B_688,E_685,C_686] : k3_enumset1(B_688,C_686,D_684,F_687,E_685) = k3_enumset1(B_688,C_686,D_684,E_685,F_687) ),
    inference(superposition,[status(thm),theory(equality)],[c_24146,c_28])).

tff(c_25169,plain,(
    ! [A_696,B_697,D_698,C_699] : k3_enumset1(A_696,A_696,B_697,D_698,C_699) = k2_enumset1(A_696,B_697,C_699,D_698) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_24885])).

tff(c_25377,plain,(
    ! [A_696,B_697,D_698,C_699] : k2_enumset1(A_696,B_697,D_698,C_699) = k2_enumset1(A_696,B_697,C_699,D_698) ),
    inference(superposition,[status(thm),theory(equality)],[c_25169,c_26])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_34])).

tff(c_26720,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25377,c_35])).

tff(c_29787,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17570,c_17570,c_26720])).

tff(c_29790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_29787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.22/4.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.22/4.97  
% 12.22/4.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.22/4.97  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.22/4.97  
% 12.22/4.97  %Foreground sorts:
% 12.22/4.97  
% 12.22/4.97  
% 12.22/4.97  %Background operators:
% 12.22/4.97  
% 12.22/4.97  
% 12.22/4.97  %Foreground operators:
% 12.22/4.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.22/4.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.22/4.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.22/4.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.22/4.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.22/4.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.22/4.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.22/4.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.22/4.97  tff('#skF_2', type, '#skF_2': $i).
% 12.22/4.97  tff('#skF_3', type, '#skF_3': $i).
% 12.22/4.97  tff('#skF_1', type, '#skF_1': $i).
% 12.22/4.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.22/4.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.22/4.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.22/4.97  tff('#skF_4', type, '#skF_4': $i).
% 12.22/4.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.22/4.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.22/4.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.22/4.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.22/4.97  
% 12.22/4.99  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 12.22/4.99  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 12.22/4.99  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 12.22/4.99  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 12.22/4.99  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 12.22/4.99  tff(f_55, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 12.22/4.99  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 12.22/4.99  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.22/4.99  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 12.22/4.99  tff(f_57, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 12.22/4.99  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 12.22/4.99  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 12.22/4.99  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 12.22/4.99  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 12.22/4.99  tff(c_8, plain, (![A_8, C_10, D_11, B_9]: (k2_enumset1(A_8, C_10, D_11, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.22/4.99  tff(c_26, plain, (![A_57, B_58, C_59, D_60]: (k3_enumset1(A_57, A_57, B_58, C_59, D_60)=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.22/4.99  tff(c_22, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.22/4.99  tff(c_28, plain, (![A_61, B_62, E_65, C_63, D_64]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, E_65)=k3_enumset1(A_61, B_62, C_63, D_64, E_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.22/4.99  tff(c_24, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.22/4.99  tff(c_30, plain, (![B_67, A_66, F_71, C_68, E_70, D_69]: (k5_enumset1(A_66, A_66, B_67, C_68, D_69, E_70, F_71)=k4_enumset1(A_66, B_67, C_68, D_69, E_70, F_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.22/4.99  tff(c_375, plain, (![B_129, A_130, D_132, C_134, E_131, G_128, F_133]: (k2_xboole_0(k3_enumset1(A_130, B_129, C_134, D_132, E_131), k2_tarski(F_133, G_128))=k5_enumset1(A_130, B_129, C_134, D_132, E_131, F_133, G_128))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.22/4.99  tff(c_384, plain, (![A_57, B_58, G_128, F_133, D_60, C_59]: (k5_enumset1(A_57, A_57, B_58, C_59, D_60, F_133, G_128)=k2_xboole_0(k2_enumset1(A_57, B_58, C_59, D_60), k2_tarski(F_133, G_128)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_375])).
% 12.22/4.99  tff(c_419, plain, (![C_148, B_144, G_145, D_147, F_143, A_146]: (k2_xboole_0(k2_enumset1(A_146, B_144, C_148, D_147), k2_tarski(F_143, G_145))=k4_enumset1(A_146, B_144, C_148, D_147, F_143, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_384])).
% 12.22/4.99  tff(c_440, plain, (![C_56, G_145, F_143, B_55, A_54]: (k4_enumset1(A_54, A_54, B_55, C_56, F_143, G_145)=k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k2_tarski(F_143, G_145)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_419])).
% 12.22/4.99  tff(c_447, plain, (![F_149, B_152, G_153, C_150, A_151]: (k2_xboole_0(k1_enumset1(A_151, B_152, C_150), k2_tarski(F_149, G_153))=k3_enumset1(A_151, B_152, C_150, F_149, G_153))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_440])).
% 12.22/4.99  tff(c_468, plain, (![A_52, B_53, F_149, G_153]: (k3_enumset1(A_52, A_52, B_53, F_149, G_153)=k2_xboole_0(k2_tarski(A_52, B_53), k2_tarski(F_149, G_153)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_447])).
% 12.22/4.99  tff(c_474, plain, (![A_52, B_53, F_149, G_153]: (k2_xboole_0(k2_tarski(A_52, B_53), k2_tarski(F_149, G_153))=k2_enumset1(A_52, B_53, F_149, G_153))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_468])).
% 12.22/4.99  tff(c_20, plain, (![A_51]: (k2_tarski(A_51, A_51)=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.22/4.99  tff(c_475, plain, (![A_154, B_155, F_156, G_157]: (k2_xboole_0(k2_tarski(A_154, B_155), k2_tarski(F_156, G_157))=k2_enumset1(A_154, B_155, F_156, G_157))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_468])).
% 12.22/4.99  tff(c_526, plain, (![A_171, B_172, A_173]: (k2_xboole_0(k2_tarski(A_171, B_172), k1_tarski(A_173))=k2_enumset1(A_171, B_172, A_173, A_173))), inference(superposition, [status(thm), theory('equality')], [c_20, c_475])).
% 12.22/4.99  tff(c_984, plain, (![A_207, B_208, A_209]: (k2_xboole_0(k2_tarski(A_207, B_208), k1_tarski(A_209))=k2_enumset1(A_207, A_209, A_209, B_208))), inference(superposition, [status(thm), theory('equality')], [c_526, c_8])).
% 12.22/4.99  tff(c_72, plain, (![B_86, C_87, A_88]: (k1_enumset1(B_86, C_87, A_88)=k1_enumset1(A_88, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.99  tff(c_88, plain, (![B_86, C_87]: (k1_enumset1(B_86, C_87, B_86)=k2_tarski(B_86, C_87))), inference(superposition, [status(thm), theory('equality')], [c_72, c_22])).
% 12.22/4.99  tff(c_210, plain, (![A_96, C_97, D_98, B_99]: (k2_enumset1(A_96, C_97, D_98, B_99)=k2_enumset1(A_96, B_99, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.22/4.99  tff(c_226, plain, (![B_99, C_97, D_98]: (k2_enumset1(B_99, C_97, D_98, B_99)=k1_enumset1(B_99, C_97, D_98))), inference(superposition, [status(thm), theory('equality')], [c_210, c_24])).
% 12.22/4.99  tff(c_543, plain, (![A_173, B_172]: (k2_xboole_0(k2_tarski(A_173, B_172), k1_tarski(A_173))=k1_enumset1(A_173, B_172, A_173))), inference(superposition, [status(thm), theory('equality')], [c_526, c_226])).
% 12.22/4.99  tff(c_586, plain, (![A_173, B_172]: (k2_xboole_0(k2_tarski(A_173, B_172), k1_tarski(A_173))=k2_tarski(A_173, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_543])).
% 12.22/4.99  tff(c_1209, plain, (![A_212, B_213]: (k2_enumset1(A_212, A_212, A_212, B_213)=k2_tarski(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_984, c_586])).
% 12.22/4.99  tff(c_1326, plain, (![C_214, D_215]: (k2_enumset1(C_214, C_214, D_215, C_214)=k2_tarski(C_214, D_215))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1209])).
% 12.22/4.99  tff(c_390, plain, (![A_57, B_58, G_128, F_133, D_60, C_59]: (k2_xboole_0(k2_enumset1(A_57, B_58, C_59, D_60), k2_tarski(F_133, G_128))=k4_enumset1(A_57, B_58, C_59, D_60, F_133, G_128))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_384])).
% 12.22/4.99  tff(c_1360, plain, (![C_214, D_215, F_133, G_128]: (k4_enumset1(C_214, C_214, D_215, C_214, F_133, G_128)=k2_xboole_0(k2_tarski(C_214, D_215), k2_tarski(F_133, G_128)))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_390])).
% 12.22/4.99  tff(c_5293, plain, (![C_353, D_354, F_355, G_356]: (k4_enumset1(C_353, C_353, D_354, C_353, F_355, G_356)=k2_enumset1(C_353, D_354, F_355, G_356))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_1360])).
% 12.22/4.99  tff(c_5329, plain, (![C_353, D_354, F_355, G_356]: (k3_enumset1(C_353, D_354, C_353, F_355, G_356)=k2_enumset1(C_353, D_354, F_355, G_356))), inference(superposition, [status(thm), theory('equality')], [c_5293, c_28])).
% 12.22/4.99  tff(c_107, plain, (![B_53, A_52]: (k1_enumset1(B_53, A_52, A_52)=k2_tarski(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_22, c_72])).
% 12.22/4.99  tff(c_484, plain, (![A_51, F_156, G_157]: (k2_xboole_0(k1_tarski(A_51), k2_tarski(F_156, G_157))=k2_enumset1(A_51, A_51, F_156, G_157))), inference(superposition, [status(thm), theory('equality')], [c_20, c_475])).
% 12.22/4.99  tff(c_504, plain, (![A_166, F_167, G_168]: (k2_xboole_0(k1_tarski(A_166), k2_tarski(F_167, G_168))=k1_enumset1(A_166, F_167, G_168))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_484])).
% 12.22/4.99  tff(c_513, plain, (![A_166, A_51]: (k2_xboole_0(k1_tarski(A_166), k1_tarski(A_51))=k1_enumset1(A_166, A_51, A_51))), inference(superposition, [status(thm), theory('equality')], [c_20, c_504])).
% 12.22/4.99  tff(c_516, plain, (![A_166, A_51]: (k2_xboole_0(k1_tarski(A_166), k1_tarski(A_51))=k2_tarski(A_51, A_166))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_513])).
% 12.22/4.99  tff(c_7721, plain, (![D_427, C_428, A_425, A_429, B_426]: (k4_enumset1(A_429, B_426, C_428, D_427, A_425, A_425)=k2_xboole_0(k2_enumset1(A_429, B_426, C_428, D_427), k1_tarski(A_425)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_419])).
% 12.22/4.99  tff(c_8022, plain, (![A_435, B_436, C_437, A_438]: (k4_enumset1(A_435, A_435, B_436, C_437, A_438, A_438)=k2_xboole_0(k1_enumset1(A_435, B_436, C_437), k1_tarski(A_438)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7721])).
% 12.22/4.99  tff(c_15042, plain, (![A_537, B_538, A_539]: (k4_enumset1(A_537, A_537, A_537, B_538, A_539, A_539)=k2_xboole_0(k2_tarski(A_537, B_538), k1_tarski(A_539)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8022])).
% 12.22/4.99  tff(c_15279, plain, (![A_540, B_541]: (k4_enumset1(A_540, A_540, A_540, B_541, A_540, A_540)=k2_tarski(A_540, B_541))), inference(superposition, [status(thm), theory('equality')], [c_15042, c_586])).
% 12.22/4.99  tff(c_446, plain, (![C_56, G_145, F_143, B_55, A_54]: (k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k2_tarski(F_143, G_145))=k3_enumset1(A_54, B_55, C_56, F_143, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_440])).
% 12.22/4.99  tff(c_431, plain, (![G_145, B_99, C_97, F_143, D_98]: (k4_enumset1(B_99, C_97, D_98, B_99, F_143, G_145)=k2_xboole_0(k1_enumset1(B_99, C_97, D_98), k2_tarski(F_143, G_145)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_419])).
% 12.22/4.99  tff(c_11110, plain, (![G_145, B_99, C_97, F_143, D_98]: (k4_enumset1(B_99, C_97, D_98, B_99, F_143, G_145)=k3_enumset1(B_99, C_97, D_98, F_143, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_431])).
% 12.22/4.99  tff(c_15292, plain, (![B_541]: (k3_enumset1(B_541, B_541, B_541, B_541, B_541)=k2_tarski(B_541, B_541))), inference(superposition, [status(thm), theory('equality')], [c_15279, c_11110])).
% 12.22/4.99  tff(c_15409, plain, (![B_541]: (k3_enumset1(B_541, B_541, B_541, B_541, B_541)=k1_tarski(B_541))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_15292])).
% 12.22/4.99  tff(c_32, plain, (![B_73, G_78, C_74, E_76, A_72, D_75, F_77]: (k6_enumset1(A_72, A_72, B_73, C_74, D_75, E_76, F_77, G_78)=k5_enumset1(A_72, B_73, C_74, D_75, E_76, F_77, G_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.22/4.99  tff(c_491, plain, (![A_163, E_165, C_159, D_161, F_162, H_160, B_164, G_158]: (k2_xboole_0(k5_enumset1(A_163, B_164, C_159, D_161, E_165, F_162, G_158), k1_tarski(H_160))=k6_enumset1(A_163, B_164, C_159, D_161, E_165, F_162, G_158, H_160))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.22/4.99  tff(c_500, plain, (![B_67, A_66, F_71, C_68, E_70, H_160, D_69]: (k6_enumset1(A_66, A_66, B_67, C_68, D_69, E_70, F_71, H_160)=k2_xboole_0(k4_enumset1(A_66, B_67, C_68, D_69, E_70, F_71), k1_tarski(H_160)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_491])).
% 12.22/4.99  tff(c_503, plain, (![B_67, A_66, F_71, C_68, E_70, H_160, D_69]: (k2_xboole_0(k4_enumset1(A_66, B_67, C_68, D_69, E_70, F_71), k1_tarski(H_160))=k5_enumset1(A_66, B_67, C_68, D_69, E_70, F_71, H_160))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_500])).
% 12.22/4.99  tff(c_702, plain, (![D_183, C_181, A_177, F_180, G_179, H_178, B_184, E_182]: (k2_xboole_0(k4_enumset1(A_177, B_184, C_181, D_183, E_182, F_180), k2_tarski(G_179, H_178))=k6_enumset1(A_177, B_184, C_181, D_183, E_182, F_180, G_179, H_178))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.22/4.99  tff(c_714, plain, (![D_183, C_181, A_177, F_180, A_51, B_184, E_182]: (k6_enumset1(A_177, B_184, C_181, D_183, E_182, F_180, A_51, A_51)=k2_xboole_0(k4_enumset1(A_177, B_184, C_181, D_183, E_182, F_180), k1_tarski(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_702])).
% 12.22/4.99  tff(c_3253, plain, (![E_305, D_303, F_304, C_307, A_306, A_302, B_308]: (k6_enumset1(A_306, B_308, C_307, D_303, E_305, F_304, A_302, A_302)=k5_enumset1(A_306, B_308, C_307, D_303, E_305, F_304, A_302))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_714])).
% 12.22/4.99  tff(c_3264, plain, (![E_305, D_303, F_304, C_307, A_302, B_308]: (k5_enumset1(B_308, C_307, D_303, E_305, F_304, A_302, A_302)=k5_enumset1(B_308, B_308, C_307, D_303, E_305, F_304, A_302))), inference(superposition, [status(thm), theory('equality')], [c_3253, c_32])).
% 12.22/4.99  tff(c_3278, plain, (![E_305, D_303, F_304, C_307, A_302, B_308]: (k5_enumset1(B_308, C_307, D_303, E_305, F_304, A_302, A_302)=k4_enumset1(B_308, C_307, D_303, E_305, F_304, A_302))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3264])).
% 12.22/4.99  tff(c_387, plain, (![B_129, A_130, D_132, C_134, E_131, A_51]: (k5_enumset1(A_130, B_129, C_134, D_132, E_131, A_51, A_51)=k2_xboole_0(k3_enumset1(A_130, B_129, C_134, D_132, E_131), k1_tarski(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_375])).
% 12.22/4.99  tff(c_17108, plain, (![C_572, B_573, A_569, E_570, A_571, D_574]: (k2_xboole_0(k3_enumset1(A_569, B_573, C_572, D_574, E_570), k1_tarski(A_571))=k4_enumset1(A_569, B_573, C_572, D_574, E_570, A_571))), inference(demodulation, [status(thm), theory('equality')], [c_3278, c_387])).
% 12.22/4.99  tff(c_17117, plain, (![B_541, A_571]: (k4_enumset1(B_541, B_541, B_541, B_541, B_541, A_571)=k2_xboole_0(k1_tarski(B_541), k1_tarski(A_571)))), inference(superposition, [status(thm), theory('equality')], [c_15409, c_17108])).
% 12.22/4.99  tff(c_17236, plain, (![B_575, A_576]: (k4_enumset1(B_575, B_575, B_575, B_575, B_575, A_576)=k2_tarski(A_576, B_575))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_17117])).
% 12.22/4.99  tff(c_490, plain, (![A_51, F_156, G_157]: (k2_xboole_0(k1_tarski(A_51), k2_tarski(F_156, G_157))=k1_enumset1(A_51, F_156, G_157))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_484])).
% 12.22/4.99  tff(c_2044, plain, (![A_266, B_267, C_268, A_269]: (k3_enumset1(A_266, B_267, C_268, A_269, A_269)=k2_xboole_0(k1_enumset1(A_266, B_267, C_268), k1_tarski(A_269)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_447])).
% 12.22/4.99  tff(c_2188, plain, (![B_272, A_273, A_274]: (k3_enumset1(B_272, A_273, A_273, A_274, A_274)=k2_xboole_0(k2_tarski(A_273, B_272), k1_tarski(A_274)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_2044])).
% 12.22/4.99  tff(c_2296, plain, (![B_275, A_276]: (k3_enumset1(B_275, A_276, A_276, A_276, A_276)=k2_tarski(A_276, B_275))), inference(superposition, [status(thm), theory('equality')], [c_2188, c_586])).
% 12.22/4.99  tff(c_2335, plain, (![A_276]: (k2_enumset1(A_276, A_276, A_276, A_276)=k2_tarski(A_276, A_276))), inference(superposition, [status(thm), theory('equality')], [c_2296, c_26])).
% 12.22/4.99  tff(c_2380, plain, (![A_277]: (k2_enumset1(A_277, A_277, A_277, A_277)=k1_tarski(A_277))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2335])).
% 12.22/4.99  tff(c_2416, plain, (![A_277, F_133, G_128]: (k4_enumset1(A_277, A_277, A_277, A_277, F_133, G_128)=k2_xboole_0(k1_tarski(A_277), k2_tarski(F_133, G_128)))), inference(superposition, [status(thm), theory('equality')], [c_2380, c_390])).
% 12.22/4.99  tff(c_2487, plain, (![A_277, F_133, G_128]: (k4_enumset1(A_277, A_277, A_277, A_277, F_133, G_128)=k1_enumset1(A_277, F_133, G_128))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_2416])).
% 12.22/4.99  tff(c_17432, plain, (![B_577, A_578]: (k1_enumset1(B_577, B_577, A_578)=k2_tarski(A_578, B_577))), inference(superposition, [status(thm), theory('equality')], [c_17236, c_2487])).
% 12.22/4.99  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.99  tff(c_465, plain, (![B_6, C_7, F_149, G_153, A_5]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k2_tarski(F_149, G_153))=k3_enumset1(B_6, C_7, A_5, F_149, G_153))), inference(superposition, [status(thm), theory('equality')], [c_6, c_447])).
% 12.22/4.99  tff(c_17471, plain, (![B_577, A_578, F_149, G_153]: (k3_enumset1(B_577, A_578, B_577, F_149, G_153)=k2_xboole_0(k2_tarski(A_578, B_577), k2_tarski(F_149, G_153)))), inference(superposition, [status(thm), theory('equality')], [c_17432, c_465])).
% 12.22/4.99  tff(c_17570, plain, (![B_577, A_578, F_149, G_153]: (k2_enumset1(B_577, A_578, F_149, G_153)=k2_enumset1(A_578, B_577, F_149, G_153))), inference(demodulation, [status(thm), theory('equality')], [c_5329, c_474, c_17471])).
% 12.22/4.99  tff(c_3252, plain, (![D_183, C_181, A_177, F_180, A_51, B_184, E_182]: (k6_enumset1(A_177, B_184, C_181, D_183, E_182, F_180, A_51, A_51)=k5_enumset1(A_177, B_184, C_181, D_183, E_182, F_180, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_714])).
% 12.22/4.99  tff(c_10, plain, (![E_16, D_15, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k3_enumset1(A_12, B_13, C_14, D_15, E_16), k2_tarski(F_17, G_18))=k5_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.22/4.99  tff(c_721, plain, (![H_187, F_185, D_188, B_190, A_192, E_189, C_186, G_191]: (k2_xboole_0(k3_enumset1(A_192, B_190, C_186, D_188, E_189), k1_enumset1(F_185, G_191, H_187))=k6_enumset1(A_192, B_190, C_186, D_188, E_189, F_185, G_191, H_187))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.22/4.99  tff(c_6775, plain, (![C_405, B_407, C_409, A_410, E_408, A_411, D_412, B_406]: (k2_xboole_0(k3_enumset1(A_411, B_407, C_405, D_412, E_408), k1_enumset1(B_406, C_409, A_410))=k6_enumset1(A_411, B_407, C_405, D_412, E_408, A_410, B_406, C_409))), inference(superposition, [status(thm), theory('equality')], [c_6, c_721])).
% 12.22/4.99  tff(c_6877, plain, (![C_405, B_53, B_407, E_408, A_52, A_411, D_412]: (k6_enumset1(A_411, B_407, C_405, D_412, E_408, B_53, A_52, A_52)=k2_xboole_0(k3_enumset1(A_411, B_407, C_405, D_412, E_408), k2_tarski(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6775])).
% 12.22/4.99  tff(c_14950, plain, (![D_533, E_532, C_536, A_530, A_535, B_531, B_534]: (k5_enumset1(A_535, B_534, C_536, D_533, E_532, B_531, A_530)=k5_enumset1(A_535, B_534, C_536, D_533, E_532, A_530, B_531))), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_10, c_6877])).
% 12.22/4.99  tff(c_22120, plain, (![B_653, F_651, D_655, A_650, E_652, C_654]: (k5_enumset1(A_650, A_650, B_653, C_654, D_655, F_651, E_652)=k4_enumset1(A_650, B_653, C_654, D_655, E_652, F_651))), inference(superposition, [status(thm), theory('equality')], [c_30, c_14950])).
% 12.22/4.99  tff(c_23502, plain, (![D_667, C_666, F_663, B_665, A_662, E_664]: (k4_enumset1(A_662, B_665, C_666, D_667, F_663, E_664)=k4_enumset1(A_662, B_665, C_666, D_667, E_664, F_663))), inference(superposition, [status(thm), theory('equality')], [c_30, c_22120])).
% 12.22/4.99  tff(c_24146, plain, (![C_670, E_674, F_671, D_673, B_672]: (k4_enumset1(B_672, B_672, C_670, D_673, E_674, F_671)=k3_enumset1(B_672, C_670, D_673, F_671, E_674))), inference(superposition, [status(thm), theory('equality')], [c_23502, c_28])).
% 12.22/4.99  tff(c_24885, plain, (![D_684, F_687, B_688, E_685, C_686]: (k3_enumset1(B_688, C_686, D_684, F_687, E_685)=k3_enumset1(B_688, C_686, D_684, E_685, F_687))), inference(superposition, [status(thm), theory('equality')], [c_24146, c_28])).
% 12.22/4.99  tff(c_25169, plain, (![A_696, B_697, D_698, C_699]: (k3_enumset1(A_696, A_696, B_697, D_698, C_699)=k2_enumset1(A_696, B_697, C_699, D_698))), inference(superposition, [status(thm), theory('equality')], [c_26, c_24885])).
% 12.22/4.99  tff(c_25377, plain, (![A_696, B_697, D_698, C_699]: (k2_enumset1(A_696, B_697, D_698, C_699)=k2_enumset1(A_696, B_697, C_699, D_698))), inference(superposition, [status(thm), theory('equality')], [c_25169, c_26])).
% 12.22/4.99  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.22/4.99  tff(c_35, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_34])).
% 12.22/4.99  tff(c_26720, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25377, c_35])).
% 12.22/4.99  tff(c_29787, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17570, c_17570, c_26720])).
% 12.22/4.99  tff(c_29790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_29787])).
% 12.22/4.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.22/4.99  
% 12.22/4.99  Inference rules
% 12.22/4.99  ----------------------
% 12.22/4.99  #Ref     : 0
% 12.22/4.99  #Sup     : 6982
% 12.22/4.99  #Fact    : 0
% 12.22/4.99  #Define  : 0
% 12.22/4.99  #Split   : 0
% 12.22/4.99  #Chain   : 0
% 12.22/4.99  #Close   : 0
% 12.22/4.99  
% 12.22/4.99  Ordering : KBO
% 12.22/4.99  
% 12.22/4.99  Simplification rules
% 12.22/4.99  ----------------------
% 12.22/4.99  #Subsume      : 999
% 12.22/4.99  #Demod        : 8722
% 12.22/4.99  #Tautology    : 4354
% 12.22/4.99  #SimpNegUnit  : 0
% 12.22/4.99  #BackRed      : 3
% 12.22/4.99  
% 12.22/4.99  #Partial instantiations: 0
% 12.22/4.99  #Strategies tried      : 1
% 12.22/4.99  
% 12.22/4.99  Timing (in seconds)
% 12.22/4.99  ----------------------
% 12.22/5.00  Preprocessing        : 0.41
% 12.22/5.00  Parsing              : 0.24
% 12.22/5.00  CNF conversion       : 0.02
% 12.22/5.00  Main loop            : 3.80
% 12.22/5.00  Inferencing          : 1.00
% 12.22/5.00  Reduction            : 2.12
% 12.22/5.00  Demodulation         : 1.92
% 12.22/5.00  BG Simplification    : 0.11
% 12.22/5.00  Subsumption          : 0.42
% 12.22/5.00  Abstraction          : 0.19
% 12.22/5.00  MUC search           : 0.00
% 12.22/5.00  Cooper               : 0.00
% 12.22/5.00  Total                : 4.26
% 12.22/5.00  Index Insertion      : 0.00
% 12.22/5.00  Index Deletion       : 0.00
% 12.22/5.00  Index Matching       : 0.00
% 12.22/5.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

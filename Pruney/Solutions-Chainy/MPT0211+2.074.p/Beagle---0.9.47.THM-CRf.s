%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 234 expanded)
%              Number of leaves         :   30 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :   57 ( 216 expanded)
%              Number of equality atoms :   56 ( 215 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_55,C_57,B_56] : k1_enumset1(A_55,C_57,B_56) = k1_enumset1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : k5_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47) = k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : k6_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53,G_54) = k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_593,plain,(
    ! [A_110,F_112,H_108,B_109,C_106,D_113,G_111,E_107] : k2_xboole_0(k5_enumset1(A_110,B_109,C_106,D_113,E_107,F_112,G_111),k1_tarski(H_108)) = k6_enumset1(A_110,B_109,C_106,D_113,E_107,F_112,G_111,H_108) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_602,plain,(
    ! [B_43,A_42,H_108,D_45,E_46,C_44,F_47] : k6_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47,H_108) = k2_xboole_0(k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47),k1_tarski(H_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_593])).

tff(c_606,plain,(
    ! [D_115,A_117,H_118,B_116,C_120,F_119,E_114] : k2_xboole_0(k4_enumset1(A_117,B_116,C_120,D_115,E_114,F_119),k1_tarski(H_118)) = k5_enumset1(A_117,B_116,C_120,D_115,E_114,F_119,H_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_602])).

tff(c_615,plain,(
    ! [C_39,B_38,A_37,D_40,H_118,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,H_118) = k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k1_tarski(H_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_606])).

tff(c_636,plain,(
    ! [A_130,E_133,B_131,D_132,H_129,C_134] : k2_xboole_0(k3_enumset1(A_130,B_131,C_134,D_132,E_133),k1_tarski(H_129)) = k4_enumset1(A_130,B_131,C_134,D_132,E_133,H_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_615])).

tff(c_645,plain,(
    ! [D_36,H_129,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,H_129) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(H_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_636])).

tff(c_649,plain,(
    ! [C_136,D_137,H_138,B_139,A_135] : k2_xboole_0(k2_enumset1(A_135,B_139,C_136,D_137),k1_tarski(H_138)) = k3_enumset1(A_135,B_139,C_136,D_137,H_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_645])).

tff(c_658,plain,(
    ! [A_30,B_31,C_32,H_138] : k3_enumset1(A_30,A_30,B_31,C_32,H_138) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(H_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_649])).

tff(c_662,plain,(
    ! [A_140,B_141,C_142,H_143] : k2_xboole_0(k1_enumset1(A_140,B_141,C_142),k1_tarski(H_143)) = k2_enumset1(A_140,B_141,C_142,H_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_658])).

tff(c_705,plain,(
    ! [A_144,C_145,B_146,H_147] : k2_xboole_0(k1_enumset1(A_144,C_145,B_146),k1_tarski(H_147)) = k2_enumset1(A_144,B_146,C_145,H_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_662])).

tff(c_661,plain,(
    ! [A_30,B_31,C_32,H_138] : k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(H_138)) = k2_enumset1(A_30,B_31,C_32,H_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_658])).

tff(c_711,plain,(
    ! [A_144,C_145,B_146,H_147] : k2_enumset1(A_144,C_145,B_146,H_147) = k2_enumset1(A_144,B_146,C_145,H_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_661])).

tff(c_16,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_619,plain,(
    ! [H_128,E_127,A_124,B_125,G_123,D_126,C_122,F_121] : k2_xboole_0(k4_enumset1(A_124,B_125,C_122,D_126,E_127,F_121),k2_tarski(G_123,H_128)) = k6_enumset1(A_124,B_125,C_122,D_126,E_127,F_121,G_123,H_128) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_628,plain,(
    ! [H_128,C_39,B_38,G_123,A_37,D_40,E_41] : k6_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,G_123,H_128) = k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k2_tarski(G_123,H_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_619])).

tff(c_955,plain,(
    ! [D_177,H_179,E_178,C_180,A_175,G_174,B_176] : k2_xboole_0(k3_enumset1(A_175,B_176,C_180,D_177,E_178),k2_tarski(G_174,H_179)) = k5_enumset1(A_175,B_176,C_180,D_177,E_178,G_174,H_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_628])).

tff(c_967,plain,(
    ! [D_36,H_179,A_33,B_34,G_174,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,G_174,H_179) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k2_tarski(G_174,H_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_955])).

tff(c_1716,plain,(
    ! [D_221,C_220,G_222,H_224,A_219,B_223] : k2_xboole_0(k2_enumset1(A_219,B_223,C_220,D_221),k2_tarski(G_222,H_224)) = k4_enumset1(A_219,B_223,C_220,D_221,G_222,H_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_967])).

tff(c_1755,plain,(
    ! [A_30,C_32,B_31,G_222,H_224] : k4_enumset1(A_30,A_30,B_31,C_32,G_222,H_224) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k2_tarski(G_222,H_224)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1716])).

tff(c_2745,plain,(
    ! [H_262,C_263,A_266,B_264,G_265] : k2_xboole_0(k1_enumset1(A_266,B_264,C_263),k2_tarski(G_265,H_262)) = k3_enumset1(A_266,B_264,C_263,G_265,H_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1755])).

tff(c_2790,plain,(
    ! [A_28,B_29,G_265,H_262] : k3_enumset1(A_28,A_28,B_29,G_265,H_262) = k2_xboole_0(k2_tarski(A_28,B_29),k2_tarski(G_265,H_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2745])).

tff(c_2798,plain,(
    ! [A_28,B_29,G_265,H_262] : k2_xboole_0(k2_tarski(A_28,B_29),k2_tarski(G_265,H_262)) = k2_enumset1(A_28,B_29,G_265,H_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2790])).

tff(c_143,plain,(
    ! [B_68,C_69,A_70] : k1_enumset1(B_68,C_69,A_70) = k1_enumset1(A_70,B_68,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_70,C_69] : k1_enumset1(A_70,C_69,C_69) = k2_tarski(C_69,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_16])).

tff(c_648,plain,(
    ! [D_36,H_129,A_33,B_34,C_35] : k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(H_129)) = k3_enumset1(A_33,B_34,C_35,D_36,H_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_645])).

tff(c_14,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1758,plain,(
    ! [D_221,A_27,C_220,A_219,B_223] : k4_enumset1(A_219,B_223,C_220,D_221,A_27,A_27) = k2_xboole_0(k2_enumset1(A_219,B_223,C_220,D_221),k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1716])).

tff(c_1771,plain,(
    ! [D_227,C_226,A_225,A_229,B_228] : k4_enumset1(A_225,B_228,C_226,D_227,A_229,A_229) = k3_enumset1(A_225,B_228,C_226,D_227,A_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1758])).

tff(c_1784,plain,(
    ! [B_228,C_226,D_227,A_229] : k3_enumset1(B_228,C_226,D_227,A_229,A_229) = k3_enumset1(B_228,B_228,C_226,D_227,A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_22])).

tff(c_1799,plain,(
    ! [B_230,C_231,D_232,A_233] : k3_enumset1(B_230,C_231,D_232,A_233,A_233) = k2_enumset1(B_230,C_231,D_232,A_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1784])).

tff(c_1820,plain,(
    ! [C_231,D_232,A_233] : k2_enumset1(C_231,D_232,A_233,A_233) = k2_enumset1(C_231,C_231,D_232,A_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_20])).

tff(c_1846,plain,(
    ! [C_234,D_235,A_236] : k2_enumset1(C_234,D_235,A_236,A_236) = k1_enumset1(C_234,D_235,A_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1820])).

tff(c_1891,plain,(
    ! [D_235,A_236] : k1_enumset1(D_235,D_235,A_236) = k1_enumset1(D_235,A_236,A_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_18])).

tff(c_1943,plain,(
    ! [D_235,A_236] : k2_tarski(D_235,A_236) = k2_tarski(A_236,D_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_16,c_1891])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_1948,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1943,c_1943,c_31])).

tff(c_3064,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_1948])).

tff(c_3067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18,c_711,c_3064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.78  
% 4.27/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.78  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 4.27/1.78  
% 4.27/1.78  %Foreground sorts:
% 4.27/1.78  
% 4.27/1.78  
% 4.27/1.78  %Background operators:
% 4.27/1.78  
% 4.27/1.78  
% 4.27/1.78  %Foreground operators:
% 4.27/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.27/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.27/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.27/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.27/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.27/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.27/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.27/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.27/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.78  
% 4.60/1.80  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 4.60/1.80  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.60/1.80  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.60/1.80  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.60/1.80  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.60/1.80  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.60/1.80  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 4.60/1.80  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.60/1.80  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 4.60/1.80  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 4.60/1.80  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.60/1.80  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 4.60/1.80  tff(c_28, plain, (![A_55, C_57, B_56]: (k1_enumset1(A_55, C_57, B_56)=k1_enumset1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.60/1.80  tff(c_18, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.80  tff(c_20, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.60/1.80  tff(c_22, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.60/1.80  tff(c_24, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (k5_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47)=k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.80  tff(c_26, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (k6_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53, G_54)=k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.60/1.80  tff(c_593, plain, (![A_110, F_112, H_108, B_109, C_106, D_113, G_111, E_107]: (k2_xboole_0(k5_enumset1(A_110, B_109, C_106, D_113, E_107, F_112, G_111), k1_tarski(H_108))=k6_enumset1(A_110, B_109, C_106, D_113, E_107, F_112, G_111, H_108))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.80  tff(c_602, plain, (![B_43, A_42, H_108, D_45, E_46, C_44, F_47]: (k6_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47, H_108)=k2_xboole_0(k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47), k1_tarski(H_108)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_593])).
% 4.60/1.80  tff(c_606, plain, (![D_115, A_117, H_118, B_116, C_120, F_119, E_114]: (k2_xboole_0(k4_enumset1(A_117, B_116, C_120, D_115, E_114, F_119), k1_tarski(H_118))=k5_enumset1(A_117, B_116, C_120, D_115, E_114, F_119, H_118))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_602])).
% 4.60/1.80  tff(c_615, plain, (![C_39, B_38, A_37, D_40, H_118, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, H_118)=k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k1_tarski(H_118)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_606])).
% 4.60/1.80  tff(c_636, plain, (![A_130, E_133, B_131, D_132, H_129, C_134]: (k2_xboole_0(k3_enumset1(A_130, B_131, C_134, D_132, E_133), k1_tarski(H_129))=k4_enumset1(A_130, B_131, C_134, D_132, E_133, H_129))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_615])).
% 4.60/1.80  tff(c_645, plain, (![D_36, H_129, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, H_129)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(H_129)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_636])).
% 4.60/1.80  tff(c_649, plain, (![C_136, D_137, H_138, B_139, A_135]: (k2_xboole_0(k2_enumset1(A_135, B_139, C_136, D_137), k1_tarski(H_138))=k3_enumset1(A_135, B_139, C_136, D_137, H_138))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_645])).
% 4.60/1.80  tff(c_658, plain, (![A_30, B_31, C_32, H_138]: (k3_enumset1(A_30, A_30, B_31, C_32, H_138)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(H_138)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_649])).
% 4.60/1.80  tff(c_662, plain, (![A_140, B_141, C_142, H_143]: (k2_xboole_0(k1_enumset1(A_140, B_141, C_142), k1_tarski(H_143))=k2_enumset1(A_140, B_141, C_142, H_143))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_658])).
% 4.60/1.80  tff(c_705, plain, (![A_144, C_145, B_146, H_147]: (k2_xboole_0(k1_enumset1(A_144, C_145, B_146), k1_tarski(H_147))=k2_enumset1(A_144, B_146, C_145, H_147))), inference(superposition, [status(thm), theory('equality')], [c_28, c_662])).
% 4.60/1.80  tff(c_661, plain, (![A_30, B_31, C_32, H_138]: (k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(H_138))=k2_enumset1(A_30, B_31, C_32, H_138))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_658])).
% 4.60/1.80  tff(c_711, plain, (![A_144, C_145, B_146, H_147]: (k2_enumset1(A_144, C_145, B_146, H_147)=k2_enumset1(A_144, B_146, C_145, H_147))), inference(superposition, [status(thm), theory('equality')], [c_705, c_661])).
% 4.60/1.80  tff(c_16, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.80  tff(c_619, plain, (![H_128, E_127, A_124, B_125, G_123, D_126, C_122, F_121]: (k2_xboole_0(k4_enumset1(A_124, B_125, C_122, D_126, E_127, F_121), k2_tarski(G_123, H_128))=k6_enumset1(A_124, B_125, C_122, D_126, E_127, F_121, G_123, H_128))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.80  tff(c_628, plain, (![H_128, C_39, B_38, G_123, A_37, D_40, E_41]: (k6_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, G_123, H_128)=k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k2_tarski(G_123, H_128)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_619])).
% 4.60/1.80  tff(c_955, plain, (![D_177, H_179, E_178, C_180, A_175, G_174, B_176]: (k2_xboole_0(k3_enumset1(A_175, B_176, C_180, D_177, E_178), k2_tarski(G_174, H_179))=k5_enumset1(A_175, B_176, C_180, D_177, E_178, G_174, H_179))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_628])).
% 4.60/1.80  tff(c_967, plain, (![D_36, H_179, A_33, B_34, G_174, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, G_174, H_179)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k2_tarski(G_174, H_179)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_955])).
% 4.60/1.80  tff(c_1716, plain, (![D_221, C_220, G_222, H_224, A_219, B_223]: (k2_xboole_0(k2_enumset1(A_219, B_223, C_220, D_221), k2_tarski(G_222, H_224))=k4_enumset1(A_219, B_223, C_220, D_221, G_222, H_224))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_967])).
% 4.60/1.80  tff(c_1755, plain, (![A_30, C_32, B_31, G_222, H_224]: (k4_enumset1(A_30, A_30, B_31, C_32, G_222, H_224)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k2_tarski(G_222, H_224)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1716])).
% 4.60/1.80  tff(c_2745, plain, (![H_262, C_263, A_266, B_264, G_265]: (k2_xboole_0(k1_enumset1(A_266, B_264, C_263), k2_tarski(G_265, H_262))=k3_enumset1(A_266, B_264, C_263, G_265, H_262))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1755])).
% 4.60/1.80  tff(c_2790, plain, (![A_28, B_29, G_265, H_262]: (k3_enumset1(A_28, A_28, B_29, G_265, H_262)=k2_xboole_0(k2_tarski(A_28, B_29), k2_tarski(G_265, H_262)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2745])).
% 4.60/1.80  tff(c_2798, plain, (![A_28, B_29, G_265, H_262]: (k2_xboole_0(k2_tarski(A_28, B_29), k2_tarski(G_265, H_262))=k2_enumset1(A_28, B_29, G_265, H_262))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2790])).
% 4.60/1.80  tff(c_143, plain, (![B_68, C_69, A_70]: (k1_enumset1(B_68, C_69, A_70)=k1_enumset1(A_70, B_68, C_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.80  tff(c_183, plain, (![A_70, C_69]: (k1_enumset1(A_70, C_69, C_69)=k2_tarski(C_69, A_70))), inference(superposition, [status(thm), theory('equality')], [c_143, c_16])).
% 4.60/1.80  tff(c_648, plain, (![D_36, H_129, A_33, B_34, C_35]: (k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(H_129))=k3_enumset1(A_33, B_34, C_35, D_36, H_129))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_645])).
% 4.60/1.80  tff(c_14, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.80  tff(c_1758, plain, (![D_221, A_27, C_220, A_219, B_223]: (k4_enumset1(A_219, B_223, C_220, D_221, A_27, A_27)=k2_xboole_0(k2_enumset1(A_219, B_223, C_220, D_221), k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1716])).
% 4.60/1.80  tff(c_1771, plain, (![D_227, C_226, A_225, A_229, B_228]: (k4_enumset1(A_225, B_228, C_226, D_227, A_229, A_229)=k3_enumset1(A_225, B_228, C_226, D_227, A_229))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_1758])).
% 4.60/1.80  tff(c_1784, plain, (![B_228, C_226, D_227, A_229]: (k3_enumset1(B_228, C_226, D_227, A_229, A_229)=k3_enumset1(B_228, B_228, C_226, D_227, A_229))), inference(superposition, [status(thm), theory('equality')], [c_1771, c_22])).
% 4.60/1.80  tff(c_1799, plain, (![B_230, C_231, D_232, A_233]: (k3_enumset1(B_230, C_231, D_232, A_233, A_233)=k2_enumset1(B_230, C_231, D_232, A_233))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1784])).
% 4.60/1.80  tff(c_1820, plain, (![C_231, D_232, A_233]: (k2_enumset1(C_231, D_232, A_233, A_233)=k2_enumset1(C_231, C_231, D_232, A_233))), inference(superposition, [status(thm), theory('equality')], [c_1799, c_20])).
% 4.60/1.80  tff(c_1846, plain, (![C_234, D_235, A_236]: (k2_enumset1(C_234, D_235, A_236, A_236)=k1_enumset1(C_234, D_235, A_236))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1820])).
% 4.60/1.80  tff(c_1891, plain, (![D_235, A_236]: (k1_enumset1(D_235, D_235, A_236)=k1_enumset1(D_235, A_236, A_236))), inference(superposition, [status(thm), theory('equality')], [c_1846, c_18])).
% 4.60/1.80  tff(c_1943, plain, (![D_235, A_236]: (k2_tarski(D_235, A_236)=k2_tarski(A_236, D_235))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_16, c_1891])).
% 4.60/1.80  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.80  tff(c_31, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 4.60/1.80  tff(c_1948, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1943, c_1943, c_31])).
% 4.60/1.80  tff(c_3064, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_1948])).
% 4.60/1.80  tff(c_3067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_18, c_711, c_3064])).
% 4.60/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.80  
% 4.60/1.80  Inference rules
% 4.60/1.80  ----------------------
% 4.60/1.80  #Ref     : 0
% 4.60/1.80  #Sup     : 759
% 4.60/1.80  #Fact    : 0
% 4.60/1.80  #Define  : 0
% 4.60/1.80  #Split   : 0
% 4.60/1.80  #Chain   : 0
% 4.60/1.80  #Close   : 0
% 4.60/1.80  
% 4.60/1.80  Ordering : KBO
% 4.60/1.80  
% 4.60/1.80  Simplification rules
% 4.60/1.80  ----------------------
% 4.60/1.80  #Subsume      : 149
% 4.60/1.80  #Demod        : 473
% 4.60/1.80  #Tautology    : 449
% 4.60/1.80  #SimpNegUnit  : 0
% 4.60/1.80  #BackRed      : 2
% 4.60/1.80  
% 4.60/1.80  #Partial instantiations: 0
% 4.60/1.80  #Strategies tried      : 1
% 4.60/1.80  
% 4.60/1.80  Timing (in seconds)
% 4.60/1.80  ----------------------
% 4.60/1.80  Preprocessing        : 0.31
% 4.60/1.80  Parsing              : 0.17
% 4.60/1.80  CNF conversion       : 0.02
% 4.60/1.80  Main loop            : 0.73
% 4.60/1.80  Inferencing          : 0.25
% 4.60/1.80  Reduction            : 0.34
% 4.60/1.80  Demodulation         : 0.28
% 4.60/1.80  BG Simplification    : 0.03
% 4.60/1.80  Subsumption          : 0.08
% 4.60/1.80  Abstraction          : 0.05
% 4.60/1.80  MUC search           : 0.00
% 4.60/1.80  Cooper               : 0.00
% 4.60/1.80  Total                : 1.08
% 4.60/1.80  Index Insertion      : 0.00
% 4.60/1.80  Index Deletion       : 0.00
% 4.60/1.80  Index Matching       : 0.00
% 4.60/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------

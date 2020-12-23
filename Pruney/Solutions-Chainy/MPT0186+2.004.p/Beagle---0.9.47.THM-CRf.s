%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 227 expanded)
%              Number of leaves         :   31 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :   53 ( 208 expanded)
%              Number of equality atoms :   52 ( 207 expanded)
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

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_20,plain,(
    ! [A_39,B_40,C_41,D_42] : k3_enumset1(A_39,A_39,B_40,C_41,D_42) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k1_tarski(E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [B_49,F_53,A_48,D_51,E_52,C_50] : k5_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53) = k4_enumset1(A_48,B_49,C_50,D_51,E_52,F_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [A_112,D_116,F_115,E_114,C_113,G_118,B_117] : k2_xboole_0(k3_enumset1(A_112,B_117,C_113,D_116,E_114),k2_tarski(F_115,G_118)) = k5_enumset1(A_112,B_117,C_113,D_116,E_114,F_115,G_118) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_291,plain,(
    ! [F_115,D_42,A_39,C_41,B_40,G_118] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,F_115,G_118) = k2_xboole_0(k2_enumset1(A_39,B_40,C_41,D_42),k2_tarski(F_115,G_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_282])).

tff(c_338,plain,(
    ! [A_124,C_126,F_129,B_125,G_127,D_128] : k2_xboole_0(k2_enumset1(A_124,B_125,C_126,D_128),k2_tarski(F_129,G_127)) = k4_enumset1(A_124,B_125,C_126,D_128,F_129,G_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_291])).

tff(c_356,plain,(
    ! [A_124,C_126,B_125,A_33,D_128] : k4_enumset1(A_124,B_125,C_126,D_128,A_33,A_33) = k2_xboole_0(k2_enumset1(A_124,B_125,C_126,D_128),k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_338])).

tff(c_361,plain,(
    ! [B_133,A_130,D_132,A_131,C_134] : k4_enumset1(A_131,B_133,C_134,D_132,A_130,A_130) = k3_enumset1(A_131,B_133,C_134,D_132,A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_356])).

tff(c_22,plain,(
    ! [E_47,D_46,C_45,A_43,B_44] : k4_enumset1(A_43,A_43,B_44,C_45,D_46,E_47) = k3_enumset1(A_43,B_44,C_45,D_46,E_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_368,plain,(
    ! [B_133,C_134,D_132,A_130] : k3_enumset1(B_133,C_134,D_132,A_130,A_130) = k3_enumset1(B_133,B_133,C_134,D_132,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_22])).

tff(c_377,plain,(
    ! [B_133,C_134,D_132,A_130] : k3_enumset1(B_133,C_134,D_132,A_130,A_130) = k2_enumset1(B_133,C_134,D_132,A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_368])).

tff(c_18,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [B_143,C_144,D_145,A_146] : k3_enumset1(B_143,C_144,D_145,A_146,A_146) = k2_enumset1(B_143,C_144,D_145,A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_368])).

tff(c_416,plain,(
    ! [C_144,D_145,A_146] : k2_enumset1(C_144,D_145,A_146,A_146) = k2_enumset1(C_144,C_144,D_145,A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_20])).

tff(c_434,plain,(
    ! [C_144,D_145,A_146] : k2_enumset1(C_144,D_145,A_146,A_146) = k1_enumset1(C_144,D_145,A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_416])).

tff(c_16,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k3_enumset1(A_18,B_19,C_20,D_21,E_22),k2_tarski(F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_380,plain,(
    ! [G_136,A_137,E_142,B_141,F_140,H_138,C_139,D_135] : k2_xboole_0(k4_enumset1(A_137,B_141,C_139,D_135,E_142,F_140),k2_tarski(G_136,H_138)) = k6_enumset1(A_137,B_141,C_139,D_135,E_142,F_140,G_136,H_138) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_392,plain,(
    ! [G_136,E_47,D_46,H_138,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,D_46,E_47,G_136,H_138) = k2_xboole_0(k3_enumset1(A_43,B_44,C_45,D_46,E_47),k2_tarski(G_136,H_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_380])).

tff(c_399,plain,(
    ! [G_136,E_47,D_46,H_138,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,D_46,E_47,G_136,H_138) = k5_enumset1(A_43,B_44,C_45,D_46,E_47,G_136,H_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_392])).

tff(c_522,plain,(
    ! [B_155,F_153,G_154,H_158,E_159,C_156,D_152,A_157] : k2_xboole_0(k2_enumset1(A_157,B_155,C_156,D_152),k2_enumset1(E_159,F_153,G_154,H_158)) = k6_enumset1(A_157,B_155,C_156,D_152,E_159,F_153,G_154,H_158) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_549,plain,(
    ! [F_153,A_36,G_154,H_158,E_159,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,E_159,F_153,G_154,H_158) = k2_xboole_0(k1_enumset1(A_36,B_37,C_38),k2_enumset1(E_159,F_153,G_154,H_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_522])).

tff(c_1091,plain,(
    ! [B_211,H_209,E_207,A_210,F_208,G_206,C_212] : k2_xboole_0(k1_enumset1(A_210,B_211,C_212),k2_enumset1(E_207,F_208,G_206,H_209)) = k5_enumset1(A_210,B_211,C_212,E_207,F_208,G_206,H_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_549])).

tff(c_1133,plain,(
    ! [A_34,H_209,E_207,F_208,B_35,G_206] : k5_enumset1(A_34,A_34,B_35,E_207,F_208,G_206,H_209) = k2_xboole_0(k2_tarski(A_34,B_35),k2_enumset1(E_207,F_208,G_206,H_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1091])).

tff(c_2531,plain,(
    ! [F_304,E_306,B_305,G_303,H_307,A_302] : k2_xboole_0(k2_tarski(A_302,B_305),k2_enumset1(E_306,F_304,G_303,H_307)) = k4_enumset1(A_302,B_305,E_306,F_304,G_303,H_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1133])).

tff(c_2570,plain,(
    ! [F_304,E_306,A_33,G_303,H_307] : k4_enumset1(A_33,A_33,E_306,F_304,G_303,H_307) = k2_xboole_0(k1_tarski(A_33),k2_enumset1(E_306,F_304,G_303,H_307)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2531])).

tff(c_6541,plain,(
    ! [F_412,H_411,E_414,A_410,G_413] : k2_xboole_0(k1_tarski(A_410),k2_enumset1(E_414,F_412,G_413,H_411)) = k3_enumset1(A_410,E_414,F_412,G_413,H_411) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2570])).

tff(c_6583,plain,(
    ! [A_410,C_144,D_145,A_146] : k3_enumset1(A_410,C_144,D_145,A_146,A_146) = k2_xboole_0(k1_tarski(A_410),k1_enumset1(C_144,D_145,A_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_6541])).

tff(c_6603,plain,(
    ! [A_410,C_144,D_145,A_146] : k2_xboole_0(k1_tarski(A_410),k1_enumset1(C_144,D_145,A_146)) = k2_enumset1(A_410,C_144,D_145,A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_6583])).

tff(c_1339,plain,(
    ! [C_233,A_230,C_228,B_232,A_231,B_229] : k5_enumset1(A_231,B_229,C_228,A_230,A_230,B_232,C_233) = k2_xboole_0(k1_enumset1(A_231,B_229,C_228),k1_enumset1(A_230,B_232,C_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1091])).

tff(c_1638,plain,(
    ! [A_252,B_251,C_253,A_250,B_254] : k5_enumset1(A_250,A_250,B_251,A_252,A_252,B_254,C_253) = k2_xboole_0(k2_tarski(A_250,B_251),k1_enumset1(A_252,B_254,C_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1339])).

tff(c_2231,plain,(
    ! [A_296,F_293,E_297,D_294,B_295] : k4_enumset1(A_296,B_295,D_294,D_294,E_297,F_293) = k2_xboole_0(k2_tarski(A_296,B_295),k1_enumset1(D_294,E_297,F_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1638])).

tff(c_2299,plain,(
    ! [A_33,D_294,E_297,F_293] : k4_enumset1(A_33,A_33,D_294,D_294,E_297,F_293) = k2_xboole_0(k1_tarski(A_33),k1_enumset1(D_294,E_297,F_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2231])).

tff(c_16755,plain,(
    ! [A_585,D_586,E_587,F_588] : k4_enumset1(A_585,A_585,D_586,D_586,E_587,F_588) = k2_enumset1(A_585,D_586,E_587,F_588) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6603,c_2299])).

tff(c_26,plain,(
    ! [B_55,A_54,C_56] : k1_enumset1(B_55,A_54,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2290,plain,(
    ! [A_296,C_56,B_55,B_295,A_54] : k4_enumset1(A_296,B_295,A_54,A_54,B_55,C_56) = k2_xboole_0(k2_tarski(A_296,B_295),k1_enumset1(B_55,A_54,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2231])).

tff(c_16777,plain,(
    ! [A_585,E_587,D_586,F_588] : k2_xboole_0(k2_tarski(A_585,A_585),k1_enumset1(E_587,D_586,F_588)) = k2_enumset1(A_585,D_586,E_587,F_588) ),
    inference(superposition,[status(thm),theory(equality)],[c_16755,c_2290])).

tff(c_16892,plain,(
    ! [A_585,E_587,D_586,F_588] : k2_enumset1(A_585,E_587,D_586,F_588) = k2_enumset1(A_585,D_586,E_587,F_588) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6603,c_14,c_16777])).

tff(c_28,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16892,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.25  
% 9.45/3.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.26  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.45/3.26  
% 9.45/3.26  %Foreground sorts:
% 9.45/3.26  
% 9.45/3.26  
% 9.45/3.26  %Background operators:
% 9.45/3.26  
% 9.45/3.26  
% 9.45/3.26  %Foreground operators:
% 9.45/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.45/3.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.45/3.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.45/3.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.45/3.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.45/3.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.45/3.26  tff('#skF_2', type, '#skF_2': $i).
% 9.45/3.26  tff('#skF_3', type, '#skF_3': $i).
% 9.45/3.26  tff('#skF_1', type, '#skF_1': $i).
% 9.45/3.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.26  tff('#skF_4', type, '#skF_4': $i).
% 9.45/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.45/3.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.45/3.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.45/3.26  
% 9.45/3.27  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 9.45/3.27  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 9.45/3.27  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.45/3.27  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 9.45/3.27  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 9.45/3.27  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 9.45/3.27  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 9.45/3.27  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.45/3.27  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 9.45/3.27  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 9.45/3.27  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 9.45/3.27  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 9.45/3.27  tff(c_20, plain, (![A_39, B_40, C_41, D_42]: (k3_enumset1(A_39, A_39, B_40, C_41, D_42)=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.45/3.27  tff(c_8, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k1_tarski(E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.45/3.27  tff(c_14, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.45/3.27  tff(c_24, plain, (![B_49, F_53, A_48, D_51, E_52, C_50]: (k5_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53)=k4_enumset1(A_48, B_49, C_50, D_51, E_52, F_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.45/3.27  tff(c_282, plain, (![A_112, D_116, F_115, E_114, C_113, G_118, B_117]: (k2_xboole_0(k3_enumset1(A_112, B_117, C_113, D_116, E_114), k2_tarski(F_115, G_118))=k5_enumset1(A_112, B_117, C_113, D_116, E_114, F_115, G_118))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.27  tff(c_291, plain, (![F_115, D_42, A_39, C_41, B_40, G_118]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, F_115, G_118)=k2_xboole_0(k2_enumset1(A_39, B_40, C_41, D_42), k2_tarski(F_115, G_118)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_282])).
% 9.45/3.27  tff(c_338, plain, (![A_124, C_126, F_129, B_125, G_127, D_128]: (k2_xboole_0(k2_enumset1(A_124, B_125, C_126, D_128), k2_tarski(F_129, G_127))=k4_enumset1(A_124, B_125, C_126, D_128, F_129, G_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_291])).
% 9.45/3.27  tff(c_356, plain, (![A_124, C_126, B_125, A_33, D_128]: (k4_enumset1(A_124, B_125, C_126, D_128, A_33, A_33)=k2_xboole_0(k2_enumset1(A_124, B_125, C_126, D_128), k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_338])).
% 9.45/3.27  tff(c_361, plain, (![B_133, A_130, D_132, A_131, C_134]: (k4_enumset1(A_131, B_133, C_134, D_132, A_130, A_130)=k3_enumset1(A_131, B_133, C_134, D_132, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_356])).
% 9.45/3.27  tff(c_22, plain, (![E_47, D_46, C_45, A_43, B_44]: (k4_enumset1(A_43, A_43, B_44, C_45, D_46, E_47)=k3_enumset1(A_43, B_44, C_45, D_46, E_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.45/3.27  tff(c_368, plain, (![B_133, C_134, D_132, A_130]: (k3_enumset1(B_133, C_134, D_132, A_130, A_130)=k3_enumset1(B_133, B_133, C_134, D_132, A_130))), inference(superposition, [status(thm), theory('equality')], [c_361, c_22])).
% 9.45/3.27  tff(c_377, plain, (![B_133, C_134, D_132, A_130]: (k3_enumset1(B_133, C_134, D_132, A_130, A_130)=k2_enumset1(B_133, C_134, D_132, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_368])).
% 9.45/3.27  tff(c_18, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.45/3.27  tff(c_400, plain, (![B_143, C_144, D_145, A_146]: (k3_enumset1(B_143, C_144, D_145, A_146, A_146)=k2_enumset1(B_143, C_144, D_145, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_368])).
% 9.45/3.27  tff(c_416, plain, (![C_144, D_145, A_146]: (k2_enumset1(C_144, D_145, A_146, A_146)=k2_enumset1(C_144, C_144, D_145, A_146))), inference(superposition, [status(thm), theory('equality')], [c_400, c_20])).
% 9.45/3.27  tff(c_434, plain, (![C_144, D_145, A_146]: (k2_enumset1(C_144, D_145, A_146, A_146)=k1_enumset1(C_144, D_145, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_416])).
% 9.45/3.27  tff(c_16, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.45/3.27  tff(c_10, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k3_enumset1(A_18, B_19, C_20, D_21, E_22), k2_tarski(F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.27  tff(c_380, plain, (![G_136, A_137, E_142, B_141, F_140, H_138, C_139, D_135]: (k2_xboole_0(k4_enumset1(A_137, B_141, C_139, D_135, E_142, F_140), k2_tarski(G_136, H_138))=k6_enumset1(A_137, B_141, C_139, D_135, E_142, F_140, G_136, H_138))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.45/3.27  tff(c_392, plain, (![G_136, E_47, D_46, H_138, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, D_46, E_47, G_136, H_138)=k2_xboole_0(k3_enumset1(A_43, B_44, C_45, D_46, E_47), k2_tarski(G_136, H_138)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_380])).
% 9.45/3.27  tff(c_399, plain, (![G_136, E_47, D_46, H_138, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, D_46, E_47, G_136, H_138)=k5_enumset1(A_43, B_44, C_45, D_46, E_47, G_136, H_138))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_392])).
% 9.45/3.27  tff(c_522, plain, (![B_155, F_153, G_154, H_158, E_159, C_156, D_152, A_157]: (k2_xboole_0(k2_enumset1(A_157, B_155, C_156, D_152), k2_enumset1(E_159, F_153, G_154, H_158))=k6_enumset1(A_157, B_155, C_156, D_152, E_159, F_153, G_154, H_158))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.45/3.27  tff(c_549, plain, (![F_153, A_36, G_154, H_158, E_159, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, E_159, F_153, G_154, H_158)=k2_xboole_0(k1_enumset1(A_36, B_37, C_38), k2_enumset1(E_159, F_153, G_154, H_158)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_522])).
% 9.45/3.27  tff(c_1091, plain, (![B_211, H_209, E_207, A_210, F_208, G_206, C_212]: (k2_xboole_0(k1_enumset1(A_210, B_211, C_212), k2_enumset1(E_207, F_208, G_206, H_209))=k5_enumset1(A_210, B_211, C_212, E_207, F_208, G_206, H_209))), inference(demodulation, [status(thm), theory('equality')], [c_399, c_549])).
% 9.45/3.27  tff(c_1133, plain, (![A_34, H_209, E_207, F_208, B_35, G_206]: (k5_enumset1(A_34, A_34, B_35, E_207, F_208, G_206, H_209)=k2_xboole_0(k2_tarski(A_34, B_35), k2_enumset1(E_207, F_208, G_206, H_209)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1091])).
% 9.45/3.27  tff(c_2531, plain, (![F_304, E_306, B_305, G_303, H_307, A_302]: (k2_xboole_0(k2_tarski(A_302, B_305), k2_enumset1(E_306, F_304, G_303, H_307))=k4_enumset1(A_302, B_305, E_306, F_304, G_303, H_307))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1133])).
% 9.45/3.27  tff(c_2570, plain, (![F_304, E_306, A_33, G_303, H_307]: (k4_enumset1(A_33, A_33, E_306, F_304, G_303, H_307)=k2_xboole_0(k1_tarski(A_33), k2_enumset1(E_306, F_304, G_303, H_307)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2531])).
% 9.45/3.27  tff(c_6541, plain, (![F_412, H_411, E_414, A_410, G_413]: (k2_xboole_0(k1_tarski(A_410), k2_enumset1(E_414, F_412, G_413, H_411))=k3_enumset1(A_410, E_414, F_412, G_413, H_411))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2570])).
% 9.45/3.27  tff(c_6583, plain, (![A_410, C_144, D_145, A_146]: (k3_enumset1(A_410, C_144, D_145, A_146, A_146)=k2_xboole_0(k1_tarski(A_410), k1_enumset1(C_144, D_145, A_146)))), inference(superposition, [status(thm), theory('equality')], [c_434, c_6541])).
% 9.45/3.27  tff(c_6603, plain, (![A_410, C_144, D_145, A_146]: (k2_xboole_0(k1_tarski(A_410), k1_enumset1(C_144, D_145, A_146))=k2_enumset1(A_410, C_144, D_145, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_6583])).
% 9.45/3.27  tff(c_1339, plain, (![C_233, A_230, C_228, B_232, A_231, B_229]: (k5_enumset1(A_231, B_229, C_228, A_230, A_230, B_232, C_233)=k2_xboole_0(k1_enumset1(A_231, B_229, C_228), k1_enumset1(A_230, B_232, C_233)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1091])).
% 9.45/3.27  tff(c_1638, plain, (![A_252, B_251, C_253, A_250, B_254]: (k5_enumset1(A_250, A_250, B_251, A_252, A_252, B_254, C_253)=k2_xboole_0(k2_tarski(A_250, B_251), k1_enumset1(A_252, B_254, C_253)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1339])).
% 9.45/3.27  tff(c_2231, plain, (![A_296, F_293, E_297, D_294, B_295]: (k4_enumset1(A_296, B_295, D_294, D_294, E_297, F_293)=k2_xboole_0(k2_tarski(A_296, B_295), k1_enumset1(D_294, E_297, F_293)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1638])).
% 9.45/3.27  tff(c_2299, plain, (![A_33, D_294, E_297, F_293]: (k4_enumset1(A_33, A_33, D_294, D_294, E_297, F_293)=k2_xboole_0(k1_tarski(A_33), k1_enumset1(D_294, E_297, F_293)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2231])).
% 9.45/3.27  tff(c_16755, plain, (![A_585, D_586, E_587, F_588]: (k4_enumset1(A_585, A_585, D_586, D_586, E_587, F_588)=k2_enumset1(A_585, D_586, E_587, F_588))), inference(demodulation, [status(thm), theory('equality')], [c_6603, c_2299])).
% 9.45/3.27  tff(c_26, plain, (![B_55, A_54, C_56]: (k1_enumset1(B_55, A_54, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.45/3.27  tff(c_2290, plain, (![A_296, C_56, B_55, B_295, A_54]: (k4_enumset1(A_296, B_295, A_54, A_54, B_55, C_56)=k2_xboole_0(k2_tarski(A_296, B_295), k1_enumset1(B_55, A_54, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2231])).
% 9.45/3.27  tff(c_16777, plain, (![A_585, E_587, D_586, F_588]: (k2_xboole_0(k2_tarski(A_585, A_585), k1_enumset1(E_587, D_586, F_588))=k2_enumset1(A_585, D_586, E_587, F_588))), inference(superposition, [status(thm), theory('equality')], [c_16755, c_2290])).
% 9.45/3.27  tff(c_16892, plain, (![A_585, E_587, D_586, F_588]: (k2_enumset1(A_585, E_587, D_586, F_588)=k2_enumset1(A_585, D_586, E_587, F_588))), inference(demodulation, [status(thm), theory('equality')], [c_6603, c_14, c_16777])).
% 9.45/3.27  tff(c_28, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.45/3.27  tff(c_16925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16892, c_28])).
% 9.45/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.27  
% 9.45/3.27  Inference rules
% 9.45/3.27  ----------------------
% 9.45/3.27  #Ref     : 0
% 9.45/3.27  #Sup     : 3718
% 9.45/3.27  #Fact    : 0
% 9.45/3.27  #Define  : 0
% 9.45/3.27  #Split   : 0
% 9.45/3.27  #Chain   : 0
% 9.45/3.27  #Close   : 0
% 9.45/3.27  
% 9.45/3.27  Ordering : KBO
% 9.45/3.27  
% 9.45/3.27  Simplification rules
% 9.45/3.27  ----------------------
% 9.45/3.27  #Subsume      : 144
% 9.45/3.27  #Demod        : 5710
% 9.45/3.27  #Tautology    : 2883
% 9.45/3.27  #SimpNegUnit  : 0
% 9.45/3.27  #BackRed      : 8
% 9.45/3.27  
% 9.45/3.27  #Partial instantiations: 0
% 9.45/3.27  #Strategies tried      : 1
% 9.45/3.27  
% 9.45/3.27  Timing (in seconds)
% 9.45/3.27  ----------------------
% 9.45/3.28  Preprocessing        : 0.30
% 9.45/3.28  Parsing              : 0.16
% 9.45/3.28  CNF conversion       : 0.02
% 9.45/3.28  Main loop            : 2.18
% 9.45/3.28  Inferencing          : 0.66
% 9.45/3.28  Reduction            : 1.14
% 9.45/3.28  Demodulation         : 1.01
% 9.45/3.28  BG Simplification    : 0.07
% 9.45/3.28  Subsumption          : 0.23
% 9.45/3.28  Abstraction          : 0.12
% 9.45/3.28  MUC search           : 0.00
% 9.45/3.28  Cooper               : 0.00
% 9.45/3.28  Total                : 2.52
% 9.45/3.28  Index Insertion      : 0.00
% 9.45/3.28  Index Deletion       : 0.00
% 9.45/3.28  Index Matching       : 0.00
% 9.45/3.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

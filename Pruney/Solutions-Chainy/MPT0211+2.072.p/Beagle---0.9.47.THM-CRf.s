%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 9.99s
% Output     : CNFRefutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 466 expanded)
%              Number of leaves         :   30 ( 169 expanded)
%              Depth                    :   16
%              Number of atoms          :   72 ( 448 expanded)
%              Number of equality atoms :   71 ( 447 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_56,C_58,B_57] : k1_enumset1(A_56,C_58,B_57) = k1_enumset1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_566,plain,(
    ! [D_96,B_95,E_97,C_93,A_94] : k2_xboole_0(k1_tarski(A_94),k2_enumset1(B_95,C_93,D_96,E_97)) = k3_enumset1(A_94,B_95,C_93,D_96,E_97) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_575,plain,(
    ! [A_94,A_31,B_32,C_33] : k3_enumset1(A_94,A_31,A_31,B_32,C_33) = k2_xboole_0(k1_tarski(A_94),k1_enumset1(A_31,B_32,C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_578,plain,(
    ! [A_98,A_99,B_100,C_101] : k3_enumset1(A_98,A_99,A_99,B_100,C_101) = k2_xboole_0(k1_tarski(A_98),k1_enumset1(A_99,B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36,D_37] : k3_enumset1(A_34,A_34,B_35,C_36,D_37) = k2_enumset1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_588,plain,(
    ! [A_99,B_100,C_101] : k2_xboole_0(k1_tarski(A_99),k1_enumset1(A_99,B_100,C_101)) = k2_enumset1(A_99,A_99,B_100,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_20])).

tff(c_638,plain,(
    ! [A_102,B_103,C_104] : k2_xboole_0(k1_tarski(A_102),k1_enumset1(A_102,B_103,C_104)) = k1_enumset1(A_102,B_103,C_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_588])).

tff(c_651,plain,(
    ! [A_31,B_32,C_33] : k3_enumset1(A_31,A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_638])).

tff(c_50,plain,(
    ! [A_63,C_64,B_65] : k1_enumset1(A_63,C_64,B_65) = k1_enumset1(A_63,B_65,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [B_65,C_64] : k1_enumset1(B_65,C_64,B_65) = k2_tarski(B_65,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_899,plain,(
    ! [B_140,A_141,C_142] : k2_xboole_0(k1_tarski(B_140),k1_enumset1(A_141,B_140,C_142)) = k1_enumset1(B_140,C_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_638])).

tff(c_974,plain,(
    ! [B_143,A_144,C_145] : k3_enumset1(B_143,A_144,A_144,B_143,C_145) = k1_enumset1(B_143,C_145,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_575])).

tff(c_995,plain,(
    ! [A_144,C_145] : k2_enumset1(A_144,A_144,A_144,C_145) = k1_enumset1(A_144,C_145,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_20])).

tff(c_1019,plain,(
    ! [A_144,C_145] : k2_enumset1(A_144,A_144,A_144,C_145) = k2_tarski(A_144,C_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_995])).

tff(c_22,plain,(
    ! [D_41,B_39,A_38,E_42,C_40] : k4_enumset1(A_38,A_38,B_39,C_40,D_41,E_42) = k3_enumset1(A_38,B_39,C_40,D_41,E_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_756,plain,(
    ! [D_122,A_121,F_118,B_119,C_123,E_120] : k2_xboole_0(k3_enumset1(A_121,B_119,C_123,D_122,E_120),k1_tarski(F_118)) = k4_enumset1(A_121,B_119,C_123,D_122,E_120,F_118) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_771,plain,(
    ! [D_37,F_118,A_34,B_35,C_36] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,F_118) = k2_xboole_0(k2_enumset1(A_34,B_35,C_36,D_37),k1_tarski(F_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_756])).

tff(c_1225,plain,(
    ! [D_162,C_165,B_163,A_161,F_164] : k2_xboole_0(k2_enumset1(A_161,B_163,C_165,D_162),k1_tarski(F_164)) = k3_enumset1(A_161,B_163,C_165,D_162,F_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_1234,plain,(
    ! [A_144,C_145,F_164] : k3_enumset1(A_144,A_144,A_144,C_145,F_164) = k2_xboole_0(k2_tarski(A_144,C_145),k1_tarski(F_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_1225])).

tff(c_1243,plain,(
    ! [A_144,C_145,F_164] : k2_xboole_0(k2_tarski(A_144,C_145),k1_tarski(F_164)) = k1_enumset1(A_144,C_145,F_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1234])).

tff(c_8,plain,(
    ! [C_10,B_9,A_8] : k1_enumset1(C_10,B_9,A_8) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1256,plain,(
    ! [C_169,A_170,B_171] : k2_xboole_0(k1_tarski(C_169),k1_enumset1(A_170,B_171,C_169)) = k1_enumset1(C_169,B_171,A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_638])).

tff(c_1460,plain,(
    ! [C_175,A_176,B_177] : k3_enumset1(C_175,A_176,A_176,B_177,C_175) = k1_enumset1(C_175,B_177,A_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_575])).

tff(c_1492,plain,(
    ! [A_176,B_177] : k2_enumset1(A_176,A_176,B_177,A_176) = k1_enumset1(A_176,B_177,A_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_20])).

tff(c_1534,plain,(
    ! [A_178,B_179] : k2_enumset1(A_178,A_178,B_179,A_178) = k2_tarski(A_178,B_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1492])).

tff(c_774,plain,(
    ! [D_37,F_118,A_34,B_35,C_36] : k2_xboole_0(k2_enumset1(A_34,B_35,C_36,D_37),k1_tarski(F_118)) = k3_enumset1(A_34,B_35,C_36,D_37,F_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_1540,plain,(
    ! [A_178,B_179,F_118] : k3_enumset1(A_178,A_178,B_179,A_178,F_118) = k2_xboole_0(k2_tarski(A_178,B_179),k1_tarski(F_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_774])).

tff(c_1684,plain,(
    ! [A_189,B_190,F_191] : k3_enumset1(A_189,A_189,B_190,A_189,F_191) = k1_enumset1(A_189,B_190,F_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1540])).

tff(c_1724,plain,(
    ! [A_189,B_190,F_191] : k2_enumset1(A_189,B_190,A_189,F_191) = k1_enumset1(A_189,B_190,F_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_1684,c_20])).

tff(c_24,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] : k5_enumset1(A_43,A_43,B_44,C_45,D_46,E_47,F_48) = k4_enumset1(A_43,B_44,C_45,D_46,E_47,F_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1025,plain,(
    ! [C_147,F_149,E_148,G_150,B_152,D_151,A_146] : k2_xboole_0(k3_enumset1(A_146,B_152,C_147,D_151,E_148),k2_tarski(F_149,G_150)) = k5_enumset1(A_146,B_152,C_147,D_151,E_148,F_149,G_150) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1046,plain,(
    ! [D_37,F_149,G_150,A_34,B_35,C_36] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,F_149,G_150) = k2_xboole_0(k2_enumset1(A_34,B_35,C_36,D_37),k2_tarski(F_149,G_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1025])).

tff(c_1660,plain,(
    ! [D_184,F_185,G_187,C_188,B_186,A_183] : k2_xboole_0(k2_enumset1(A_183,B_186,C_188,D_184),k2_tarski(F_185,G_187)) = k4_enumset1(A_183,B_186,C_188,D_184,F_185,G_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1046])).

tff(c_1678,plain,(
    ! [A_31,F_185,C_33,G_187,B_32] : k4_enumset1(A_31,A_31,B_32,C_33,F_185,G_187) = k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k2_tarski(F_185,G_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1660])).

tff(c_7928,plain,(
    ! [F_308,B_306,A_307,G_310,C_309] : k2_xboole_0(k1_enumset1(A_307,B_306,C_309),k2_tarski(F_308,G_310)) = k3_enumset1(A_307,B_306,C_309,F_308,G_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1678])).

tff(c_7979,plain,(
    ! [A_29,B_30,F_308,G_310] : k3_enumset1(A_29,A_29,B_30,F_308,G_310) = k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(F_308,G_310)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7928])).

tff(c_7982,plain,(
    ! [A_29,B_30,F_308,G_310] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(F_308,G_310)) = k2_enumset1(A_29,B_30,F_308,G_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7979])).

tff(c_146,plain,(
    ! [B_70,C_71,A_72] : k1_enumset1(B_70,C_71,A_72) = k1_enumset1(A_72,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_72,C_71] : k1_enumset1(A_72,C_71,C_71) = k2_tarski(C_71,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_16])).

tff(c_1526,plain,(
    ! [A_176,B_177] : k2_enumset1(A_176,A_176,B_177,A_176) = k2_tarski(A_176,B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1492])).

tff(c_1240,plain,(
    ! [A_31,B_32,C_33,F_164] : k3_enumset1(A_31,A_31,B_32,C_33,F_164) = k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k1_tarski(F_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1225])).

tff(c_1245,plain,(
    ! [A_31,B_32,C_33,F_164] : k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k1_tarski(F_164)) = k2_enumset1(A_31,B_32,C_33,F_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1240])).

tff(c_2203,plain,(
    ! [A_202,B_203,C_204,F_205] : k2_xboole_0(k1_enumset1(A_202,B_203,C_204),k1_tarski(F_205)) = k2_enumset1(A_202,B_203,C_204,F_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1240])).

tff(c_4297,plain,(
    ! [C_244,B_245,A_246,F_247] : k2_xboole_0(k1_enumset1(C_244,B_245,A_246),k1_tarski(F_247)) = k2_enumset1(A_246,B_245,C_244,F_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2203])).

tff(c_4780,plain,(
    ! [C_255,B_256,A_257,F_258] : k2_enumset1(C_255,B_256,A_257,F_258) = k2_enumset1(A_257,B_256,C_255,F_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_4297])).

tff(c_5073,plain,(
    ! [B_261,A_262] : k2_enumset1(B_261,A_262,A_262,A_262) = k2_tarski(A_262,B_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_4780])).

tff(c_5119,plain,(
    ! [B_261,A_262,F_118] : k3_enumset1(B_261,A_262,A_262,A_262,F_118) = k2_xboole_0(k2_tarski(A_262,B_261),k1_tarski(F_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5073,c_774])).

tff(c_6978,plain,(
    ! [B_293,A_294,F_295] : k3_enumset1(B_293,A_294,A_294,A_294,F_295) = k1_enumset1(A_294,B_293,F_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_5119])).

tff(c_1354,plain,(
    ! [A_172,B_173,C_174] : k2_xboole_0(k1_tarski(A_172),k1_enumset1(B_173,C_174,A_172)) = k1_enumset1(A_172,B_173,C_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_638])).

tff(c_1405,plain,(
    ! [C_33,A_31,B_32] : k3_enumset1(C_33,A_31,A_31,B_32,C_33) = k1_enumset1(C_33,A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_1354])).

tff(c_7041,plain,(
    ! [F_295,A_294] : k1_enumset1(F_295,A_294,A_294) = k1_enumset1(A_294,F_295,F_295) ),
    inference(superposition,[status(thm),theory(equality)],[c_6978,c_1405])).

tff(c_7183,plain,(
    ! [F_295,A_294] : k2_tarski(F_295,A_294) = k2_tarski(A_294,F_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_7041])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_7215,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7183,c_7183,c_31])).

tff(c_25441,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7982,c_7215])).

tff(c_25444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1724,c_25441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:01:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.99/3.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.87  
% 9.99/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.87  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 9.99/3.87  
% 9.99/3.87  %Foreground sorts:
% 9.99/3.87  
% 9.99/3.87  
% 9.99/3.87  %Background operators:
% 9.99/3.87  
% 9.99/3.87  
% 9.99/3.87  %Foreground operators:
% 9.99/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.99/3.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.99/3.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.99/3.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.99/3.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.99/3.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.99/3.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.99/3.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.99/3.87  tff('#skF_2', type, '#skF_2': $i).
% 9.99/3.87  tff('#skF_3', type, '#skF_3': $i).
% 9.99/3.87  tff('#skF_1', type, '#skF_1': $i).
% 9.99/3.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.99/3.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.99/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.99/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.99/3.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.99/3.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.99/3.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.99/3.87  
% 9.99/3.89  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 9.99/3.89  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 9.99/3.89  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 9.99/3.89  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 9.99/3.89  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.99/3.89  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 9.99/3.89  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 9.99/3.89  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 9.99/3.89  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 9.99/3.89  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 9.99/3.89  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 9.99/3.89  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 9.99/3.89  tff(c_28, plain, (![A_56, C_58, B_57]: (k1_enumset1(A_56, C_58, B_57)=k1_enumset1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.99/3.89  tff(c_18, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.99/3.89  tff(c_566, plain, (![D_96, B_95, E_97, C_93, A_94]: (k2_xboole_0(k1_tarski(A_94), k2_enumset1(B_95, C_93, D_96, E_97))=k3_enumset1(A_94, B_95, C_93, D_96, E_97))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.99/3.89  tff(c_575, plain, (![A_94, A_31, B_32, C_33]: (k3_enumset1(A_94, A_31, A_31, B_32, C_33)=k2_xboole_0(k1_tarski(A_94), k1_enumset1(A_31, B_32, C_33)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 9.99/3.89  tff(c_578, plain, (![A_98, A_99, B_100, C_101]: (k3_enumset1(A_98, A_99, A_99, B_100, C_101)=k2_xboole_0(k1_tarski(A_98), k1_enumset1(A_99, B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 9.99/3.89  tff(c_20, plain, (![A_34, B_35, C_36, D_37]: (k3_enumset1(A_34, A_34, B_35, C_36, D_37)=k2_enumset1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.99/3.89  tff(c_588, plain, (![A_99, B_100, C_101]: (k2_xboole_0(k1_tarski(A_99), k1_enumset1(A_99, B_100, C_101))=k2_enumset1(A_99, A_99, B_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_578, c_20])).
% 9.99/3.89  tff(c_638, plain, (![A_102, B_103, C_104]: (k2_xboole_0(k1_tarski(A_102), k1_enumset1(A_102, B_103, C_104))=k1_enumset1(A_102, B_103, C_104))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_588])).
% 9.99/3.89  tff(c_651, plain, (![A_31, B_32, C_33]: (k3_enumset1(A_31, A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(superposition, [status(thm), theory('equality')], [c_575, c_638])).
% 9.99/3.89  tff(c_50, plain, (![A_63, C_64, B_65]: (k1_enumset1(A_63, C_64, B_65)=k1_enumset1(A_63, B_65, C_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.99/3.89  tff(c_16, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.99/3.89  tff(c_66, plain, (![B_65, C_64]: (k1_enumset1(B_65, C_64, B_65)=k2_tarski(B_65, C_64))), inference(superposition, [status(thm), theory('equality')], [c_50, c_16])).
% 9.99/3.89  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.99/3.89  tff(c_899, plain, (![B_140, A_141, C_142]: (k2_xboole_0(k1_tarski(B_140), k1_enumset1(A_141, B_140, C_142))=k1_enumset1(B_140, C_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_6, c_638])).
% 9.99/3.89  tff(c_974, plain, (![B_143, A_144, C_145]: (k3_enumset1(B_143, A_144, A_144, B_143, C_145)=k1_enumset1(B_143, C_145, A_144))), inference(superposition, [status(thm), theory('equality')], [c_899, c_575])).
% 9.99/3.89  tff(c_995, plain, (![A_144, C_145]: (k2_enumset1(A_144, A_144, A_144, C_145)=k1_enumset1(A_144, C_145, A_144))), inference(superposition, [status(thm), theory('equality')], [c_974, c_20])).
% 9.99/3.89  tff(c_1019, plain, (![A_144, C_145]: (k2_enumset1(A_144, A_144, A_144, C_145)=k2_tarski(A_144, C_145))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_995])).
% 9.99/3.89  tff(c_22, plain, (![D_41, B_39, A_38, E_42, C_40]: (k4_enumset1(A_38, A_38, B_39, C_40, D_41, E_42)=k3_enumset1(A_38, B_39, C_40, D_41, E_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.99/3.89  tff(c_756, plain, (![D_122, A_121, F_118, B_119, C_123, E_120]: (k2_xboole_0(k3_enumset1(A_121, B_119, C_123, D_122, E_120), k1_tarski(F_118))=k4_enumset1(A_121, B_119, C_123, D_122, E_120, F_118))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.99/3.89  tff(c_771, plain, (![D_37, F_118, A_34, B_35, C_36]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, F_118)=k2_xboole_0(k2_enumset1(A_34, B_35, C_36, D_37), k1_tarski(F_118)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_756])).
% 9.99/3.89  tff(c_1225, plain, (![D_162, C_165, B_163, A_161, F_164]: (k2_xboole_0(k2_enumset1(A_161, B_163, C_165, D_162), k1_tarski(F_164))=k3_enumset1(A_161, B_163, C_165, D_162, F_164))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_771])).
% 9.99/3.89  tff(c_1234, plain, (![A_144, C_145, F_164]: (k3_enumset1(A_144, A_144, A_144, C_145, F_164)=k2_xboole_0(k2_tarski(A_144, C_145), k1_tarski(F_164)))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_1225])).
% 9.99/3.89  tff(c_1243, plain, (![A_144, C_145, F_164]: (k2_xboole_0(k2_tarski(A_144, C_145), k1_tarski(F_164))=k1_enumset1(A_144, C_145, F_164))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_1234])).
% 9.99/3.89  tff(c_8, plain, (![C_10, B_9, A_8]: (k1_enumset1(C_10, B_9, A_8)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.99/3.89  tff(c_1256, plain, (![C_169, A_170, B_171]: (k2_xboole_0(k1_tarski(C_169), k1_enumset1(A_170, B_171, C_169))=k1_enumset1(C_169, B_171, A_170))), inference(superposition, [status(thm), theory('equality')], [c_8, c_638])).
% 9.99/3.89  tff(c_1460, plain, (![C_175, A_176, B_177]: (k3_enumset1(C_175, A_176, A_176, B_177, C_175)=k1_enumset1(C_175, B_177, A_176))), inference(superposition, [status(thm), theory('equality')], [c_1256, c_575])).
% 9.99/3.89  tff(c_1492, plain, (![A_176, B_177]: (k2_enumset1(A_176, A_176, B_177, A_176)=k1_enumset1(A_176, B_177, A_176))), inference(superposition, [status(thm), theory('equality')], [c_1460, c_20])).
% 9.99/3.89  tff(c_1534, plain, (![A_178, B_179]: (k2_enumset1(A_178, A_178, B_179, A_178)=k2_tarski(A_178, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1492])).
% 9.99/3.89  tff(c_774, plain, (![D_37, F_118, A_34, B_35, C_36]: (k2_xboole_0(k2_enumset1(A_34, B_35, C_36, D_37), k1_tarski(F_118))=k3_enumset1(A_34, B_35, C_36, D_37, F_118))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_771])).
% 9.99/3.89  tff(c_1540, plain, (![A_178, B_179, F_118]: (k3_enumset1(A_178, A_178, B_179, A_178, F_118)=k2_xboole_0(k2_tarski(A_178, B_179), k1_tarski(F_118)))), inference(superposition, [status(thm), theory('equality')], [c_1534, c_774])).
% 9.99/3.89  tff(c_1684, plain, (![A_189, B_190, F_191]: (k3_enumset1(A_189, A_189, B_190, A_189, F_191)=k1_enumset1(A_189, B_190, F_191))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1540])).
% 9.99/3.89  tff(c_1724, plain, (![A_189, B_190, F_191]: (k2_enumset1(A_189, B_190, A_189, F_191)=k1_enumset1(A_189, B_190, F_191))), inference(superposition, [status(thm), theory('equality')], [c_1684, c_20])).
% 9.99/3.89  tff(c_24, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (k5_enumset1(A_43, A_43, B_44, C_45, D_46, E_47, F_48)=k4_enumset1(A_43, B_44, C_45, D_46, E_47, F_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.99/3.89  tff(c_1025, plain, (![C_147, F_149, E_148, G_150, B_152, D_151, A_146]: (k2_xboole_0(k3_enumset1(A_146, B_152, C_147, D_151, E_148), k2_tarski(F_149, G_150))=k5_enumset1(A_146, B_152, C_147, D_151, E_148, F_149, G_150))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.99/3.89  tff(c_1046, plain, (![D_37, F_149, G_150, A_34, B_35, C_36]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, F_149, G_150)=k2_xboole_0(k2_enumset1(A_34, B_35, C_36, D_37), k2_tarski(F_149, G_150)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1025])).
% 9.99/3.89  tff(c_1660, plain, (![D_184, F_185, G_187, C_188, B_186, A_183]: (k2_xboole_0(k2_enumset1(A_183, B_186, C_188, D_184), k2_tarski(F_185, G_187))=k4_enumset1(A_183, B_186, C_188, D_184, F_185, G_187))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1046])).
% 9.99/3.89  tff(c_1678, plain, (![A_31, F_185, C_33, G_187, B_32]: (k4_enumset1(A_31, A_31, B_32, C_33, F_185, G_187)=k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k2_tarski(F_185, G_187)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1660])).
% 9.99/3.89  tff(c_7928, plain, (![F_308, B_306, A_307, G_310, C_309]: (k2_xboole_0(k1_enumset1(A_307, B_306, C_309), k2_tarski(F_308, G_310))=k3_enumset1(A_307, B_306, C_309, F_308, G_310))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1678])).
% 9.99/3.89  tff(c_7979, plain, (![A_29, B_30, F_308, G_310]: (k3_enumset1(A_29, A_29, B_30, F_308, G_310)=k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(F_308, G_310)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7928])).
% 9.99/3.89  tff(c_7982, plain, (![A_29, B_30, F_308, G_310]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(F_308, G_310))=k2_enumset1(A_29, B_30, F_308, G_310))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_7979])).
% 9.99/3.89  tff(c_146, plain, (![B_70, C_71, A_72]: (k1_enumset1(B_70, C_71, A_72)=k1_enumset1(A_72, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.99/3.89  tff(c_186, plain, (![A_72, C_71]: (k1_enumset1(A_72, C_71, C_71)=k2_tarski(C_71, A_72))), inference(superposition, [status(thm), theory('equality')], [c_146, c_16])).
% 9.99/3.89  tff(c_1526, plain, (![A_176, B_177]: (k2_enumset1(A_176, A_176, B_177, A_176)=k2_tarski(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1492])).
% 9.99/3.89  tff(c_1240, plain, (![A_31, B_32, C_33, F_164]: (k3_enumset1(A_31, A_31, B_32, C_33, F_164)=k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k1_tarski(F_164)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1225])).
% 9.99/3.89  tff(c_1245, plain, (![A_31, B_32, C_33, F_164]: (k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k1_tarski(F_164))=k2_enumset1(A_31, B_32, C_33, F_164))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1240])).
% 9.99/3.89  tff(c_2203, plain, (![A_202, B_203, C_204, F_205]: (k2_xboole_0(k1_enumset1(A_202, B_203, C_204), k1_tarski(F_205))=k2_enumset1(A_202, B_203, C_204, F_205))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1240])).
% 9.99/3.89  tff(c_4297, plain, (![C_244, B_245, A_246, F_247]: (k2_xboole_0(k1_enumset1(C_244, B_245, A_246), k1_tarski(F_247))=k2_enumset1(A_246, B_245, C_244, F_247))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2203])).
% 9.99/3.89  tff(c_4780, plain, (![C_255, B_256, A_257, F_258]: (k2_enumset1(C_255, B_256, A_257, F_258)=k2_enumset1(A_257, B_256, C_255, F_258))), inference(superposition, [status(thm), theory('equality')], [c_1245, c_4297])).
% 9.99/3.89  tff(c_5073, plain, (![B_261, A_262]: (k2_enumset1(B_261, A_262, A_262, A_262)=k2_tarski(A_262, B_261))), inference(superposition, [status(thm), theory('equality')], [c_1526, c_4780])).
% 9.99/3.89  tff(c_5119, plain, (![B_261, A_262, F_118]: (k3_enumset1(B_261, A_262, A_262, A_262, F_118)=k2_xboole_0(k2_tarski(A_262, B_261), k1_tarski(F_118)))), inference(superposition, [status(thm), theory('equality')], [c_5073, c_774])).
% 9.99/3.89  tff(c_6978, plain, (![B_293, A_294, F_295]: (k3_enumset1(B_293, A_294, A_294, A_294, F_295)=k1_enumset1(A_294, B_293, F_295))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_5119])).
% 9.99/3.89  tff(c_1354, plain, (![A_172, B_173, C_174]: (k2_xboole_0(k1_tarski(A_172), k1_enumset1(B_173, C_174, A_172))=k1_enumset1(A_172, B_173, C_174))), inference(superposition, [status(thm), theory('equality')], [c_6, c_638])).
% 9.99/3.89  tff(c_1405, plain, (![C_33, A_31, B_32]: (k3_enumset1(C_33, A_31, A_31, B_32, C_33)=k1_enumset1(C_33, A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_575, c_1354])).
% 9.99/3.89  tff(c_7041, plain, (![F_295, A_294]: (k1_enumset1(F_295, A_294, A_294)=k1_enumset1(A_294, F_295, F_295))), inference(superposition, [status(thm), theory('equality')], [c_6978, c_1405])).
% 9.99/3.89  tff(c_7183, plain, (![F_295, A_294]: (k2_tarski(F_295, A_294)=k2_tarski(A_294, F_295))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_7041])).
% 9.99/3.89  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.99/3.89  tff(c_31, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 9.99/3.89  tff(c_7215, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7183, c_7183, c_31])).
% 9.99/3.89  tff(c_25441, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7982, c_7215])).
% 9.99/3.89  tff(c_25444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1724, c_25441])).
% 9.99/3.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.89  
% 9.99/3.89  Inference rules
% 9.99/3.89  ----------------------
% 9.99/3.89  #Ref     : 0
% 9.99/3.89  #Sup     : 5813
% 9.99/3.89  #Fact    : 0
% 9.99/3.89  #Define  : 0
% 9.99/3.89  #Split   : 0
% 9.99/3.89  #Chain   : 0
% 9.99/3.89  #Close   : 0
% 9.99/3.89  
% 9.99/3.89  Ordering : KBO
% 9.99/3.89  
% 9.99/3.89  Simplification rules
% 9.99/3.89  ----------------------
% 9.99/3.89  #Subsume      : 1016
% 9.99/3.89  #Demod        : 5686
% 9.99/3.89  #Tautology    : 4156
% 9.99/3.89  #SimpNegUnit  : 0
% 9.99/3.89  #BackRed      : 17
% 9.99/3.89  
% 9.99/3.89  #Partial instantiations: 0
% 9.99/3.89  #Strategies tried      : 1
% 9.99/3.89  
% 9.99/3.89  Timing (in seconds)
% 9.99/3.89  ----------------------
% 9.99/3.90  Preprocessing        : 0.31
% 9.99/3.90  Parsing              : 0.17
% 9.99/3.90  CNF conversion       : 0.02
% 9.99/3.90  Main loop            : 2.82
% 9.99/3.90  Inferencing          : 0.80
% 9.99/3.90  Reduction            : 1.51
% 9.99/3.90  Demodulation         : 1.35
% 9.99/3.90  BG Simplification    : 0.07
% 9.99/3.90  Subsumption          : 0.33
% 9.99/3.90  Abstraction          : 0.13
% 9.99/3.90  MUC search           : 0.00
% 9.99/3.90  Cooper               : 0.00
% 9.99/3.90  Total                : 3.17
% 9.99/3.90  Index Insertion      : 0.00
% 9.99/3.90  Index Deletion       : 0.00
% 9.99/3.90  Index Matching       : 0.00
% 9.99/3.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 12.15s
% Output     : CNFRefutation 12.26s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 502 expanded)
%              Number of leaves         :   31 ( 181 expanded)
%              Depth                    :   16
%              Number of atoms          :   75 ( 484 expanded)
%              Number of equality atoms :   74 ( 483 expanded)
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

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_57,C_59,B_58] : k1_enumset1(A_57,C_59,B_58) = k1_enumset1(A_57,B_58,C_59) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_566,plain,(
    ! [A_95,C_94,E_98,B_96,D_97] : k2_xboole_0(k1_tarski(A_95),k2_enumset1(B_96,C_94,D_97,E_98)) = k3_enumset1(A_95,B_96,C_94,D_97,E_98) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_575,plain,(
    ! [A_95,A_32,B_33,C_34] : k3_enumset1(A_95,A_32,A_32,B_33,C_34) = k2_xboole_0(k1_tarski(A_95),k1_enumset1(A_32,B_33,C_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_578,plain,(
    ! [A_99,A_100,B_101,C_102] : k3_enumset1(A_99,A_100,A_100,B_101,C_102) = k2_xboole_0(k1_tarski(A_99),k1_enumset1(A_100,B_101,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_20,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_588,plain,(
    ! [A_100,B_101,C_102] : k2_xboole_0(k1_tarski(A_100),k1_enumset1(A_100,B_101,C_102)) = k2_enumset1(A_100,A_100,B_101,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_20])).

tff(c_638,plain,(
    ! [A_103,B_104,C_105] : k2_xboole_0(k1_tarski(A_103),k1_enumset1(A_103,B_104,C_105)) = k1_enumset1(A_103,B_104,C_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_588])).

tff(c_651,plain,(
    ! [A_32,B_33,C_34] : k3_enumset1(A_32,A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_638])).

tff(c_50,plain,(
    ! [A_64,C_65,B_66] : k1_enumset1(A_64,C_65,B_66) = k1_enumset1(A_64,B_66,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [B_66,C_65] : k1_enumset1(B_66,C_65,B_66) = k2_tarski(B_66,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_899,plain,(
    ! [B_141,A_142,C_143] : k2_xboole_0(k1_tarski(B_141),k1_enumset1(A_142,B_141,C_143)) = k1_enumset1(B_141,C_143,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_638])).

tff(c_974,plain,(
    ! [B_144,A_145,C_146] : k3_enumset1(B_144,A_145,A_145,B_144,C_146) = k1_enumset1(B_144,C_146,A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_575])).

tff(c_995,plain,(
    ! [A_145,C_146] : k2_enumset1(A_145,A_145,A_145,C_146) = k1_enumset1(A_145,C_146,A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_20])).

tff(c_1019,plain,(
    ! [A_145,C_146] : k2_enumset1(A_145,A_145,A_145,C_146) = k2_tarski(A_145,C_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_995])).

tff(c_22,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_756,plain,(
    ! [E_121,A_122,D_123,B_120,F_119,C_124] : k2_xboole_0(k3_enumset1(A_122,B_120,C_124,D_123,E_121),k1_tarski(F_119)) = k4_enumset1(A_122,B_120,C_124,D_123,E_121,F_119) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_771,plain,(
    ! [A_35,B_36,C_37,D_38,F_119] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,F_119) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(F_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_756])).

tff(c_1210,plain,(
    ! [A_163,B_166,F_167,D_165,C_164] : k2_xboole_0(k2_enumset1(A_163,B_166,C_164,D_165),k1_tarski(F_167)) = k3_enumset1(A_163,B_166,C_164,D_165,F_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_1219,plain,(
    ! [A_145,C_146,F_167] : k3_enumset1(A_145,A_145,A_145,C_146,F_167) = k2_xboole_0(k2_tarski(A_145,C_146),k1_tarski(F_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_1210])).

tff(c_1228,plain,(
    ! [A_145,C_146,F_167] : k2_xboole_0(k2_tarski(A_145,C_146),k1_tarski(F_167)) = k1_enumset1(A_145,C_146,F_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1219])).

tff(c_8,plain,(
    ! [C_10,B_9,A_8] : k1_enumset1(C_10,B_9,A_8) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1242,plain,(
    ! [A_171,C_172,B_173] : k2_xboole_0(k1_tarski(A_171),k1_enumset1(C_172,B_173,A_171)) = k1_enumset1(A_171,B_173,C_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_638])).

tff(c_1340,plain,(
    ! [A_174,C_175,B_176] : k3_enumset1(A_174,C_175,C_175,B_176,A_174) = k1_enumset1(A_174,B_176,C_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_575])).

tff(c_1369,plain,(
    ! [C_175,B_176] : k2_enumset1(C_175,C_175,B_176,C_175) = k1_enumset1(C_175,B_176,C_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_20])).

tff(c_1403,plain,(
    ! [C_175,B_176] : k2_enumset1(C_175,C_175,B_176,C_175) = k2_tarski(C_175,B_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1369])).

tff(c_1225,plain,(
    ! [A_32,B_33,C_34,F_167] : k3_enumset1(A_32,A_32,B_33,C_34,F_167) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(F_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1210])).

tff(c_1826,plain,(
    ! [A_198,B_199,C_200,F_201] : k2_xboole_0(k1_enumset1(A_198,B_199,C_200),k1_tarski(F_201)) = k2_enumset1(A_198,B_199,C_200,F_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1225])).

tff(c_3603,plain,(
    ! [B_234,C_235,A_236,F_237] : k2_xboole_0(k1_enumset1(B_234,C_235,A_236),k1_tarski(F_237)) = k2_enumset1(A_236,B_234,C_235,F_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1826])).

tff(c_1230,plain,(
    ! [A_32,B_33,C_34,F_167] : k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(F_167)) = k2_enumset1(A_32,B_33,C_34,F_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1225])).

tff(c_3656,plain,(
    ! [B_238,C_239,A_240,F_241] : k2_enumset1(B_238,C_239,A_240,F_241) = k2_enumset1(A_240,B_238,C_239,F_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_3603,c_1230])).

tff(c_4359,plain,(
    ! [C_254,B_255] : k2_enumset1(C_254,B_255,C_254,C_254) = k2_tarski(C_254,B_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_3656])).

tff(c_774,plain,(
    ! [A_35,B_36,C_37,D_38,F_119] : k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k1_tarski(F_119)) = k3_enumset1(A_35,B_36,C_37,D_38,F_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_4394,plain,(
    ! [C_254,B_255,F_119] : k3_enumset1(C_254,B_255,C_254,C_254,F_119) = k2_xboole_0(k2_tarski(C_254,B_255),k1_tarski(F_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4359,c_774])).

tff(c_4465,plain,(
    ! [C_254,B_255,F_119] : k3_enumset1(C_254,B_255,C_254,C_254,F_119) = k1_enumset1(C_254,B_255,F_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_4394])).

tff(c_24,plain,(
    ! [C_46,E_48,F_49,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49) = k4_enumset1(A_44,B_45,C_46,D_47,E_48,F_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_50,B_51,G_56,E_54,C_52,D_53,F_55] : k6_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,G_56) = k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,G_56) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1025,plain,(
    ! [G_151,C_148,E_149,F_150,D_153,H_152,A_147,B_154] : k2_xboole_0(k4_enumset1(A_147,B_154,C_148,D_153,E_149,F_150),k2_tarski(G_151,H_152)) = k6_enumset1(A_147,B_154,C_148,D_153,E_149,F_150,G_151,H_152) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1034,plain,(
    ! [G_151,E_43,D_42,H_152,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,G_151,H_152) = k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k2_tarski(G_151,H_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1025])).

tff(c_1536,plain,(
    ! [E_188,B_183,G_184,A_182,D_187,H_185,C_186] : k2_xboole_0(k3_enumset1(A_182,B_183,C_186,D_187,E_188),k2_tarski(G_184,H_185)) = k5_enumset1(A_182,B_183,C_186,D_187,E_188,G_184,H_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1034])).

tff(c_1566,plain,(
    ! [A_35,G_184,B_36,C_37,D_38,H_185] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,G_184,H_185) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k2_tarski(G_184,H_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1536])).

tff(c_8109,plain,(
    ! [C_318,H_317,G_319,B_321,D_320,A_316] : k2_xboole_0(k2_enumset1(A_316,B_321,C_318,D_320),k2_tarski(G_319,H_317)) = k4_enumset1(A_316,B_321,C_318,D_320,G_319,H_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1566])).

tff(c_8184,plain,(
    ! [B_33,C_34,H_317,G_319,A_32] : k4_enumset1(A_32,A_32,B_33,C_34,G_319,H_317) = k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k2_tarski(G_319,H_317)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8109])).

tff(c_35667,plain,(
    ! [G_575,C_573,H_572,B_571,A_574] : k2_xboole_0(k1_enumset1(A_574,B_571,C_573),k2_tarski(G_575,H_572)) = k3_enumset1(A_574,B_571,C_573,G_575,H_572) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8184])).

tff(c_37480,plain,(
    ! [H_595,A_594,C_593,G_591,B_592] : k2_xboole_0(k1_enumset1(A_594,B_592,C_593),k2_tarski(G_591,H_595)) = k3_enumset1(B_592,C_593,A_594,G_591,H_595) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35667])).

tff(c_37540,plain,(
    ! [A_30,B_31,G_591,H_595] : k3_enumset1(A_30,B_31,A_30,G_591,H_595) = k2_xboole_0(k2_tarski(A_30,B_31),k2_tarski(G_591,H_595)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_37480])).

tff(c_146,plain,(
    ! [B_71,C_72,A_73] : k1_enumset1(B_71,C_72,A_73) = k1_enumset1(A_73,B_71,C_72) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_73,C_72] : k1_enumset1(A_73,C_72,C_72) = k2_tarski(C_72,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_16])).

tff(c_4481,plain,(
    ! [A_256,F_257] : k2_enumset1(A_256,F_257,F_257,F_257) = k2_tarski(F_257,A_256) ),
    inference(superposition,[status(thm),theory(equality)],[c_3656,c_1403])).

tff(c_4520,plain,(
    ! [A_256,F_257,F_119] : k3_enumset1(A_256,F_257,F_257,F_257,F_119) = k2_xboole_0(k2_tarski(F_257,A_256),k1_tarski(F_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4481,c_774])).

tff(c_6938,plain,(
    ! [A_299,F_300,F_301] : k3_enumset1(A_299,F_300,F_300,F_300,F_301) = k1_enumset1(F_300,A_299,F_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_4520])).

tff(c_1626,plain,(
    ! [A_192,B_193,C_194] : k2_xboole_0(k1_tarski(A_192),k1_enumset1(B_193,C_194,A_192)) = k1_enumset1(A_192,B_193,C_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_638])).

tff(c_1651,plain,(
    ! [A_192,B_193,C_194] : k3_enumset1(A_192,B_193,B_193,C_194,A_192) = k1_enumset1(A_192,B_193,C_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_575])).

tff(c_6997,plain,(
    ! [F_301,F_300] : k1_enumset1(F_301,F_300,F_300) = k1_enumset1(F_300,F_301,F_301) ),
    inference(superposition,[status(thm),theory(equality)],[c_6938,c_1651])).

tff(c_7142,plain,(
    ! [F_301,F_300] : k2_tarski(F_301,F_300) = k2_tarski(F_300,F_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_6997])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_7175,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7142,c_7142,c_31])).

tff(c_37557,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37540,c_7175])).

tff(c_37560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4465,c_37557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.15/5.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.79  
% 12.17/5.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.80  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 12.17/5.80  
% 12.17/5.80  %Foreground sorts:
% 12.17/5.80  
% 12.17/5.80  
% 12.17/5.80  %Background operators:
% 12.17/5.80  
% 12.17/5.80  
% 12.17/5.80  %Foreground operators:
% 12.17/5.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.17/5.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.17/5.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.17/5.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.17/5.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.17/5.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.17/5.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.17/5.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.17/5.80  tff('#skF_2', type, '#skF_2': $i).
% 12.17/5.80  tff('#skF_3', type, '#skF_3': $i).
% 12.17/5.80  tff('#skF_1', type, '#skF_1': $i).
% 12.17/5.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.17/5.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.17/5.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.17/5.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.17/5.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.17/5.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.17/5.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.17/5.80  
% 12.26/5.82  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 12.26/5.82  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.26/5.82  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 12.26/5.82  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 12.26/5.82  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.26/5.82  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 12.26/5.82  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 12.26/5.82  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 12.26/5.82  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 12.26/5.82  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 12.26/5.82  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 12.26/5.82  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 12.26/5.82  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 12.26/5.82  tff(c_28, plain, (![A_57, C_59, B_58]: (k1_enumset1(A_57, C_59, B_58)=k1_enumset1(A_57, B_58, C_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.26/5.82  tff(c_18, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.26/5.82  tff(c_566, plain, (![A_95, C_94, E_98, B_96, D_97]: (k2_xboole_0(k1_tarski(A_95), k2_enumset1(B_96, C_94, D_97, E_98))=k3_enumset1(A_95, B_96, C_94, D_97, E_98))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.26/5.82  tff(c_575, plain, (![A_95, A_32, B_33, C_34]: (k3_enumset1(A_95, A_32, A_32, B_33, C_34)=k2_xboole_0(k1_tarski(A_95), k1_enumset1(A_32, B_33, C_34)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 12.26/5.82  tff(c_578, plain, (![A_99, A_100, B_101, C_102]: (k3_enumset1(A_99, A_100, A_100, B_101, C_102)=k2_xboole_0(k1_tarski(A_99), k1_enumset1(A_100, B_101, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 12.26/5.82  tff(c_20, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.26/5.82  tff(c_588, plain, (![A_100, B_101, C_102]: (k2_xboole_0(k1_tarski(A_100), k1_enumset1(A_100, B_101, C_102))=k2_enumset1(A_100, A_100, B_101, C_102))), inference(superposition, [status(thm), theory('equality')], [c_578, c_20])).
% 12.26/5.82  tff(c_638, plain, (![A_103, B_104, C_105]: (k2_xboole_0(k1_tarski(A_103), k1_enumset1(A_103, B_104, C_105))=k1_enumset1(A_103, B_104, C_105))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_588])).
% 12.26/5.82  tff(c_651, plain, (![A_32, B_33, C_34]: (k3_enumset1(A_32, A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(superposition, [status(thm), theory('equality')], [c_575, c_638])).
% 12.26/5.82  tff(c_50, plain, (![A_64, C_65, B_66]: (k1_enumset1(A_64, C_65, B_66)=k1_enumset1(A_64, B_66, C_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.26/5.82  tff(c_16, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.26/5.82  tff(c_66, plain, (![B_66, C_65]: (k1_enumset1(B_66, C_65, B_66)=k2_tarski(B_66, C_65))), inference(superposition, [status(thm), theory('equality')], [c_50, c_16])).
% 12.26/5.82  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.26/5.82  tff(c_899, plain, (![B_141, A_142, C_143]: (k2_xboole_0(k1_tarski(B_141), k1_enumset1(A_142, B_141, C_143))=k1_enumset1(B_141, C_143, A_142))), inference(superposition, [status(thm), theory('equality')], [c_6, c_638])).
% 12.26/5.82  tff(c_974, plain, (![B_144, A_145, C_146]: (k3_enumset1(B_144, A_145, A_145, B_144, C_146)=k1_enumset1(B_144, C_146, A_145))), inference(superposition, [status(thm), theory('equality')], [c_899, c_575])).
% 12.26/5.82  tff(c_995, plain, (![A_145, C_146]: (k2_enumset1(A_145, A_145, A_145, C_146)=k1_enumset1(A_145, C_146, A_145))), inference(superposition, [status(thm), theory('equality')], [c_974, c_20])).
% 12.26/5.82  tff(c_1019, plain, (![A_145, C_146]: (k2_enumset1(A_145, A_145, A_145, C_146)=k2_tarski(A_145, C_146))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_995])).
% 12.26/5.82  tff(c_22, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.26/5.82  tff(c_756, plain, (![E_121, A_122, D_123, B_120, F_119, C_124]: (k2_xboole_0(k3_enumset1(A_122, B_120, C_124, D_123, E_121), k1_tarski(F_119))=k4_enumset1(A_122, B_120, C_124, D_123, E_121, F_119))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.26/5.82  tff(c_771, plain, (![A_35, B_36, C_37, D_38, F_119]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, F_119)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(F_119)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_756])).
% 12.26/5.82  tff(c_1210, plain, (![A_163, B_166, F_167, D_165, C_164]: (k2_xboole_0(k2_enumset1(A_163, B_166, C_164, D_165), k1_tarski(F_167))=k3_enumset1(A_163, B_166, C_164, D_165, F_167))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_771])).
% 12.26/5.82  tff(c_1219, plain, (![A_145, C_146, F_167]: (k3_enumset1(A_145, A_145, A_145, C_146, F_167)=k2_xboole_0(k2_tarski(A_145, C_146), k1_tarski(F_167)))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_1210])).
% 12.26/5.82  tff(c_1228, plain, (![A_145, C_146, F_167]: (k2_xboole_0(k2_tarski(A_145, C_146), k1_tarski(F_167))=k1_enumset1(A_145, C_146, F_167))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_1219])).
% 12.26/5.82  tff(c_8, plain, (![C_10, B_9, A_8]: (k1_enumset1(C_10, B_9, A_8)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.26/5.82  tff(c_1242, plain, (![A_171, C_172, B_173]: (k2_xboole_0(k1_tarski(A_171), k1_enumset1(C_172, B_173, A_171))=k1_enumset1(A_171, B_173, C_172))), inference(superposition, [status(thm), theory('equality')], [c_8, c_638])).
% 12.26/5.82  tff(c_1340, plain, (![A_174, C_175, B_176]: (k3_enumset1(A_174, C_175, C_175, B_176, A_174)=k1_enumset1(A_174, B_176, C_175))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_575])).
% 12.26/5.82  tff(c_1369, plain, (![C_175, B_176]: (k2_enumset1(C_175, C_175, B_176, C_175)=k1_enumset1(C_175, B_176, C_175))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_20])).
% 12.26/5.82  tff(c_1403, plain, (![C_175, B_176]: (k2_enumset1(C_175, C_175, B_176, C_175)=k2_tarski(C_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1369])).
% 12.26/5.82  tff(c_1225, plain, (![A_32, B_33, C_34, F_167]: (k3_enumset1(A_32, A_32, B_33, C_34, F_167)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(F_167)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1210])).
% 12.26/5.82  tff(c_1826, plain, (![A_198, B_199, C_200, F_201]: (k2_xboole_0(k1_enumset1(A_198, B_199, C_200), k1_tarski(F_201))=k2_enumset1(A_198, B_199, C_200, F_201))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1225])).
% 12.26/5.82  tff(c_3603, plain, (![B_234, C_235, A_236, F_237]: (k2_xboole_0(k1_enumset1(B_234, C_235, A_236), k1_tarski(F_237))=k2_enumset1(A_236, B_234, C_235, F_237))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1826])).
% 12.26/5.82  tff(c_1230, plain, (![A_32, B_33, C_34, F_167]: (k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(F_167))=k2_enumset1(A_32, B_33, C_34, F_167))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1225])).
% 12.26/5.82  tff(c_3656, plain, (![B_238, C_239, A_240, F_241]: (k2_enumset1(B_238, C_239, A_240, F_241)=k2_enumset1(A_240, B_238, C_239, F_241))), inference(superposition, [status(thm), theory('equality')], [c_3603, c_1230])).
% 12.26/5.82  tff(c_4359, plain, (![C_254, B_255]: (k2_enumset1(C_254, B_255, C_254, C_254)=k2_tarski(C_254, B_255))), inference(superposition, [status(thm), theory('equality')], [c_1403, c_3656])).
% 12.26/5.82  tff(c_774, plain, (![A_35, B_36, C_37, D_38, F_119]: (k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k1_tarski(F_119))=k3_enumset1(A_35, B_36, C_37, D_38, F_119))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_771])).
% 12.26/5.82  tff(c_4394, plain, (![C_254, B_255, F_119]: (k3_enumset1(C_254, B_255, C_254, C_254, F_119)=k2_xboole_0(k2_tarski(C_254, B_255), k1_tarski(F_119)))), inference(superposition, [status(thm), theory('equality')], [c_4359, c_774])).
% 12.26/5.82  tff(c_4465, plain, (![C_254, B_255, F_119]: (k3_enumset1(C_254, B_255, C_254, C_254, F_119)=k1_enumset1(C_254, B_255, F_119))), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_4394])).
% 12.26/5.82  tff(c_24, plain, (![C_46, E_48, F_49, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49)=k4_enumset1(A_44, B_45, C_46, D_47, E_48, F_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.26/5.82  tff(c_26, plain, (![A_50, B_51, G_56, E_54, C_52, D_53, F_55]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, G_56)=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, G_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.26/5.82  tff(c_1025, plain, (![G_151, C_148, E_149, F_150, D_153, H_152, A_147, B_154]: (k2_xboole_0(k4_enumset1(A_147, B_154, C_148, D_153, E_149, F_150), k2_tarski(G_151, H_152))=k6_enumset1(A_147, B_154, C_148, D_153, E_149, F_150, G_151, H_152))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.26/5.82  tff(c_1034, plain, (![G_151, E_43, D_42, H_152, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, G_151, H_152)=k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k2_tarski(G_151, H_152)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1025])).
% 12.26/5.82  tff(c_1536, plain, (![E_188, B_183, G_184, A_182, D_187, H_185, C_186]: (k2_xboole_0(k3_enumset1(A_182, B_183, C_186, D_187, E_188), k2_tarski(G_184, H_185))=k5_enumset1(A_182, B_183, C_186, D_187, E_188, G_184, H_185))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1034])).
% 12.26/5.82  tff(c_1566, plain, (![A_35, G_184, B_36, C_37, D_38, H_185]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, G_184, H_185)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k2_tarski(G_184, H_185)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1536])).
% 12.26/5.82  tff(c_8109, plain, (![C_318, H_317, G_319, B_321, D_320, A_316]: (k2_xboole_0(k2_enumset1(A_316, B_321, C_318, D_320), k2_tarski(G_319, H_317))=k4_enumset1(A_316, B_321, C_318, D_320, G_319, H_317))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1566])).
% 12.26/5.82  tff(c_8184, plain, (![B_33, C_34, H_317, G_319, A_32]: (k4_enumset1(A_32, A_32, B_33, C_34, G_319, H_317)=k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k2_tarski(G_319, H_317)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8109])).
% 12.26/5.82  tff(c_35667, plain, (![G_575, C_573, H_572, B_571, A_574]: (k2_xboole_0(k1_enumset1(A_574, B_571, C_573), k2_tarski(G_575, H_572))=k3_enumset1(A_574, B_571, C_573, G_575, H_572))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8184])).
% 12.26/5.82  tff(c_37480, plain, (![H_595, A_594, C_593, G_591, B_592]: (k2_xboole_0(k1_enumset1(A_594, B_592, C_593), k2_tarski(G_591, H_595))=k3_enumset1(B_592, C_593, A_594, G_591, H_595))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35667])).
% 12.26/5.82  tff(c_37540, plain, (![A_30, B_31, G_591, H_595]: (k3_enumset1(A_30, B_31, A_30, G_591, H_595)=k2_xboole_0(k2_tarski(A_30, B_31), k2_tarski(G_591, H_595)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_37480])).
% 12.26/5.82  tff(c_146, plain, (![B_71, C_72, A_73]: (k1_enumset1(B_71, C_72, A_73)=k1_enumset1(A_73, B_71, C_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.26/5.82  tff(c_186, plain, (![A_73, C_72]: (k1_enumset1(A_73, C_72, C_72)=k2_tarski(C_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_146, c_16])).
% 12.26/5.82  tff(c_4481, plain, (![A_256, F_257]: (k2_enumset1(A_256, F_257, F_257, F_257)=k2_tarski(F_257, A_256))), inference(superposition, [status(thm), theory('equality')], [c_3656, c_1403])).
% 12.26/5.82  tff(c_4520, plain, (![A_256, F_257, F_119]: (k3_enumset1(A_256, F_257, F_257, F_257, F_119)=k2_xboole_0(k2_tarski(F_257, A_256), k1_tarski(F_119)))), inference(superposition, [status(thm), theory('equality')], [c_4481, c_774])).
% 12.26/5.82  tff(c_6938, plain, (![A_299, F_300, F_301]: (k3_enumset1(A_299, F_300, F_300, F_300, F_301)=k1_enumset1(F_300, A_299, F_301))), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_4520])).
% 12.26/5.82  tff(c_1626, plain, (![A_192, B_193, C_194]: (k2_xboole_0(k1_tarski(A_192), k1_enumset1(B_193, C_194, A_192))=k1_enumset1(A_192, B_193, C_194))), inference(superposition, [status(thm), theory('equality')], [c_6, c_638])).
% 12.26/5.82  tff(c_1651, plain, (![A_192, B_193, C_194]: (k3_enumset1(A_192, B_193, B_193, C_194, A_192)=k1_enumset1(A_192, B_193, C_194))), inference(superposition, [status(thm), theory('equality')], [c_1626, c_575])).
% 12.26/5.82  tff(c_6997, plain, (![F_301, F_300]: (k1_enumset1(F_301, F_300, F_300)=k1_enumset1(F_300, F_301, F_301))), inference(superposition, [status(thm), theory('equality')], [c_6938, c_1651])).
% 12.26/5.82  tff(c_7142, plain, (![F_301, F_300]: (k2_tarski(F_301, F_300)=k2_tarski(F_300, F_301))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_6997])).
% 12.26/5.82  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.26/5.82  tff(c_31, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 12.26/5.82  tff(c_7175, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7142, c_7142, c_31])).
% 12.26/5.82  tff(c_37557, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37540, c_7175])).
% 12.26/5.82  tff(c_37560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_4465, c_37557])).
% 12.26/5.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.26/5.82  
% 12.26/5.82  Inference rules
% 12.26/5.82  ----------------------
% 12.26/5.82  #Ref     : 0
% 12.26/5.82  #Sup     : 8834
% 12.26/5.82  #Fact    : 0
% 12.26/5.82  #Define  : 0
% 12.26/5.82  #Split   : 0
% 12.26/5.82  #Chain   : 0
% 12.26/5.82  #Close   : 0
% 12.26/5.82  
% 12.26/5.82  Ordering : KBO
% 12.26/5.82  
% 12.26/5.82  Simplification rules
% 12.26/5.82  ----------------------
% 12.26/5.82  #Subsume      : 1925
% 12.26/5.82  #Demod        : 7757
% 12.26/5.82  #Tautology    : 5936
% 12.26/5.82  #SimpNegUnit  : 0
% 12.26/5.82  #BackRed      : 16
% 12.26/5.82  
% 12.26/5.82  #Partial instantiations: 0
% 12.26/5.82  #Strategies tried      : 1
% 12.26/5.82  
% 12.26/5.82  Timing (in seconds)
% 12.26/5.82  ----------------------
% 12.31/5.82  Preprocessing        : 0.29
% 12.31/5.82  Parsing              : 0.15
% 12.31/5.82  CNF conversion       : 0.02
% 12.31/5.82  Main loop            : 4.69
% 12.31/5.82  Inferencing          : 0.99
% 12.31/5.82  Reduction            : 2.93
% 12.31/5.82  Demodulation         : 2.73
% 12.31/5.82  BG Simplification    : 0.08
% 12.31/5.82  Subsumption          : 0.53
% 12.31/5.82  Abstraction          : 0.18
% 12.31/5.82  MUC search           : 0.00
% 12.31/5.82  Cooper               : 0.00
% 12.31/5.82  Total                : 5.02
% 12.31/5.82  Index Insertion      : 0.00
% 12.31/5.82  Index Deletion       : 0.00
% 12.31/5.82  Index Matching       : 0.00
% 12.31/5.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

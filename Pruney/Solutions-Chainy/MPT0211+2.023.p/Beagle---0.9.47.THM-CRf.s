%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 20.04s
% Output     : CNFRefutation 20.04s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 519 expanded)
%              Number of leaves         :   33 ( 188 expanded)
%              Depth                    :   18
%              Number of atoms          :   75 ( 500 expanded)
%              Number of equality atoms :   74 ( 499 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_632,plain,(
    ! [A_116,C_117,D_118,B_119] : k2_enumset1(A_116,C_117,D_118,B_119) = k2_enumset1(A_116,B_119,C_117,D_118) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_52,B_53,C_54] : k2_enumset1(A_52,A_52,B_53,C_54) = k1_enumset1(A_52,B_53,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_793,plain,(
    ! [B_120,C_121,D_122] : k2_enumset1(B_120,C_121,D_122,B_120) = k1_enumset1(B_120,C_121,D_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_26])).

tff(c_149,plain,(
    ! [B_91,D_92,C_93,A_94] : k2_enumset1(B_91,D_92,C_93,A_94) = k2_enumset1(A_94,B_91,C_93,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [B_91,D_92,C_93] : k2_enumset1(B_91,D_92,C_93,B_91) = k1_enumset1(B_91,C_93,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_26])).

tff(c_825,plain,(
    ! [B_120,D_122,C_121] : k1_enumset1(B_120,D_122,C_121) = k1_enumset1(B_120,C_121,D_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_165])).

tff(c_8,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_55,B_56,C_57,D_58] : k3_enumset1(A_55,A_55,B_56,C_57,D_58) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [D_101,C_102,B_103,A_104] : k2_enumset1(D_101,C_102,B_103,A_104) = k2_enumset1(A_104,B_103,C_102,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_376,plain,(
    ! [D_105,C_106,B_107] : k2_enumset1(D_105,C_106,B_107,B_107) = k1_enumset1(B_107,C_106,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_26])).

tff(c_393,plain,(
    ! [B_107,C_106] : k1_enumset1(B_107,C_106,B_107) = k1_enumset1(B_107,B_107,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_165])).

tff(c_439,plain,(
    ! [B_107,C_106] : k1_enumset1(B_107,C_106,B_107) = k2_tarski(B_107,C_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_393])).

tff(c_30,plain,(
    ! [D_62,A_59,C_61,E_63,B_60] : k4_enumset1(A_59,A_59,B_60,C_61,D_62,E_63) = k3_enumset1(A_59,B_60,C_61,D_62,E_63) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [B_16,D_18,C_17,A_15] : k2_enumset1(B_16,D_18,C_17,A_15) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_828,plain,(
    ! [B_120,D_122,C_121] : k2_enumset1(B_120,B_120,D_122,C_121) = k1_enumset1(B_120,C_121,D_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_12])).

tff(c_32,plain,(
    ! [D_67,E_68,C_66,A_64,F_69,B_65] : k5_enumset1(A_64,A_64,B_65,C_66,D_67,E_68,F_69) = k4_enumset1(A_64,B_65,C_66,D_67,E_68,F_69) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [F_75,D_73,A_70,G_76,E_74,C_72,B_71] : k6_enumset1(A_70,A_70,B_71,C_72,D_73,E_74,F_75,G_76) = k5_enumset1(A_70,B_71,C_72,D_73,E_74,F_75,G_76) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [D_44,F_46,C_43,H_48,A_41,B_42,G_47,E_45] : k2_xboole_0(k5_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47),k1_tarski(H_48)) = k6_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47,H_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1904,plain,(
    ! [F_185,A_187,D_189,I_190,B_184,C_186,H_188,E_183,G_191] : k2_xboole_0(k6_enumset1(A_187,B_184,C_186,D_189,E_183,F_185,G_191,H_188),k1_tarski(I_190)) = k7_enumset1(A_187,B_184,C_186,D_189,E_183,F_185,G_191,H_188,I_190) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1913,plain,(
    ! [F_75,D_73,A_70,G_76,E_74,I_190,C_72,B_71] : k7_enumset1(A_70,A_70,B_71,C_72,D_73,E_74,F_75,G_76,I_190) = k2_xboole_0(k5_enumset1(A_70,B_71,C_72,D_73,E_74,F_75,G_76),k1_tarski(I_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1904])).

tff(c_1916,plain,(
    ! [F_75,D_73,A_70,G_76,E_74,I_190,C_72,B_71] : k7_enumset1(A_70,A_70,B_71,C_72,D_73,E_74,F_75,G_76,I_190) = k6_enumset1(A_70,B_71,C_72,D_73,E_74,F_75,G_76,I_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1913])).

tff(c_1883,plain,(
    ! [E_177,G_176,D_179,B_178,I_180,A_182,H_181,C_174,F_175] : k2_xboole_0(k5_enumset1(A_182,B_178,C_174,D_179,E_177,F_175,G_176),k2_tarski(H_181,I_180)) = k7_enumset1(A_182,B_178,C_174,D_179,E_177,F_175,G_176,H_181,I_180) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1892,plain,(
    ! [D_67,I_180,H_181,E_68,C_66,A_64,F_69,B_65] : k7_enumset1(A_64,A_64,B_65,C_66,D_67,E_68,F_69,H_181,I_180) = k2_xboole_0(k4_enumset1(A_64,B_65,C_66,D_67,E_68,F_69),k2_tarski(H_181,I_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1883])).

tff(c_7712,plain,(
    ! [H_269,A_271,B_267,I_270,F_273,D_266,C_268,E_272] : k2_xboole_0(k4_enumset1(A_271,B_267,C_268,D_266,E_272,F_273),k2_tarski(H_269,I_270)) = k6_enumset1(A_271,B_267,C_268,D_266,E_272,F_273,H_269,I_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1892])).

tff(c_7721,plain,(
    ! [H_269,D_62,A_59,I_270,C_61,E_63,B_60] : k6_enumset1(A_59,A_59,B_60,C_61,D_62,E_63,H_269,I_270) = k2_xboole_0(k3_enumset1(A_59,B_60,C_61,D_62,E_63),k2_tarski(H_269,I_270)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7712])).

tff(c_7767,plain,(
    ! [B_289,I_293,A_288,H_292,D_290,E_291,C_287] : k2_xboole_0(k3_enumset1(A_288,B_289,C_287,D_290,E_291),k2_tarski(H_292,I_293)) = k5_enumset1(A_288,B_289,C_287,D_290,E_291,H_292,I_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7721])).

tff(c_7776,plain,(
    ! [I_293,B_56,H_292,C_57,A_55,D_58] : k5_enumset1(A_55,A_55,B_56,C_57,D_58,H_292,I_293) = k2_xboole_0(k2_enumset1(A_55,B_56,C_57,D_58),k2_tarski(H_292,I_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7767])).

tff(c_9727,plain,(
    ! [I_351,A_350,D_348,H_349,B_347,C_352] : k2_xboole_0(k2_enumset1(A_350,B_347,C_352,D_348),k2_tarski(H_349,I_351)) = k4_enumset1(A_350,B_347,C_352,D_348,H_349,I_351) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_7776])).

tff(c_9832,plain,(
    ! [C_121,I_351,D_122,H_349,B_120] : k4_enumset1(B_120,B_120,D_122,C_121,H_349,I_351) = k2_xboole_0(k1_enumset1(B_120,C_121,D_122),k2_tarski(H_349,I_351)) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_9727])).

tff(c_18571,plain,(
    ! [I_494,H_497,B_493,D_495,C_496] : k2_xboole_0(k1_enumset1(B_493,C_496,D_495),k2_tarski(H_497,I_494)) = k3_enumset1(B_493,D_495,C_496,H_497,I_494) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9832])).

tff(c_18622,plain,(
    ! [B_107,C_106,H_497,I_494] : k3_enumset1(B_107,B_107,C_106,H_497,I_494) = k2_xboole_0(k2_tarski(B_107,C_106),k2_tarski(H_497,I_494)) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_18571])).

tff(c_18635,plain,(
    ! [B_107,C_106,H_497,I_494] : k2_xboole_0(k2_tarski(B_107,C_106),k2_tarski(H_497,I_494)) = k2_enumset1(B_107,C_106,H_497,I_494) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18622])).

tff(c_321,plain,(
    ! [D_101,C_102,B_103] : k2_enumset1(D_101,C_102,B_103,B_103) = k1_enumset1(B_103,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_26])).

tff(c_465,plain,(
    ! [A_110,D_111,C_112,B_113] : k2_enumset1(A_110,D_111,C_112,B_113) = k2_enumset1(A_110,B_113,C_112,D_111) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_543,plain,(
    ! [D_101,B_103,C_102] : k2_enumset1(D_101,B_103,B_103,C_102) = k1_enumset1(B_103,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_465])).

tff(c_403,plain,(
    ! [C_106,B_107] : k1_enumset1(C_106,B_107,B_107) = k1_enumset1(B_107,C_106,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_26])).

tff(c_1867,plain,(
    ! [H_168,C_169,E_166,D_170,A_167,G_172,B_173,F_171] : k2_xboole_0(k5_enumset1(A_167,B_173,C_169,D_170,E_166,F_171,G_172),k1_tarski(H_168)) = k6_enumset1(A_167,B_173,C_169,D_170,E_166,F_171,G_172,H_168) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1876,plain,(
    ! [H_168,D_67,E_68,C_66,A_64,F_69,B_65] : k6_enumset1(A_64,A_64,B_65,C_66,D_67,E_68,F_69,H_168) = k2_xboole_0(k4_enumset1(A_64,B_65,C_66,D_67,E_68,F_69),k1_tarski(H_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1867])).

tff(c_6512,plain,(
    ! [C_238,A_239,H_237,B_236,E_240,D_235,F_241] : k2_xboole_0(k4_enumset1(A_239,B_236,C_238,D_235,E_240,F_241),k1_tarski(H_237)) = k5_enumset1(A_239,B_236,C_238,D_235,E_240,F_241,H_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1876])).

tff(c_6521,plain,(
    ! [D_62,H_237,A_59,C_61,E_63,B_60] : k5_enumset1(A_59,A_59,B_60,C_61,D_62,E_63,H_237) = k2_xboole_0(k3_enumset1(A_59,B_60,C_61,D_62,E_63),k1_tarski(H_237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6512])).

tff(c_7729,plain,(
    ! [E_278,C_274,B_276,A_275,D_277,H_279] : k2_xboole_0(k3_enumset1(A_275,B_276,C_274,D_277,E_278),k1_tarski(H_279)) = k4_enumset1(A_275,B_276,C_274,D_277,E_278,H_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6521])).

tff(c_7738,plain,(
    ! [B_56,C_57,A_55,D_58,H_279] : k4_enumset1(A_55,A_55,B_56,C_57,D_58,H_279) = k2_xboole_0(k2_enumset1(A_55,B_56,C_57,D_58),k1_tarski(H_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7729])).

tff(c_7784,plain,(
    ! [H_294,D_296,A_297,B_295,C_298] : k2_xboole_0(k2_enumset1(A_297,B_295,C_298,D_296),k1_tarski(H_294)) = k3_enumset1(A_297,B_295,C_298,D_296,H_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7738])).

tff(c_7922,plain,(
    ! [A_52,B_53,C_54,H_294] : k3_enumset1(A_52,A_52,B_53,C_54,H_294) = k2_xboole_0(k1_enumset1(A_52,B_53,C_54),k1_tarski(H_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7784])).

tff(c_8077,plain,(
    ! [A_304,B_305,C_306,H_307] : k2_xboole_0(k1_enumset1(A_304,B_305,C_306),k1_tarski(H_307)) = k2_enumset1(A_304,B_305,C_306,H_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7922])).

tff(c_8092,plain,(
    ! [C_106,B_107,H_307] : k2_xboole_0(k1_enumset1(C_106,B_107,B_107),k1_tarski(H_307)) = k2_enumset1(B_107,C_106,C_106,H_307) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_8077])).

tff(c_8149,plain,(
    ! [C_316,B_317,H_318] : k2_xboole_0(k1_enumset1(C_316,B_317,B_317),k1_tarski(H_318)) = k1_enumset1(C_316,H_318,B_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_8092])).

tff(c_7926,plain,(
    ! [A_52,B_53,C_54,H_294] : k2_xboole_0(k1_enumset1(A_52,B_53,C_54),k1_tarski(H_294)) = k2_enumset1(A_52,B_53,C_54,H_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7922])).

tff(c_8208,plain,(
    ! [C_325,B_326,H_327] : k2_enumset1(C_325,B_326,B_326,H_327) = k1_enumset1(C_325,H_327,B_326) ),
    inference(superposition,[status(thm),theory(equality)],[c_8149,c_7926])).

tff(c_1926,plain,(
    ! [B_192,A_193,D_194,C_195] : k2_enumset1(B_192,A_193,D_194,C_195) = k2_enumset1(A_193,B_192,C_195,D_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_12])).

tff(c_2158,plain,(
    ! [C_102,D_101,B_103] : k2_enumset1(C_102,D_101,B_103,B_103) = k1_enumset1(B_103,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1926])).

tff(c_8281,plain,(
    ! [H_327,C_325] : k1_enumset1(H_327,C_325,H_327) = k1_enumset1(C_325,H_327,H_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_8208,c_2158])).

tff(c_8526,plain,(
    ! [C_325,H_327] : k1_enumset1(C_325,H_327,H_327) = k2_tarski(H_327,C_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_8281])).

tff(c_8548,plain,(
    ! [C_106,B_107] : k2_tarski(C_106,B_107) = k2_tarski(B_107,C_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8526,c_8526,c_403])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_900,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_36])).

tff(c_8582,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8548,c_8548,c_900])).

tff(c_56180,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18635,c_8582])).

tff(c_56183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_26,c_8,c_10,c_56180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.04/11.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.04/11.87  
% 20.04/11.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.04/11.87  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 20.04/11.87  
% 20.04/11.87  %Foreground sorts:
% 20.04/11.87  
% 20.04/11.87  
% 20.04/11.87  %Background operators:
% 20.04/11.87  
% 20.04/11.87  
% 20.04/11.87  %Foreground operators:
% 20.04/11.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.04/11.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.04/11.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.04/11.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.04/11.87  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.04/11.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.04/11.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.04/11.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.04/11.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.04/11.87  tff('#skF_2', type, '#skF_2': $i).
% 20.04/11.87  tff('#skF_3', type, '#skF_3': $i).
% 20.04/11.87  tff('#skF_1', type, '#skF_1': $i).
% 20.04/11.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.04/11.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.04/11.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.04/11.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.04/11.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.04/11.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.04/11.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.04/11.87  
% 20.04/11.89  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 20.04/11.89  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 20.04/11.89  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 20.04/11.89  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 20.04/11.89  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 20.04/11.89  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 20.04/11.89  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 20.04/11.89  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 20.04/11.89  tff(f_57, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 20.04/11.89  tff(f_59, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 20.04/11.89  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 20.04/11.89  tff(f_43, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 20.04/11.89  tff(f_41, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 20.04/11.89  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 20.04/11.89  tff(c_632, plain, (![A_116, C_117, D_118, B_119]: (k2_enumset1(A_116, C_117, D_118, B_119)=k2_enumset1(A_116, B_119, C_117, D_118))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.04/11.89  tff(c_26, plain, (![A_52, B_53, C_54]: (k2_enumset1(A_52, A_52, B_53, C_54)=k1_enumset1(A_52, B_53, C_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.04/11.89  tff(c_793, plain, (![B_120, C_121, D_122]: (k2_enumset1(B_120, C_121, D_122, B_120)=k1_enumset1(B_120, C_121, D_122))), inference(superposition, [status(thm), theory('equality')], [c_632, c_26])).
% 20.04/11.89  tff(c_149, plain, (![B_91, D_92, C_93, A_94]: (k2_enumset1(B_91, D_92, C_93, A_94)=k2_enumset1(A_94, B_91, C_93, D_92))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.04/11.89  tff(c_165, plain, (![B_91, D_92, C_93]: (k2_enumset1(B_91, D_92, C_93, B_91)=k1_enumset1(B_91, C_93, D_92))), inference(superposition, [status(thm), theory('equality')], [c_149, c_26])).
% 20.04/11.89  tff(c_825, plain, (![B_120, D_122, C_121]: (k1_enumset1(B_120, D_122, C_121)=k1_enumset1(B_120, C_121, D_122))), inference(superposition, [status(thm), theory('equality')], [c_793, c_165])).
% 20.04/11.89  tff(c_8, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.04/11.89  tff(c_10, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.04/11.89  tff(c_28, plain, (![A_55, B_56, C_57, D_58]: (k3_enumset1(A_55, A_55, B_56, C_57, D_58)=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.04/11.89  tff(c_24, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.04/11.89  tff(c_277, plain, (![D_101, C_102, B_103, A_104]: (k2_enumset1(D_101, C_102, B_103, A_104)=k2_enumset1(A_104, B_103, C_102, D_101))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.04/11.89  tff(c_376, plain, (![D_105, C_106, B_107]: (k2_enumset1(D_105, C_106, B_107, B_107)=k1_enumset1(B_107, C_106, D_105))), inference(superposition, [status(thm), theory('equality')], [c_277, c_26])).
% 20.04/11.89  tff(c_393, plain, (![B_107, C_106]: (k1_enumset1(B_107, C_106, B_107)=k1_enumset1(B_107, B_107, C_106))), inference(superposition, [status(thm), theory('equality')], [c_376, c_165])).
% 20.04/11.89  tff(c_439, plain, (![B_107, C_106]: (k1_enumset1(B_107, C_106, B_107)=k2_tarski(B_107, C_106))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_393])).
% 20.04/11.89  tff(c_30, plain, (![D_62, A_59, C_61, E_63, B_60]: (k4_enumset1(A_59, A_59, B_60, C_61, D_62, E_63)=k3_enumset1(A_59, B_60, C_61, D_62, E_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.04/11.89  tff(c_12, plain, (![B_16, D_18, C_17, A_15]: (k2_enumset1(B_16, D_18, C_17, A_15)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.04/11.89  tff(c_828, plain, (![B_120, D_122, C_121]: (k2_enumset1(B_120, B_120, D_122, C_121)=k1_enumset1(B_120, C_121, D_122))), inference(superposition, [status(thm), theory('equality')], [c_793, c_12])).
% 20.04/11.89  tff(c_32, plain, (![D_67, E_68, C_66, A_64, F_69, B_65]: (k5_enumset1(A_64, A_64, B_65, C_66, D_67, E_68, F_69)=k4_enumset1(A_64, B_65, C_66, D_67, E_68, F_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.04/11.89  tff(c_34, plain, (![F_75, D_73, A_70, G_76, E_74, C_72, B_71]: (k6_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75, G_76)=k5_enumset1(A_70, B_71, C_72, D_73, E_74, F_75, G_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.04/11.89  tff(c_20, plain, (![D_44, F_46, C_43, H_48, A_41, B_42, G_47, E_45]: (k2_xboole_0(k5_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47), k1_tarski(H_48))=k6_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47, H_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.04/11.89  tff(c_1904, plain, (![F_185, A_187, D_189, I_190, B_184, C_186, H_188, E_183, G_191]: (k2_xboole_0(k6_enumset1(A_187, B_184, C_186, D_189, E_183, F_185, G_191, H_188), k1_tarski(I_190))=k7_enumset1(A_187, B_184, C_186, D_189, E_183, F_185, G_191, H_188, I_190))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.04/11.89  tff(c_1913, plain, (![F_75, D_73, A_70, G_76, E_74, I_190, C_72, B_71]: (k7_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75, G_76, I_190)=k2_xboole_0(k5_enumset1(A_70, B_71, C_72, D_73, E_74, F_75, G_76), k1_tarski(I_190)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1904])).
% 20.04/11.89  tff(c_1916, plain, (![F_75, D_73, A_70, G_76, E_74, I_190, C_72, B_71]: (k7_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75, G_76, I_190)=k6_enumset1(A_70, B_71, C_72, D_73, E_74, F_75, G_76, I_190))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1913])).
% 20.04/11.89  tff(c_1883, plain, (![E_177, G_176, D_179, B_178, I_180, A_182, H_181, C_174, F_175]: (k2_xboole_0(k5_enumset1(A_182, B_178, C_174, D_179, E_177, F_175, G_176), k2_tarski(H_181, I_180))=k7_enumset1(A_182, B_178, C_174, D_179, E_177, F_175, G_176, H_181, I_180))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.04/11.89  tff(c_1892, plain, (![D_67, I_180, H_181, E_68, C_66, A_64, F_69, B_65]: (k7_enumset1(A_64, A_64, B_65, C_66, D_67, E_68, F_69, H_181, I_180)=k2_xboole_0(k4_enumset1(A_64, B_65, C_66, D_67, E_68, F_69), k2_tarski(H_181, I_180)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1883])).
% 20.04/11.89  tff(c_7712, plain, (![H_269, A_271, B_267, I_270, F_273, D_266, C_268, E_272]: (k2_xboole_0(k4_enumset1(A_271, B_267, C_268, D_266, E_272, F_273), k2_tarski(H_269, I_270))=k6_enumset1(A_271, B_267, C_268, D_266, E_272, F_273, H_269, I_270))), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1892])).
% 20.04/11.89  tff(c_7721, plain, (![H_269, D_62, A_59, I_270, C_61, E_63, B_60]: (k6_enumset1(A_59, A_59, B_60, C_61, D_62, E_63, H_269, I_270)=k2_xboole_0(k3_enumset1(A_59, B_60, C_61, D_62, E_63), k2_tarski(H_269, I_270)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7712])).
% 20.04/11.89  tff(c_7767, plain, (![B_289, I_293, A_288, H_292, D_290, E_291, C_287]: (k2_xboole_0(k3_enumset1(A_288, B_289, C_287, D_290, E_291), k2_tarski(H_292, I_293))=k5_enumset1(A_288, B_289, C_287, D_290, E_291, H_292, I_293))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7721])).
% 20.04/11.89  tff(c_7776, plain, (![I_293, B_56, H_292, C_57, A_55, D_58]: (k5_enumset1(A_55, A_55, B_56, C_57, D_58, H_292, I_293)=k2_xboole_0(k2_enumset1(A_55, B_56, C_57, D_58), k2_tarski(H_292, I_293)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7767])).
% 20.04/11.89  tff(c_9727, plain, (![I_351, A_350, D_348, H_349, B_347, C_352]: (k2_xboole_0(k2_enumset1(A_350, B_347, C_352, D_348), k2_tarski(H_349, I_351))=k4_enumset1(A_350, B_347, C_352, D_348, H_349, I_351))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_7776])).
% 20.04/11.89  tff(c_9832, plain, (![C_121, I_351, D_122, H_349, B_120]: (k4_enumset1(B_120, B_120, D_122, C_121, H_349, I_351)=k2_xboole_0(k1_enumset1(B_120, C_121, D_122), k2_tarski(H_349, I_351)))), inference(superposition, [status(thm), theory('equality')], [c_828, c_9727])).
% 20.04/11.89  tff(c_18571, plain, (![I_494, H_497, B_493, D_495, C_496]: (k2_xboole_0(k1_enumset1(B_493, C_496, D_495), k2_tarski(H_497, I_494))=k3_enumset1(B_493, D_495, C_496, H_497, I_494))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9832])).
% 20.04/11.89  tff(c_18622, plain, (![B_107, C_106, H_497, I_494]: (k3_enumset1(B_107, B_107, C_106, H_497, I_494)=k2_xboole_0(k2_tarski(B_107, C_106), k2_tarski(H_497, I_494)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_18571])).
% 20.04/11.89  tff(c_18635, plain, (![B_107, C_106, H_497, I_494]: (k2_xboole_0(k2_tarski(B_107, C_106), k2_tarski(H_497, I_494))=k2_enumset1(B_107, C_106, H_497, I_494))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18622])).
% 20.04/11.89  tff(c_321, plain, (![D_101, C_102, B_103]: (k2_enumset1(D_101, C_102, B_103, B_103)=k1_enumset1(B_103, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_277, c_26])).
% 20.04/11.89  tff(c_465, plain, (![A_110, D_111, C_112, B_113]: (k2_enumset1(A_110, D_111, C_112, B_113)=k2_enumset1(A_110, B_113, C_112, D_111))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.04/11.89  tff(c_543, plain, (![D_101, B_103, C_102]: (k2_enumset1(D_101, B_103, B_103, C_102)=k1_enumset1(B_103, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_321, c_465])).
% 20.04/11.89  tff(c_403, plain, (![C_106, B_107]: (k1_enumset1(C_106, B_107, B_107)=k1_enumset1(B_107, C_106, C_106))), inference(superposition, [status(thm), theory('equality')], [c_376, c_26])).
% 20.04/11.89  tff(c_1867, plain, (![H_168, C_169, E_166, D_170, A_167, G_172, B_173, F_171]: (k2_xboole_0(k5_enumset1(A_167, B_173, C_169, D_170, E_166, F_171, G_172), k1_tarski(H_168))=k6_enumset1(A_167, B_173, C_169, D_170, E_166, F_171, G_172, H_168))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.04/11.89  tff(c_1876, plain, (![H_168, D_67, E_68, C_66, A_64, F_69, B_65]: (k6_enumset1(A_64, A_64, B_65, C_66, D_67, E_68, F_69, H_168)=k2_xboole_0(k4_enumset1(A_64, B_65, C_66, D_67, E_68, F_69), k1_tarski(H_168)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1867])).
% 20.04/11.89  tff(c_6512, plain, (![C_238, A_239, H_237, B_236, E_240, D_235, F_241]: (k2_xboole_0(k4_enumset1(A_239, B_236, C_238, D_235, E_240, F_241), k1_tarski(H_237))=k5_enumset1(A_239, B_236, C_238, D_235, E_240, F_241, H_237))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1876])).
% 20.04/11.89  tff(c_6521, plain, (![D_62, H_237, A_59, C_61, E_63, B_60]: (k5_enumset1(A_59, A_59, B_60, C_61, D_62, E_63, H_237)=k2_xboole_0(k3_enumset1(A_59, B_60, C_61, D_62, E_63), k1_tarski(H_237)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6512])).
% 20.04/11.89  tff(c_7729, plain, (![E_278, C_274, B_276, A_275, D_277, H_279]: (k2_xboole_0(k3_enumset1(A_275, B_276, C_274, D_277, E_278), k1_tarski(H_279))=k4_enumset1(A_275, B_276, C_274, D_277, E_278, H_279))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6521])).
% 20.04/11.89  tff(c_7738, plain, (![B_56, C_57, A_55, D_58, H_279]: (k4_enumset1(A_55, A_55, B_56, C_57, D_58, H_279)=k2_xboole_0(k2_enumset1(A_55, B_56, C_57, D_58), k1_tarski(H_279)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7729])).
% 20.04/11.89  tff(c_7784, plain, (![H_294, D_296, A_297, B_295, C_298]: (k2_xboole_0(k2_enumset1(A_297, B_295, C_298, D_296), k1_tarski(H_294))=k3_enumset1(A_297, B_295, C_298, D_296, H_294))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7738])).
% 20.04/11.89  tff(c_7922, plain, (![A_52, B_53, C_54, H_294]: (k3_enumset1(A_52, A_52, B_53, C_54, H_294)=k2_xboole_0(k1_enumset1(A_52, B_53, C_54), k1_tarski(H_294)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7784])).
% 20.04/11.89  tff(c_8077, plain, (![A_304, B_305, C_306, H_307]: (k2_xboole_0(k1_enumset1(A_304, B_305, C_306), k1_tarski(H_307))=k2_enumset1(A_304, B_305, C_306, H_307))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7922])).
% 20.04/11.89  tff(c_8092, plain, (![C_106, B_107, H_307]: (k2_xboole_0(k1_enumset1(C_106, B_107, B_107), k1_tarski(H_307))=k2_enumset1(B_107, C_106, C_106, H_307))), inference(superposition, [status(thm), theory('equality')], [c_403, c_8077])).
% 20.04/11.89  tff(c_8149, plain, (![C_316, B_317, H_318]: (k2_xboole_0(k1_enumset1(C_316, B_317, B_317), k1_tarski(H_318))=k1_enumset1(C_316, H_318, B_317))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_8092])).
% 20.04/11.89  tff(c_7926, plain, (![A_52, B_53, C_54, H_294]: (k2_xboole_0(k1_enumset1(A_52, B_53, C_54), k1_tarski(H_294))=k2_enumset1(A_52, B_53, C_54, H_294))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7922])).
% 20.04/11.89  tff(c_8208, plain, (![C_325, B_326, H_327]: (k2_enumset1(C_325, B_326, B_326, H_327)=k1_enumset1(C_325, H_327, B_326))), inference(superposition, [status(thm), theory('equality')], [c_8149, c_7926])).
% 20.04/11.89  tff(c_1926, plain, (![B_192, A_193, D_194, C_195]: (k2_enumset1(B_192, A_193, D_194, C_195)=k2_enumset1(A_193, B_192, C_195, D_194))), inference(superposition, [status(thm), theory('equality')], [c_632, c_12])).
% 20.04/11.89  tff(c_2158, plain, (![C_102, D_101, B_103]: (k2_enumset1(C_102, D_101, B_103, B_103)=k1_enumset1(B_103, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_321, c_1926])).
% 20.04/11.89  tff(c_8281, plain, (![H_327, C_325]: (k1_enumset1(H_327, C_325, H_327)=k1_enumset1(C_325, H_327, H_327))), inference(superposition, [status(thm), theory('equality')], [c_8208, c_2158])).
% 20.04/11.89  tff(c_8526, plain, (![C_325, H_327]: (k1_enumset1(C_325, H_327, H_327)=k2_tarski(H_327, C_325))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_8281])).
% 20.04/11.89  tff(c_8548, plain, (![C_106, B_107]: (k2_tarski(C_106, B_107)=k2_tarski(B_107, C_106))), inference(demodulation, [status(thm), theory('equality')], [c_8526, c_8526, c_403])).
% 20.04/11.89  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.04/11.89  tff(c_900, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_36])).
% 20.04/11.89  tff(c_8582, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8548, c_8548, c_900])).
% 20.04/11.89  tff(c_56180, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18635, c_8582])).
% 20.04/11.89  tff(c_56183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_825, c_26, c_8, c_10, c_56180])).
% 20.04/11.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.04/11.89  
% 20.04/11.89  Inference rules
% 20.04/11.89  ----------------------
% 20.04/11.89  #Ref     : 0
% 20.04/11.89  #Sup     : 13822
% 20.04/11.89  #Fact    : 0
% 20.04/11.89  #Define  : 0
% 20.04/11.89  #Split   : 0
% 20.04/11.89  #Chain   : 0
% 20.04/11.89  #Close   : 0
% 20.04/11.89  
% 20.04/11.89  Ordering : KBO
% 20.04/11.89  
% 20.04/11.89  Simplification rules
% 20.04/11.89  ----------------------
% 20.04/11.89  #Subsume      : 4282
% 20.04/11.89  #Demod        : 12681
% 20.04/11.89  #Tautology    : 7191
% 20.04/11.89  #SimpNegUnit  : 0
% 20.04/11.89  #BackRed      : 5
% 20.04/11.89  
% 20.04/11.89  #Partial instantiations: 0
% 20.04/11.89  #Strategies tried      : 1
% 20.04/11.89  
% 20.04/11.89  Timing (in seconds)
% 20.04/11.89  ----------------------
% 20.04/11.89  Preprocessing        : 0.32
% 20.04/11.89  Parsing              : 0.17
% 20.04/11.89  CNF conversion       : 0.02
% 20.04/11.90  Main loop            : 10.78
% 20.04/11.90  Inferencing          : 1.51
% 20.04/11.90  Reduction            : 7.92
% 20.04/11.90  Demodulation         : 7.57
% 20.04/11.90  BG Simplification    : 0.14
% 20.04/11.90  Subsumption          : 0.98
% 20.04/11.90  Abstraction          : 0.34
% 20.04/11.90  MUC search           : 0.00
% 20.04/11.90  Cooper               : 0.00
% 20.04/11.90  Total                : 11.15
% 20.04/11.90  Index Insertion      : 0.00
% 20.04/11.90  Index Deletion       : 0.00
% 20.04/11.90  Index Matching       : 0.00
% 20.04/11.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:12 EST 2020

% Result     : Theorem 30.48s
% Output     : CNFRefutation 30.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 120 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :   53 (  97 expanded)
%              Number of equality atoms :   52 (  96 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_enumset1(G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,G_21,E_19,H_22,F_20,C_17,I_23] : k2_xboole_0(k1_tarski(A_15),k6_enumset1(B_16,C_17,D_18,E_19,F_20,G_21,H_22,I_23)) = k7_enumset1(A_15,B_16,C_17,D_18,E_19,F_20,G_21,H_22,I_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_46,E_50,B_47,H_53,C_48,D_49,G_52,F_51] : k2_xboole_0(k1_tarski(A_46),k5_enumset1(B_47,C_48,D_49,E_50,F_51,G_52,H_53)) = k6_enumset1(A_46,B_47,C_48,D_49,E_50,F_51,G_52,H_53) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k2_xboole_0(k1_tarski(A_39),k4_enumset1(B_40,C_41,D_42,E_43,F_44,G_45)) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_57,B_58,C_59,D_60] : k3_enumset1(A_57,A_57,B_58,C_59,D_60) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_205,plain,(
    ! [B_104,E_100,F_102,D_103,A_99,C_101] : k2_xboole_0(k1_tarski(A_99),k3_enumset1(B_104,C_101,D_103,E_100,F_102)) = k4_enumset1(A_99,B_104,C_101,D_103,E_100,F_102) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [D_108,A_105,C_109,A_107,B_106] : k4_enumset1(A_105,A_107,A_107,B_106,C_109,D_108) = k2_xboole_0(k1_tarski(A_105),k2_enumset1(A_107,B_106,C_109,D_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_205])).

tff(c_329,plain,(
    ! [A_127,A_128,B_129,C_130] : k4_enumset1(A_127,A_128,A_128,A_128,B_129,C_130) = k2_xboole_0(k1_tarski(A_127),k1_enumset1(A_128,B_129,C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_220])).

tff(c_24,plain,(
    ! [A_61,B_62,E_65,C_63,D_64] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,E_65) = k3_enumset1(A_61,B_62,C_63,D_64,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_230,plain,(
    ! [A_107,B_106,C_109,D_108] : k2_xboole_0(k1_tarski(A_107),k2_enumset1(A_107,B_106,C_109,D_108)) = k3_enumset1(A_107,A_107,B_106,C_109,D_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_24])).

tff(c_253,plain,(
    ! [A_110,B_111,C_112,D_113] : k2_xboole_0(k1_tarski(A_110),k2_enumset1(A_110,B_111,C_112,D_113)) = k2_enumset1(A_110,B_111,C_112,D_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_230])).

tff(c_272,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_54,B_55,C_56)) = k2_enumset1(A_54,A_54,B_55,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_253])).

tff(c_275,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_54,B_55,C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_272])).

tff(c_394,plain,(
    ! [A_138,B_139,C_140] : k4_enumset1(A_138,A_138,A_138,A_138,B_139,C_140) = k1_enumset1(A_138,B_139,C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_275])).

tff(c_409,plain,(
    ! [A_138,B_139,C_140] : k3_enumset1(A_138,A_138,A_138,B_139,C_140) = k1_enumset1(A_138,B_139,C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_24])).

tff(c_841,plain,(
    ! [I_192,A_191,F_190,D_193,E_189,C_186,G_185,H_188,B_187] : k2_xboole_0(k3_enumset1(A_191,B_187,C_186,D_193,E_189),k2_enumset1(F_190,G_185,H_188,I_192)) = k7_enumset1(A_191,B_187,C_186,D_193,E_189,F_190,G_185,H_188,I_192) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2212,plain,(
    ! [D_321,A_315,E_320,C_318,C_316,A_317,B_314,B_319] : k7_enumset1(A_315,B_314,C_318,D_321,E_320,A_317,A_317,B_319,C_316) = k2_xboole_0(k3_enumset1(A_315,B_314,C_318,D_321,E_320),k1_enumset1(A_317,B_319,C_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_841])).

tff(c_2267,plain,(
    ! [C_140,A_138,C_316,A_317,B_319,B_139] : k7_enumset1(A_138,A_138,A_138,B_139,C_140,A_317,A_317,B_319,C_316) = k2_xboole_0(k1_enumset1(A_138,B_139,C_140),k1_enumset1(A_317,B_319,C_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_2212])).

tff(c_2278,plain,(
    ! [C_323,A_326,C_327,B_325,A_322,B_324] : k7_enumset1(A_322,A_322,A_322,B_325,C_327,A_326,A_326,B_324,C_323) = k4_enumset1(A_322,B_325,C_327,A_326,B_324,C_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2267])).

tff(c_26,plain,(
    ! [B_67,G_72,A_66,F_71,C_68,E_70,D_69] : k6_enumset1(A_66,A_66,B_67,C_68,D_69,E_70,F_71,G_72) = k5_enumset1(A_66,B_67,C_68,D_69,E_70,F_71,G_72) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1009,plain,(
    ! [B_208,D_205,I_207,C_203,G_206,H_204,E_210,F_209,A_211] : k2_xboole_0(k1_tarski(A_211),k6_enumset1(B_208,C_203,D_205,E_210,F_209,G_206,H_204,I_207)) = k7_enumset1(A_211,B_208,C_203,D_205,E_210,F_209,G_206,H_204,I_207) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1033,plain,(
    ! [B_67,G_72,A_66,F_71,C_68,E_70,A_211,D_69] : k7_enumset1(A_211,A_66,A_66,B_67,C_68,D_69,E_70,F_71,G_72) = k2_xboole_0(k1_tarski(A_211),k5_enumset1(A_66,B_67,C_68,D_69,E_70,F_71,G_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1009])).

tff(c_1038,plain,(
    ! [B_67,G_72,A_66,F_71,C_68,E_70,A_211,D_69] : k7_enumset1(A_211,A_66,A_66,B_67,C_68,D_69,E_70,F_71,G_72) = k6_enumset1(A_211,A_66,B_67,C_68,D_69,E_70,F_71,G_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1033])).

tff(c_2322,plain,(
    ! [C_331,A_330,C_328,B_333,B_329,A_332] : k6_enumset1(A_332,A_332,B_333,C_331,A_330,A_330,B_329,C_328) = k4_enumset1(A_332,B_333,C_331,A_330,B_329,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_2278,c_1038])).

tff(c_2478,plain,(
    ! [A_342,B_341,A_343,C_339,B_344,C_340] : k5_enumset1(A_343,B_341,C_340,A_342,A_342,B_344,C_339) = k4_enumset1(A_343,B_341,C_340,A_342,B_344,C_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_2322,c_26])).

tff(c_2500,plain,(
    ! [A_46,A_342,B_341,A_343,C_339,B_344,C_340] : k6_enumset1(A_46,A_343,B_341,C_340,A_342,A_342,B_344,C_339) = k2_xboole_0(k1_tarski(A_46),k4_enumset1(A_343,B_341,C_340,A_342,B_344,C_339)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2478,c_18])).

tff(c_4806,plain,(
    ! [C_517,B_516,C_514,A_515,A_518,B_512,A_513] : k6_enumset1(A_518,A_513,B_512,C_517,A_515,A_515,B_516,C_514) = k5_enumset1(A_518,A_513,B_512,C_517,A_515,B_516,C_514) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2500])).

tff(c_4863,plain,(
    ! [A_15,C_517,B_516,C_514,A_515,A_518,B_512,A_513] : k7_enumset1(A_15,A_518,A_513,B_512,C_517,A_515,A_515,B_516,C_514) = k2_xboole_0(k1_tarski(A_15),k5_enumset1(A_518,A_513,B_512,C_517,A_515,B_516,C_514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4806,c_10])).

tff(c_4930,plain,(
    ! [A_15,C_517,B_516,C_514,A_515,A_518,B_512,A_513] : k7_enumset1(A_15,A_518,A_513,B_512,C_517,A_515,A_515,B_516,C_514) = k6_enumset1(A_15,A_518,A_513,B_512,C_517,A_515,B_516,C_514) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4863])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [B_104,E_100,F_102,D_103,C_3,A_99,C_101] : k2_xboole_0(k1_tarski(A_99),k2_xboole_0(k3_enumset1(B_104,C_101,D_103,E_100,F_102),C_3)) = k2_xboole_0(k4_enumset1(A_99,B_104,C_101,D_103,E_100,F_102),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_2229,plain,(
    ! [D_321,A_315,E_320,A_99,C_318,C_316,A_317,B_314,B_319] : k2_xboole_0(k4_enumset1(A_99,A_315,B_314,C_318,D_321,E_320),k1_enumset1(A_317,B_319,C_316)) = k2_xboole_0(k1_tarski(A_99),k7_enumset1(A_315,B_314,C_318,D_321,E_320,A_317,A_317,B_319,C_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2212,c_211])).

tff(c_25374,plain,(
    ! [D_321,A_315,E_320,A_99,C_318,C_316,A_317,B_314,B_319] : k2_xboole_0(k4_enumset1(A_99,A_315,B_314,C_318,D_321,E_320),k1_enumset1(A_317,B_319,C_316)) = k7_enumset1(A_99,A_315,B_314,C_318,D_321,E_320,A_317,B_319,C_316) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4930,c_2229])).

tff(c_315,plain,(
    ! [B_122,F_121,E_125,A_126,D_124,C_123] : k2_xboole_0(k1_enumset1(A_126,B_122,C_123),k1_enumset1(D_124,E_125,F_121)) = k4_enumset1(A_126,B_122,C_123,D_124,E_125,F_121) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1889,plain,(
    ! [E_296,C_299,F_301,B_297,C_300,A_295,D_298] : k2_xboole_0(k1_enumset1(A_295,B_297,C_299),k2_xboole_0(k1_enumset1(D_298,E_296,F_301),C_300)) = k2_xboole_0(k4_enumset1(A_295,B_297,C_299,D_298,E_296,F_301),C_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_2])).

tff(c_1922,plain,(
    ! [C_299,C_11,E_13,B_297,B_10,F_14,A_295,D_12,A_9] : k2_xboole_0(k4_enumset1(A_295,B_297,C_299,A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k2_xboole_0(k1_enumset1(A_295,B_297,C_299),k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1889])).

tff(c_25375,plain,(
    ! [C_299,C_11,E_13,B_297,B_10,F_14,A_295,D_12,A_9] : k2_xboole_0(k1_enumset1(A_295,B_297,C_299),k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14)) = k7_enumset1(A_295,B_297,C_299,A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25374,c_1922])).

tff(c_28,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_enumset1('#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19307,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k4_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1922,c_28])).

tff(c_52590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25375,c_19307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.48/19.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.48/19.37  
% 30.48/19.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.48/19.37  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 30.48/19.37  
% 30.48/19.37  %Foreground sorts:
% 30.48/19.37  
% 30.48/19.37  
% 30.48/19.37  %Background operators:
% 30.48/19.37  
% 30.48/19.37  
% 30.48/19.37  %Foreground operators:
% 30.48/19.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.48/19.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.48/19.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.48/19.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 30.48/19.37  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 30.48/19.37  tff('#skF_7', type, '#skF_7': $i).
% 30.48/19.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.48/19.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 30.48/19.37  tff('#skF_5', type, '#skF_5': $i).
% 30.48/19.37  tff('#skF_6', type, '#skF_6': $i).
% 30.48/19.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 30.48/19.37  tff('#skF_2', type, '#skF_2': $i).
% 30.48/19.37  tff('#skF_3', type, '#skF_3': $i).
% 30.48/19.37  tff('#skF_1', type, '#skF_1': $i).
% 30.48/19.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 30.48/19.37  tff('#skF_9', type, '#skF_9': $i).
% 30.48/19.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 30.48/19.37  tff('#skF_8', type, '#skF_8': $i).
% 30.48/19.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.48/19.37  tff('#skF_4', type, '#skF_4': $i).
% 30.48/19.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.48/19.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.48/19.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 30.48/19.37  
% 30.48/19.39  tff(f_35, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 30.48/19.39  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 30.48/19.39  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 30.48/19.39  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 30.48/19.39  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 30.48/19.39  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 30.48/19.39  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 30.48/19.39  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 30.48/19.39  tff(f_37, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 30.48/19.39  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 30.48/19.39  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 30.48/19.39  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_enumset1(G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 30.48/19.39  tff(c_10, plain, (![B_16, A_15, D_18, G_21, E_19, H_22, F_20, C_17, I_23]: (k2_xboole_0(k1_tarski(A_15), k6_enumset1(B_16, C_17, D_18, E_19, F_20, G_21, H_22, I_23))=k7_enumset1(A_15, B_16, C_17, D_18, E_19, F_20, G_21, H_22, I_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.48/19.39  tff(c_18, plain, (![A_46, E_50, B_47, H_53, C_48, D_49, G_52, F_51]: (k2_xboole_0(k1_tarski(A_46), k5_enumset1(B_47, C_48, D_49, E_50, F_51, G_52, H_53))=k6_enumset1(A_46, B_47, C_48, D_49, E_50, F_51, G_52, H_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.48/19.39  tff(c_16, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k2_xboole_0(k1_tarski(A_39), k4_enumset1(B_40, C_41, D_42, E_43, F_44, G_45))=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.48/19.39  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/19.39  tff(c_20, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.48/19.39  tff(c_22, plain, (![A_57, B_58, C_59, D_60]: (k3_enumset1(A_57, A_57, B_58, C_59, D_60)=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 30.48/19.39  tff(c_205, plain, (![B_104, E_100, F_102, D_103, A_99, C_101]: (k2_xboole_0(k1_tarski(A_99), k3_enumset1(B_104, C_101, D_103, E_100, F_102))=k4_enumset1(A_99, B_104, C_101, D_103, E_100, F_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.48/19.39  tff(c_220, plain, (![D_108, A_105, C_109, A_107, B_106]: (k4_enumset1(A_105, A_107, A_107, B_106, C_109, D_108)=k2_xboole_0(k1_tarski(A_105), k2_enumset1(A_107, B_106, C_109, D_108)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_205])).
% 30.48/19.39  tff(c_329, plain, (![A_127, A_128, B_129, C_130]: (k4_enumset1(A_127, A_128, A_128, A_128, B_129, C_130)=k2_xboole_0(k1_tarski(A_127), k1_enumset1(A_128, B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_220])).
% 30.48/19.39  tff(c_24, plain, (![A_61, B_62, E_65, C_63, D_64]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, E_65)=k3_enumset1(A_61, B_62, C_63, D_64, E_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.48/19.39  tff(c_230, plain, (![A_107, B_106, C_109, D_108]: (k2_xboole_0(k1_tarski(A_107), k2_enumset1(A_107, B_106, C_109, D_108))=k3_enumset1(A_107, A_107, B_106, C_109, D_108))), inference(superposition, [status(thm), theory('equality')], [c_220, c_24])).
% 30.48/19.39  tff(c_253, plain, (![A_110, B_111, C_112, D_113]: (k2_xboole_0(k1_tarski(A_110), k2_enumset1(A_110, B_111, C_112, D_113))=k2_enumset1(A_110, B_111, C_112, D_113))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_230])).
% 30.48/19.39  tff(c_272, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_54, B_55, C_56))=k2_enumset1(A_54, A_54, B_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_20, c_253])).
% 30.48/19.39  tff(c_275, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_54, B_55, C_56))=k1_enumset1(A_54, B_55, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_272])).
% 30.48/19.39  tff(c_394, plain, (![A_138, B_139, C_140]: (k4_enumset1(A_138, A_138, A_138, A_138, B_139, C_140)=k1_enumset1(A_138, B_139, C_140))), inference(superposition, [status(thm), theory('equality')], [c_329, c_275])).
% 30.48/19.39  tff(c_409, plain, (![A_138, B_139, C_140]: (k3_enumset1(A_138, A_138, A_138, B_139, C_140)=k1_enumset1(A_138, B_139, C_140))), inference(superposition, [status(thm), theory('equality')], [c_394, c_24])).
% 30.48/19.39  tff(c_841, plain, (![I_192, A_191, F_190, D_193, E_189, C_186, G_185, H_188, B_187]: (k2_xboole_0(k3_enumset1(A_191, B_187, C_186, D_193, E_189), k2_enumset1(F_190, G_185, H_188, I_192))=k7_enumset1(A_191, B_187, C_186, D_193, E_189, F_190, G_185, H_188, I_192))), inference(cnfTransformation, [status(thm)], [f_37])).
% 30.48/19.39  tff(c_2212, plain, (![D_321, A_315, E_320, C_318, C_316, A_317, B_314, B_319]: (k7_enumset1(A_315, B_314, C_318, D_321, E_320, A_317, A_317, B_319, C_316)=k2_xboole_0(k3_enumset1(A_315, B_314, C_318, D_321, E_320), k1_enumset1(A_317, B_319, C_316)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_841])).
% 30.48/19.39  tff(c_2267, plain, (![C_140, A_138, C_316, A_317, B_319, B_139]: (k7_enumset1(A_138, A_138, A_138, B_139, C_140, A_317, A_317, B_319, C_316)=k2_xboole_0(k1_enumset1(A_138, B_139, C_140), k1_enumset1(A_317, B_319, C_316)))), inference(superposition, [status(thm), theory('equality')], [c_409, c_2212])).
% 30.48/19.39  tff(c_2278, plain, (![C_323, A_326, C_327, B_325, A_322, B_324]: (k7_enumset1(A_322, A_322, A_322, B_325, C_327, A_326, A_326, B_324, C_323)=k4_enumset1(A_322, B_325, C_327, A_326, B_324, C_323))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2267])).
% 30.48/19.39  tff(c_26, plain, (![B_67, G_72, A_66, F_71, C_68, E_70, D_69]: (k6_enumset1(A_66, A_66, B_67, C_68, D_69, E_70, F_71, G_72)=k5_enumset1(A_66, B_67, C_68, D_69, E_70, F_71, G_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.48/19.39  tff(c_1009, plain, (![B_208, D_205, I_207, C_203, G_206, H_204, E_210, F_209, A_211]: (k2_xboole_0(k1_tarski(A_211), k6_enumset1(B_208, C_203, D_205, E_210, F_209, G_206, H_204, I_207))=k7_enumset1(A_211, B_208, C_203, D_205, E_210, F_209, G_206, H_204, I_207))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.48/19.39  tff(c_1033, plain, (![B_67, G_72, A_66, F_71, C_68, E_70, A_211, D_69]: (k7_enumset1(A_211, A_66, A_66, B_67, C_68, D_69, E_70, F_71, G_72)=k2_xboole_0(k1_tarski(A_211), k5_enumset1(A_66, B_67, C_68, D_69, E_70, F_71, G_72)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1009])).
% 30.48/19.39  tff(c_1038, plain, (![B_67, G_72, A_66, F_71, C_68, E_70, A_211, D_69]: (k7_enumset1(A_211, A_66, A_66, B_67, C_68, D_69, E_70, F_71, G_72)=k6_enumset1(A_211, A_66, B_67, C_68, D_69, E_70, F_71, G_72))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1033])).
% 30.48/19.39  tff(c_2322, plain, (![C_331, A_330, C_328, B_333, B_329, A_332]: (k6_enumset1(A_332, A_332, B_333, C_331, A_330, A_330, B_329, C_328)=k4_enumset1(A_332, B_333, C_331, A_330, B_329, C_328))), inference(superposition, [status(thm), theory('equality')], [c_2278, c_1038])).
% 30.48/19.39  tff(c_2478, plain, (![A_342, B_341, A_343, C_339, B_344, C_340]: (k5_enumset1(A_343, B_341, C_340, A_342, A_342, B_344, C_339)=k4_enumset1(A_343, B_341, C_340, A_342, B_344, C_339))), inference(superposition, [status(thm), theory('equality')], [c_2322, c_26])).
% 30.48/19.39  tff(c_2500, plain, (![A_46, A_342, B_341, A_343, C_339, B_344, C_340]: (k6_enumset1(A_46, A_343, B_341, C_340, A_342, A_342, B_344, C_339)=k2_xboole_0(k1_tarski(A_46), k4_enumset1(A_343, B_341, C_340, A_342, B_344, C_339)))), inference(superposition, [status(thm), theory('equality')], [c_2478, c_18])).
% 30.48/19.39  tff(c_4806, plain, (![C_517, B_516, C_514, A_515, A_518, B_512, A_513]: (k6_enumset1(A_518, A_513, B_512, C_517, A_515, A_515, B_516, C_514)=k5_enumset1(A_518, A_513, B_512, C_517, A_515, B_516, C_514))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2500])).
% 30.48/19.39  tff(c_4863, plain, (![A_15, C_517, B_516, C_514, A_515, A_518, B_512, A_513]: (k7_enumset1(A_15, A_518, A_513, B_512, C_517, A_515, A_515, B_516, C_514)=k2_xboole_0(k1_tarski(A_15), k5_enumset1(A_518, A_513, B_512, C_517, A_515, B_516, C_514)))), inference(superposition, [status(thm), theory('equality')], [c_4806, c_10])).
% 30.48/19.39  tff(c_4930, plain, (![A_15, C_517, B_516, C_514, A_515, A_518, B_512, A_513]: (k7_enumset1(A_15, A_518, A_513, B_512, C_517, A_515, A_515, B_516, C_514)=k6_enumset1(A_15, A_518, A_513, B_512, C_517, A_515, B_516, C_514))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4863])).
% 30.48/19.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.48/19.39  tff(c_211, plain, (![B_104, E_100, F_102, D_103, C_3, A_99, C_101]: (k2_xboole_0(k1_tarski(A_99), k2_xboole_0(k3_enumset1(B_104, C_101, D_103, E_100, F_102), C_3))=k2_xboole_0(k4_enumset1(A_99, B_104, C_101, D_103, E_100, F_102), C_3))), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 30.48/19.39  tff(c_2229, plain, (![D_321, A_315, E_320, A_99, C_318, C_316, A_317, B_314, B_319]: (k2_xboole_0(k4_enumset1(A_99, A_315, B_314, C_318, D_321, E_320), k1_enumset1(A_317, B_319, C_316))=k2_xboole_0(k1_tarski(A_99), k7_enumset1(A_315, B_314, C_318, D_321, E_320, A_317, A_317, B_319, C_316)))), inference(superposition, [status(thm), theory('equality')], [c_2212, c_211])).
% 30.48/19.39  tff(c_25374, plain, (![D_321, A_315, E_320, A_99, C_318, C_316, A_317, B_314, B_319]: (k2_xboole_0(k4_enumset1(A_99, A_315, B_314, C_318, D_321, E_320), k1_enumset1(A_317, B_319, C_316))=k7_enumset1(A_99, A_315, B_314, C_318, D_321, E_320, A_317, B_319, C_316))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4930, c_2229])).
% 30.48/19.39  tff(c_315, plain, (![B_122, F_121, E_125, A_126, D_124, C_123]: (k2_xboole_0(k1_enumset1(A_126, B_122, C_123), k1_enumset1(D_124, E_125, F_121))=k4_enumset1(A_126, B_122, C_123, D_124, E_125, F_121))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/19.39  tff(c_1889, plain, (![E_296, C_299, F_301, B_297, C_300, A_295, D_298]: (k2_xboole_0(k1_enumset1(A_295, B_297, C_299), k2_xboole_0(k1_enumset1(D_298, E_296, F_301), C_300))=k2_xboole_0(k4_enumset1(A_295, B_297, C_299, D_298, E_296, F_301), C_300))), inference(superposition, [status(thm), theory('equality')], [c_315, c_2])).
% 30.48/19.39  tff(c_1922, plain, (![C_299, C_11, E_13, B_297, B_10, F_14, A_295, D_12, A_9]: (k2_xboole_0(k4_enumset1(A_295, B_297, C_299, A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k2_xboole_0(k1_enumset1(A_295, B_297, C_299), k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1889])).
% 30.48/19.39  tff(c_25375, plain, (![C_299, C_11, E_13, B_297, B_10, F_14, A_295, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_295, B_297, C_299), k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))=k7_enumset1(A_295, B_297, C_299, A_9, B_10, C_11, D_12, E_13, F_14))), inference(demodulation, [status(thm), theory('equality')], [c_25374, c_1922])).
% 30.48/19.39  tff(c_28, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_enumset1('#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_54])).
% 30.48/19.39  tff(c_19307, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k4_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1922, c_28])).
% 30.48/19.39  tff(c_52590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25375, c_19307])).
% 30.48/19.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.48/19.39  
% 30.48/19.39  Inference rules
% 30.48/19.39  ----------------------
% 30.48/19.39  #Ref     : 0
% 30.48/19.39  #Sup     : 12810
% 30.48/19.39  #Fact    : 0
% 30.48/19.39  #Define  : 0
% 30.48/19.39  #Split   : 0
% 30.48/19.39  #Chain   : 0
% 30.48/19.39  #Close   : 0
% 30.48/19.39  
% 30.48/19.39  Ordering : KBO
% 30.48/19.39  
% 30.48/19.39  Simplification rules
% 30.48/19.39  ----------------------
% 30.48/19.39  #Subsume      : 36
% 30.48/19.39  #Demod        : 28989
% 30.48/19.39  #Tautology    : 7709
% 30.48/19.39  #SimpNegUnit  : 0
% 30.48/19.39  #BackRed      : 17
% 30.48/19.39  
% 30.48/19.39  #Partial instantiations: 0
% 30.48/19.39  #Strategies tried      : 1
% 30.48/19.39  
% 30.48/19.39  Timing (in seconds)
% 30.48/19.39  ----------------------
% 30.48/19.39  Preprocessing        : 0.50
% 30.48/19.39  Parsing              : 0.26
% 30.48/19.39  CNF conversion       : 0.04
% 30.48/19.39  Main loop            : 17.98
% 30.48/19.39  Inferencing          : 4.11
% 30.48/19.39  Reduction            : 11.21
% 30.48/19.39  Demodulation         : 10.47
% 30.48/19.39  BG Simplification    : 0.58
% 30.48/19.39  Subsumption          : 1.66
% 30.48/19.39  Abstraction          : 1.28
% 30.48/19.39  MUC search           : 0.00
% 30.48/19.39  Cooper               : 0.00
% 30.48/19.39  Total                : 18.53
% 30.48/19.39  Index Insertion      : 0.00
% 30.48/19.39  Index Deletion       : 0.00
% 30.48/19.39  Index Matching       : 0.00
% 30.48/19.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 22.91s
% Output     : CNFRefutation 22.95s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 391 expanded)
%              Number of leaves         :   29 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :   64 ( 373 expanded)
%              Number of equality atoms :   63 ( 372 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

tff(c_10,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_enumset1(D_27,E_28,F_29)) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_47,B_48,C_49] : k3_enumset1(A_47,A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_45,B_46] : k2_enumset1(A_45,A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k2_tarski(D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_398,plain,(
    ! [A_121,F_120,E_122,D_123,B_119,G_124,C_118] : k2_xboole_0(k1_enumset1(A_121,B_119,C_118),k2_enumset1(D_123,E_122,F_120,G_124)) = k5_enumset1(A_121,B_119,C_118,D_123,E_122,F_120,G_124) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_413,plain,(
    ! [A_121,A_45,B_119,B_46,C_118] : k5_enumset1(A_121,B_119,C_118,A_45,A_45,A_45,B_46) = k2_xboole_0(k1_enumset1(A_121,B_119,C_118),k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_398])).

tff(c_417,plain,(
    ! [B_126,A_129,C_127,A_125,B_128] : k5_enumset1(A_125,B_126,C_127,A_129,A_129,A_129,B_128) = k3_enumset1(A_125,B_126,C_127,A_129,B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_413])).

tff(c_6,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,(
    ! [C_103,A_98,B_99,D_101,F_100,E_102,G_104] : k2_xboole_0(k2_enumset1(A_98,B_99,C_103,D_101),k1_enumset1(E_102,F_100,G_104)) = k5_enumset1(A_98,B_99,C_103,D_101,E_102,F_100,G_104) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_305,plain,(
    ! [A_108,B_107,F_106,E_109,G_105] : k5_enumset1(A_108,A_108,A_108,B_107,E_109,F_106,G_105) = k2_xboole_0(k2_tarski(A_108,B_107),k1_enumset1(E_109,F_106,G_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_323,plain,(
    ! [A_44,E_109,F_106,G_105] : k5_enumset1(A_44,A_44,A_44,A_44,E_109,F_106,G_105) = k2_xboole_0(k1_tarski(A_44),k1_enumset1(E_109,F_106,G_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_328,plain,(
    ! [A_44,E_109,F_106,G_105] : k5_enumset1(A_44,A_44,A_44,A_44,E_109,F_106,G_105) = k2_enumset1(A_44,E_109,F_106,G_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_323])).

tff(c_424,plain,(
    ! [A_129,B_128] : k3_enumset1(A_129,A_129,A_129,A_129,B_128) = k2_enumset1(A_129,A_129,A_129,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_328])).

tff(c_441,plain,(
    ! [A_129,B_128] : k1_enumset1(A_129,A_129,B_128) = k2_tarski(A_129,B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_424])).

tff(c_59,plain,(
    ! [B_62,C_63,D_61,E_60,A_64] : k2_xboole_0(k1_enumset1(A_64,B_62,C_63),k2_tarski(D_61,E_60)) = k3_enumset1(A_64,B_62,C_63,D_61,E_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_71,B_72,C_73,A_74] : k3_enumset1(A_71,B_72,C_73,A_74,A_74) = k2_xboole_0(k1_enumset1(A_71,B_72,C_73),k1_tarski(A_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_90,plain,(
    ! [C_73,A_74] : k2_xboole_0(k1_enumset1(C_73,C_73,C_73),k1_tarski(A_74)) = k1_enumset1(C_73,A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_20])).

tff(c_449,plain,(
    ! [C_73,A_74] : k2_xboole_0(k2_tarski(C_73,C_73),k1_tarski(A_74)) = k1_enumset1(C_73,A_74,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_90])).

tff(c_492,plain,(
    ! [C_132,A_133] : k2_xboole_0(k1_tarski(C_132),k1_tarski(A_133)) = k1_enumset1(C_132,A_133,A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_449])).

tff(c_502,plain,(
    ! [A_133] : k2_xboole_0(k1_tarski(A_133),k1_tarski(A_133)) = k2_tarski(A_133,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_441])).

tff(c_546,plain,(
    ! [A_134] : k2_xboole_0(k1_tarski(A_134),k1_tarski(A_134)) = k1_tarski(A_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_502])).

tff(c_453,plain,(
    ! [C_73,A_74] : k2_xboole_0(k1_tarski(C_73),k1_tarski(A_74)) = k1_enumset1(C_73,A_74,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_449])).

tff(c_577,plain,(
    ! [A_143] : k1_enumset1(A_143,A_143,A_143) = k1_tarski(A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_453])).

tff(c_610,plain,(
    ! [A_143,D_4,E_5] : k3_enumset1(A_143,A_143,A_143,D_4,E_5) = k2_xboole_0(k1_tarski(A_143),k2_tarski(D_4,E_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_2])).

tff(c_629,plain,(
    ! [A_143,D_4,E_5] : k2_xboole_0(k1_tarski(A_143),k2_tarski(D_4,E_5)) = k1_enumset1(A_143,D_4,E_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_610])).

tff(c_454,plain,(
    ! [A_130,B_131] : k1_enumset1(A_130,A_130,B_131) = k2_tarski(A_130,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_424])).

tff(c_484,plain,(
    ! [A_14,A_130,B_131] : k2_xboole_0(k1_tarski(A_14),k2_tarski(A_130,B_131)) = k2_enumset1(A_14,A_130,A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_6])).

tff(c_823,plain,(
    ! [A_14,A_130,B_131] : k2_enumset1(A_14,A_130,A_130,B_131) = k1_enumset1(A_14,A_130,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_484])).

tff(c_1587,plain,(
    ! [A_200,B_201,D_202,E_203] : k3_enumset1(A_200,A_200,B_201,D_202,E_203) = k2_xboole_0(k2_tarski(A_200,B_201),k2_tarski(D_202,E_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_2])).

tff(c_302,plain,(
    ! [A_45,B_46,F_100,E_102,G_104] : k5_enumset1(A_45,A_45,A_45,B_46,E_102,F_100,G_104) = k2_xboole_0(k2_tarski(A_45,B_46),k1_enumset1(E_102,F_100,G_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_439,plain,(
    ! [A_45,F_100,G_104] : k3_enumset1(A_45,A_45,A_45,F_100,G_104) = k2_xboole_0(k2_tarski(A_45,F_100),k1_enumset1(F_100,F_100,G_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_417])).

tff(c_445,plain,(
    ! [A_45,F_100,G_104] : k2_xboole_0(k2_tarski(A_45,F_100),k1_enumset1(F_100,F_100,G_104)) = k1_enumset1(A_45,F_100,G_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_439])).

tff(c_1165,plain,(
    ! [A_45,F_100,G_104] : k2_xboole_0(k2_tarski(A_45,F_100),k2_tarski(F_100,G_104)) = k1_enumset1(A_45,F_100,G_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_445])).

tff(c_1684,plain,(
    ! [A_204,D_205,E_206] : k3_enumset1(A_204,A_204,D_205,D_205,E_206) = k1_enumset1(A_204,D_205,E_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_1165])).

tff(c_8,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1705,plain,(
    ! [A_18,A_204,D_205,E_206] : k4_enumset1(A_18,A_204,A_204,D_205,D_205,E_206) = k2_xboole_0(k1_tarski(A_18),k1_enumset1(A_204,D_205,E_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1684,c_8])).

tff(c_1757,plain,(
    ! [A_207,A_208,D_209,E_210] : k4_enumset1(A_207,A_208,A_208,D_209,D_209,E_210) = k2_enumset1(A_207,A_208,D_209,E_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1705])).

tff(c_604,plain,(
    ! [A_143,D_27,E_28,F_29] : k4_enumset1(A_143,A_143,A_143,D_27,E_28,F_29) = k2_xboole_0(k1_tarski(A_143),k1_enumset1(D_27,E_28,F_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_10])).

tff(c_628,plain,(
    ! [A_143,D_27,E_28,F_29] : k4_enumset1(A_143,A_143,A_143,D_27,E_28,F_29) = k2_enumset1(A_143,D_27,E_28,F_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_604])).

tff(c_1764,plain,(
    ! [A_208,D_209,E_210] : k2_enumset1(A_208,D_209,D_209,E_210) = k2_enumset1(A_208,A_208,D_209,E_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_628])).

tff(c_1822,plain,(
    ! [A_211,D_212,E_213] : k2_enumset1(A_211,A_211,D_212,E_213) = k1_enumset1(A_211,D_212,E_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_1764])).

tff(c_14,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,G_43,E_41] : k2_xboole_0(k2_enumset1(A_37,B_38,C_39,D_40),k1_enumset1(E_41,F_42,G_43)) = k5_enumset1(A_37,B_38,C_39,D_40,E_41,F_42,G_43) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1855,plain,(
    ! [D_212,F_42,G_43,E_41,E_213,A_211] : k5_enumset1(A_211,A_211,D_212,E_213,E_41,F_42,G_43) = k2_xboole_0(k1_enumset1(A_211,D_212,E_213),k1_enumset1(E_41,F_42,G_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_14])).

tff(c_1885,plain,(
    ! [D_212,F_42,G_43,E_41,E_213,A_211] : k5_enumset1(A_211,A_211,D_212,E_213,E_41,F_42,G_43) = k4_enumset1(A_211,D_212,E_213,E_41,F_42,G_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1855])).

tff(c_12,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k2_enumset1(D_33,E_34,F_35,G_36)) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20778,plain,(
    ! [G_592,E_590,F_589,B_588,D_591,A_587] : k5_enumset1(A_587,A_587,B_588,D_591,E_590,F_589,G_592) = k2_xboole_0(k2_tarski(A_587,B_588),k2_enumset1(D_591,E_590,F_589,G_592)) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_12])).

tff(c_562,plain,(
    ! [H_135,G_136,D_137,F_142,E_141,C_138,B_139,A_140] : k2_xboole_0(k2_enumset1(A_140,B_139,C_138,D_137),k2_enumset1(E_141,F_142,G_136,H_135)) = k6_enumset1(A_140,B_139,C_138,D_137,E_141,F_142,G_136,H_135) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_571,plain,(
    ! [H_135,G_136,A_45,F_142,B_46,E_141] : k6_enumset1(A_45,A_45,A_45,B_46,E_141,F_142,G_136,H_135) = k2_xboole_0(k2_tarski(A_45,B_46),k2_enumset1(E_141,F_142,G_136,H_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_562])).

tff(c_20895,plain,(
    ! [G_592,E_590,F_589,B_588,D_591,A_587] : k6_enumset1(A_587,A_587,A_587,B_588,D_591,E_590,F_589,G_592) = k5_enumset1(A_587,A_587,B_588,D_591,E_590,F_589,G_592) ),
    inference(superposition,[status(thm),theory(equality)],[c_20778,c_571])).

tff(c_22,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73160,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20895,c_22])).

tff(c_76214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_73160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.91/14.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/14.97  
% 22.95/14.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/14.97  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.95/14.97  
% 22.95/14.97  %Foreground sorts:
% 22.95/14.97  
% 22.95/14.97  
% 22.95/14.97  %Background operators:
% 22.95/14.97  
% 22.95/14.97  
% 22.95/14.97  %Foreground operators:
% 22.95/14.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.95/14.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.95/14.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.95/14.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.95/14.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.95/14.97  tff('#skF_5', type, '#skF_5': $i).
% 22.95/14.97  tff('#skF_6', type, '#skF_6': $i).
% 22.95/14.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.95/14.97  tff('#skF_2', type, '#skF_2': $i).
% 22.95/14.97  tff('#skF_3', type, '#skF_3': $i).
% 22.95/14.97  tff('#skF_1', type, '#skF_1': $i).
% 22.95/14.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.95/14.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 22.95/14.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.95/14.97  tff('#skF_4', type, '#skF_4': $i).
% 22.95/14.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.95/14.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.95/14.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 22.95/14.97  
% 22.95/14.99  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 22.95/14.99  tff(f_45, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 22.95/14.99  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 22.95/14.99  tff(f_43, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 22.95/14.99  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 22.95/14.99  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 22.95/14.99  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 22.95/14.99  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 22.95/14.99  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 22.95/14.99  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 22.95/14.99  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 22.95/14.99  tff(c_10, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_enumset1(D_27, E_28, F_29))=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.95/14.99  tff(c_20, plain, (![A_47, B_48, C_49]: (k3_enumset1(A_47, A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.95/14.99  tff(c_16, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.95/14.99  tff(c_18, plain, (![A_45, B_46]: (k2_enumset1(A_45, A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.95/14.99  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k2_tarski(D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.95/14.99  tff(c_398, plain, (![A_121, F_120, E_122, D_123, B_119, G_124, C_118]: (k2_xboole_0(k1_enumset1(A_121, B_119, C_118), k2_enumset1(D_123, E_122, F_120, G_124))=k5_enumset1(A_121, B_119, C_118, D_123, E_122, F_120, G_124))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.95/14.99  tff(c_413, plain, (![A_121, A_45, B_119, B_46, C_118]: (k5_enumset1(A_121, B_119, C_118, A_45, A_45, A_45, B_46)=k2_xboole_0(k1_enumset1(A_121, B_119, C_118), k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_398])).
% 22.95/14.99  tff(c_417, plain, (![B_126, A_129, C_127, A_125, B_128]: (k5_enumset1(A_125, B_126, C_127, A_129, A_129, A_129, B_128)=k3_enumset1(A_125, B_126, C_127, A_129, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_413])).
% 22.95/14.99  tff(c_6, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.95/14.99  tff(c_287, plain, (![C_103, A_98, B_99, D_101, F_100, E_102, G_104]: (k2_xboole_0(k2_enumset1(A_98, B_99, C_103, D_101), k1_enumset1(E_102, F_100, G_104))=k5_enumset1(A_98, B_99, C_103, D_101, E_102, F_100, G_104))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.95/14.99  tff(c_305, plain, (![A_108, B_107, F_106, E_109, G_105]: (k5_enumset1(A_108, A_108, A_108, B_107, E_109, F_106, G_105)=k2_xboole_0(k2_tarski(A_108, B_107), k1_enumset1(E_109, F_106, G_105)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_287])).
% 22.95/14.99  tff(c_323, plain, (![A_44, E_109, F_106, G_105]: (k5_enumset1(A_44, A_44, A_44, A_44, E_109, F_106, G_105)=k2_xboole_0(k1_tarski(A_44), k1_enumset1(E_109, F_106, G_105)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_305])).
% 22.95/14.99  tff(c_328, plain, (![A_44, E_109, F_106, G_105]: (k5_enumset1(A_44, A_44, A_44, A_44, E_109, F_106, G_105)=k2_enumset1(A_44, E_109, F_106, G_105))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_323])).
% 22.95/14.99  tff(c_424, plain, (![A_129, B_128]: (k3_enumset1(A_129, A_129, A_129, A_129, B_128)=k2_enumset1(A_129, A_129, A_129, B_128))), inference(superposition, [status(thm), theory('equality')], [c_417, c_328])).
% 22.95/14.99  tff(c_441, plain, (![A_129, B_128]: (k1_enumset1(A_129, A_129, B_128)=k2_tarski(A_129, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_424])).
% 22.95/14.99  tff(c_59, plain, (![B_62, C_63, D_61, E_60, A_64]: (k2_xboole_0(k1_enumset1(A_64, B_62, C_63), k2_tarski(D_61, E_60))=k3_enumset1(A_64, B_62, C_63, D_61, E_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.95/14.99  tff(c_80, plain, (![A_71, B_72, C_73, A_74]: (k3_enumset1(A_71, B_72, C_73, A_74, A_74)=k2_xboole_0(k1_enumset1(A_71, B_72, C_73), k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_59])).
% 22.95/14.99  tff(c_90, plain, (![C_73, A_74]: (k2_xboole_0(k1_enumset1(C_73, C_73, C_73), k1_tarski(A_74))=k1_enumset1(C_73, A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_80, c_20])).
% 22.95/14.99  tff(c_449, plain, (![C_73, A_74]: (k2_xboole_0(k2_tarski(C_73, C_73), k1_tarski(A_74))=k1_enumset1(C_73, A_74, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_90])).
% 22.95/14.99  tff(c_492, plain, (![C_132, A_133]: (k2_xboole_0(k1_tarski(C_132), k1_tarski(A_133))=k1_enumset1(C_132, A_133, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_449])).
% 22.95/14.99  tff(c_502, plain, (![A_133]: (k2_xboole_0(k1_tarski(A_133), k1_tarski(A_133))=k2_tarski(A_133, A_133))), inference(superposition, [status(thm), theory('equality')], [c_492, c_441])).
% 22.95/14.99  tff(c_546, plain, (![A_134]: (k2_xboole_0(k1_tarski(A_134), k1_tarski(A_134))=k1_tarski(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_502])).
% 22.95/14.99  tff(c_453, plain, (![C_73, A_74]: (k2_xboole_0(k1_tarski(C_73), k1_tarski(A_74))=k1_enumset1(C_73, A_74, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_449])).
% 22.95/14.99  tff(c_577, plain, (![A_143]: (k1_enumset1(A_143, A_143, A_143)=k1_tarski(A_143))), inference(superposition, [status(thm), theory('equality')], [c_546, c_453])).
% 22.95/14.99  tff(c_610, plain, (![A_143, D_4, E_5]: (k3_enumset1(A_143, A_143, A_143, D_4, E_5)=k2_xboole_0(k1_tarski(A_143), k2_tarski(D_4, E_5)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_2])).
% 22.95/14.99  tff(c_629, plain, (![A_143, D_4, E_5]: (k2_xboole_0(k1_tarski(A_143), k2_tarski(D_4, E_5))=k1_enumset1(A_143, D_4, E_5))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_610])).
% 22.95/14.99  tff(c_454, plain, (![A_130, B_131]: (k1_enumset1(A_130, A_130, B_131)=k2_tarski(A_130, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_424])).
% 22.95/14.99  tff(c_484, plain, (![A_14, A_130, B_131]: (k2_xboole_0(k1_tarski(A_14), k2_tarski(A_130, B_131))=k2_enumset1(A_14, A_130, A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_454, c_6])).
% 22.95/14.99  tff(c_823, plain, (![A_14, A_130, B_131]: (k2_enumset1(A_14, A_130, A_130, B_131)=k1_enumset1(A_14, A_130, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_484])).
% 22.95/14.99  tff(c_1587, plain, (![A_200, B_201, D_202, E_203]: (k3_enumset1(A_200, A_200, B_201, D_202, E_203)=k2_xboole_0(k2_tarski(A_200, B_201), k2_tarski(D_202, E_203)))), inference(superposition, [status(thm), theory('equality')], [c_454, c_2])).
% 22.95/14.99  tff(c_302, plain, (![A_45, B_46, F_100, E_102, G_104]: (k5_enumset1(A_45, A_45, A_45, B_46, E_102, F_100, G_104)=k2_xboole_0(k2_tarski(A_45, B_46), k1_enumset1(E_102, F_100, G_104)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_287])).
% 22.95/14.99  tff(c_439, plain, (![A_45, F_100, G_104]: (k3_enumset1(A_45, A_45, A_45, F_100, G_104)=k2_xboole_0(k2_tarski(A_45, F_100), k1_enumset1(F_100, F_100, G_104)))), inference(superposition, [status(thm), theory('equality')], [c_302, c_417])).
% 22.95/14.99  tff(c_445, plain, (![A_45, F_100, G_104]: (k2_xboole_0(k2_tarski(A_45, F_100), k1_enumset1(F_100, F_100, G_104))=k1_enumset1(A_45, F_100, G_104))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_439])).
% 22.95/14.99  tff(c_1165, plain, (![A_45, F_100, G_104]: (k2_xboole_0(k2_tarski(A_45, F_100), k2_tarski(F_100, G_104))=k1_enumset1(A_45, F_100, G_104))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_445])).
% 22.95/14.99  tff(c_1684, plain, (![A_204, D_205, E_206]: (k3_enumset1(A_204, A_204, D_205, D_205, E_206)=k1_enumset1(A_204, D_205, E_206))), inference(superposition, [status(thm), theory('equality')], [c_1587, c_1165])).
% 22.95/14.99  tff(c_8, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.95/14.99  tff(c_1705, plain, (![A_18, A_204, D_205, E_206]: (k4_enumset1(A_18, A_204, A_204, D_205, D_205, E_206)=k2_xboole_0(k1_tarski(A_18), k1_enumset1(A_204, D_205, E_206)))), inference(superposition, [status(thm), theory('equality')], [c_1684, c_8])).
% 22.95/14.99  tff(c_1757, plain, (![A_207, A_208, D_209, E_210]: (k4_enumset1(A_207, A_208, A_208, D_209, D_209, E_210)=k2_enumset1(A_207, A_208, D_209, E_210))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1705])).
% 22.95/14.99  tff(c_604, plain, (![A_143, D_27, E_28, F_29]: (k4_enumset1(A_143, A_143, A_143, D_27, E_28, F_29)=k2_xboole_0(k1_tarski(A_143), k1_enumset1(D_27, E_28, F_29)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_10])).
% 22.95/14.99  tff(c_628, plain, (![A_143, D_27, E_28, F_29]: (k4_enumset1(A_143, A_143, A_143, D_27, E_28, F_29)=k2_enumset1(A_143, D_27, E_28, F_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_604])).
% 22.95/14.99  tff(c_1764, plain, (![A_208, D_209, E_210]: (k2_enumset1(A_208, D_209, D_209, E_210)=k2_enumset1(A_208, A_208, D_209, E_210))), inference(superposition, [status(thm), theory('equality')], [c_1757, c_628])).
% 22.95/14.99  tff(c_1822, plain, (![A_211, D_212, E_213]: (k2_enumset1(A_211, A_211, D_212, E_213)=k1_enumset1(A_211, D_212, E_213))), inference(demodulation, [status(thm), theory('equality')], [c_823, c_1764])).
% 22.95/14.99  tff(c_14, plain, (![C_39, B_38, A_37, D_40, F_42, G_43, E_41]: (k2_xboole_0(k2_enumset1(A_37, B_38, C_39, D_40), k1_enumset1(E_41, F_42, G_43))=k5_enumset1(A_37, B_38, C_39, D_40, E_41, F_42, G_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.95/14.99  tff(c_1855, plain, (![D_212, F_42, G_43, E_41, E_213, A_211]: (k5_enumset1(A_211, A_211, D_212, E_213, E_41, F_42, G_43)=k2_xboole_0(k1_enumset1(A_211, D_212, E_213), k1_enumset1(E_41, F_42, G_43)))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_14])).
% 22.95/14.99  tff(c_1885, plain, (![D_212, F_42, G_43, E_41, E_213, A_211]: (k5_enumset1(A_211, A_211, D_212, E_213, E_41, F_42, G_43)=k4_enumset1(A_211, D_212, E_213, E_41, F_42, G_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1855])).
% 22.95/14.99  tff(c_12, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k2_enumset1(D_33, E_34, F_35, G_36))=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.95/14.99  tff(c_20778, plain, (![G_592, E_590, F_589, B_588, D_591, A_587]: (k5_enumset1(A_587, A_587, B_588, D_591, E_590, F_589, G_592)=k2_xboole_0(k2_tarski(A_587, B_588), k2_enumset1(D_591, E_590, F_589, G_592)))), inference(superposition, [status(thm), theory('equality')], [c_454, c_12])).
% 22.95/14.99  tff(c_562, plain, (![H_135, G_136, D_137, F_142, E_141, C_138, B_139, A_140]: (k2_xboole_0(k2_enumset1(A_140, B_139, C_138, D_137), k2_enumset1(E_141, F_142, G_136, H_135))=k6_enumset1(A_140, B_139, C_138, D_137, E_141, F_142, G_136, H_135))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.95/14.99  tff(c_571, plain, (![H_135, G_136, A_45, F_142, B_46, E_141]: (k6_enumset1(A_45, A_45, A_45, B_46, E_141, F_142, G_136, H_135)=k2_xboole_0(k2_tarski(A_45, B_46), k2_enumset1(E_141, F_142, G_136, H_135)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_562])).
% 22.95/14.99  tff(c_20895, plain, (![G_592, E_590, F_589, B_588, D_591, A_587]: (k6_enumset1(A_587, A_587, A_587, B_588, D_591, E_590, F_589, G_592)=k5_enumset1(A_587, A_587, B_588, D_591, E_590, F_589, G_592))), inference(superposition, [status(thm), theory('equality')], [c_20778, c_571])).
% 22.95/14.99  tff(c_22, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.95/14.99  tff(c_73160, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20895, c_22])).
% 22.95/14.99  tff(c_76214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1885, c_73160])).
% 22.95/14.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.95/14.99  
% 22.95/14.99  Inference rules
% 22.95/14.99  ----------------------
% 22.95/14.99  #Ref     : 0
% 22.95/14.99  #Sup     : 17201
% 22.95/14.99  #Fact    : 0
% 22.95/14.99  #Define  : 0
% 22.95/14.99  #Split   : 0
% 22.95/14.99  #Chain   : 0
% 22.95/14.99  #Close   : 0
% 22.95/14.99  
% 22.95/14.99  Ordering : KBO
% 22.95/14.99  
% 22.95/14.99  Simplification rules
% 22.95/14.99  ----------------------
% 22.95/14.99  #Subsume      : 3942
% 22.95/14.99  #Demod        : 33346
% 22.95/14.99  #Tautology    : 11104
% 22.95/14.99  #SimpNegUnit  : 0
% 22.95/14.99  #BackRed      : 29
% 22.95/14.99  
% 22.95/14.99  #Partial instantiations: 0
% 22.95/14.99  #Strategies tried      : 1
% 22.95/14.99  
% 22.95/14.99  Timing (in seconds)
% 22.95/14.99  ----------------------
% 22.95/15.00  Preprocessing        : 0.35
% 22.95/15.00  Parsing              : 0.19
% 22.95/15.00  CNF conversion       : 0.02
% 22.95/15.00  Main loop            : 13.84
% 22.95/15.00  Inferencing          : 2.58
% 22.95/15.00  Reduction            : 9.72
% 22.95/15.00  Demodulation         : 9.24
% 22.95/15.00  BG Simplification    : 0.16
% 22.95/15.00  Subsumption          : 1.12
% 22.95/15.00  Abstraction          : 0.51
% 22.95/15.00  MUC search           : 0.00
% 22.95/15.00  Cooper               : 0.00
% 22.95/15.00  Total                : 14.23
% 22.95/15.00  Index Insertion      : 0.00
% 22.95/15.00  Index Deletion       : 0.00
% 22.95/15.00  Index Matching       : 0.00
% 22.95/15.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

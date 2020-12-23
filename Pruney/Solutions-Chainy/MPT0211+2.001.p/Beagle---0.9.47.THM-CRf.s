%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 13.65s
% Output     : CNFRefutation 13.65s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 668 expanded)
%              Number of leaves         :   31 ( 243 expanded)
%              Depth                    :   16
%              Number of atoms          :   79 ( 650 expanded)
%              Number of equality atoms :   78 ( 649 expanded)
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
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_161,plain,(
    ! [A_101,B_102,C_103,D_104] : k2_xboole_0(k1_tarski(A_101),k1_enumset1(B_102,C_103,D_104)) = k2_enumset1(A_101,B_102,C_103,D_104) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [B_102,C_103,D_104,A_101] : k2_xboole_0(k1_enumset1(B_102,C_103,D_104),k1_tarski(A_101)) = k2_enumset1(A_101,B_102,C_103,D_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_30,plain,(
    ! [A_61,B_62,C_63,D_64] : k3_enumset1(A_61,A_61,B_62,C_63,D_64) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] : k4_enumset1(A_65,A_65,B_66,C_67,D_68,E_69) = k3_enumset1(A_65,B_66,C_67,D_68,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_678,plain,(
    ! [C_140,A_143,D_145,B_142,E_141,F_144] : k2_xboole_0(k3_enumset1(A_143,B_142,C_140,D_145,E_141),k1_tarski(F_144)) = k4_enumset1(A_143,B_142,C_140,D_145,E_141,F_144) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_693,plain,(
    ! [A_61,B_62,C_63,D_64,F_144] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,F_144) = k2_xboole_0(k2_enumset1(A_61,B_62,C_63,D_64),k1_tarski(F_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_678])).

tff(c_2024,plain,(
    ! [B_222,D_221,A_223,F_219,C_220] : k2_xboole_0(k2_enumset1(A_223,B_222,C_220,D_221),k1_tarski(F_219)) = k3_enumset1(A_223,B_222,C_220,D_221,F_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_693])).

tff(c_2078,plain,(
    ! [A_58,B_59,C_60,F_219] : k3_enumset1(A_58,A_58,B_59,C_60,F_219) = k2_xboole_0(k1_enumset1(A_58,B_59,C_60),k1_tarski(F_219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2024])).

tff(c_2088,plain,(
    ! [F_224,A_225,B_226,C_227] : k2_enumset1(F_224,A_225,B_226,C_227) = k2_enumset1(A_225,B_226,C_227,F_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_30,c_2078])).

tff(c_2300,plain,(
    ! [C_60,A_58,B_59] : k2_enumset1(C_60,A_58,A_58,B_59) = k1_enumset1(A_58,B_59,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2088])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_185,plain,(
    ! [A_105,A_106,B_107] : k2_xboole_0(k1_tarski(A_105),k2_tarski(A_106,B_107)) = k2_enumset1(A_105,A_106,A_106,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_787,plain,(
    ! [A_155,B_156,A_157] : k2_xboole_0(k1_tarski(A_155),k2_tarski(B_156,A_157)) = k2_enumset1(A_155,A_157,A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_185])).

tff(c_176,plain,(
    ! [A_101,A_56,B_57] : k2_xboole_0(k1_tarski(A_101),k2_tarski(A_56,B_57)) = k2_enumset1(A_101,A_56,A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_835,plain,(
    ! [A_155,B_156,A_157] : k2_enumset1(A_155,B_156,B_156,A_157) = k2_enumset1(A_155,A_157,A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_176])).

tff(c_3690,plain,(
    ! [B_156,A_157,A_155] : k1_enumset1(B_156,A_157,A_155) = k1_enumset1(A_157,B_156,A_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_2300,c_835])).

tff(c_490,plain,(
    ! [C_133,B_132,F_131,D_134,A_136,E_135] : k2_xboole_0(k1_enumset1(A_136,B_132,C_133),k1_enumset1(D_134,E_135,F_131)) = k4_enumset1(A_136,B_132,C_133,D_134,E_135,F_131) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_511,plain,(
    ! [A_56,F_131,B_57,D_134,E_135] : k4_enumset1(A_56,A_56,B_57,D_134,E_135,F_131) = k2_xboole_0(k2_tarski(A_56,B_57),k1_enumset1(D_134,E_135,F_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_490])).

tff(c_1842,plain,(
    ! [B_212,F_213,A_215,D_211,E_214] : k2_xboole_0(k2_tarski(A_215,B_212),k1_enumset1(D_211,E_214,F_213)) = k3_enumset1(A_215,B_212,D_211,E_214,F_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_511])).

tff(c_1848,plain,(
    ! [B_212,F_213,A_215,D_211,E_214] : k2_xboole_0(k1_enumset1(D_211,E_214,F_213),k2_tarski(A_215,B_212)) = k3_enumset1(A_215,B_212,D_211,E_214,F_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_1842,c_2])).

tff(c_524,plain,(
    ! [A_56,F_131,B_57,D_134,E_135] : k2_xboole_0(k2_tarski(A_56,B_57),k1_enumset1(D_134,E_135,F_131)) = k3_enumset1(A_56,B_57,D_134,E_135,F_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_511])).

tff(c_2908,plain,(
    ! [C_244,A_246,B_243,A_245,B_242] : k4_enumset1(A_246,B_242,C_244,A_245,A_245,B_243) = k2_xboole_0(k1_enumset1(A_246,B_242,C_244),k2_tarski(A_245,B_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_490])).

tff(c_2927,plain,(
    ! [C_244,A_246,B_243,A_245,B_242] : k4_enumset1(A_246,B_242,C_244,A_245,A_245,B_243) = k2_xboole_0(k2_tarski(A_245,B_243),k1_enumset1(A_246,B_242,C_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2908,c_2])).

tff(c_2968,plain,(
    ! [C_244,A_246,B_243,A_245,B_242] : k4_enumset1(A_246,B_242,C_244,A_245,A_245,B_243) = k3_enumset1(A_245,B_243,A_246,B_242,C_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_2927])).

tff(c_2952,plain,(
    ! [C_244,A_246,A_7,B_242,B_8] : k4_enumset1(A_246,B_242,C_244,A_7,A_7,B_8) = k2_xboole_0(k1_enumset1(A_246,B_242,C_244),k2_tarski(B_8,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2908])).

tff(c_38065,plain,(
    ! [C_244,A_246,A_7,B_242,B_8] : k3_enumset1(B_8,A_7,A_246,B_242,C_244) = k3_enumset1(A_7,B_8,A_246,B_242,C_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_2968,c_2952])).

tff(c_3693,plain,(
    ! [C_270,A_271,B_272] : k2_enumset1(C_270,A_271,A_271,B_272) = k1_enumset1(A_271,B_272,C_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2088])).

tff(c_2087,plain,(
    ! [F_219,A_58,B_59,C_60] : k2_enumset1(F_219,A_58,B_59,C_60) = k2_enumset1(A_58,B_59,C_60,F_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_30,c_2078])).

tff(c_3730,plain,(
    ! [B_272,C_270,A_271] : k2_enumset1(B_272,C_270,A_271,A_271) = k1_enumset1(A_271,B_272,C_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_3693,c_2087])).

tff(c_24,plain,(
    ! [A_55] : k2_tarski(A_55,A_55) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2964,plain,(
    ! [A_246,B_242,C_244,A_55] : k4_enumset1(A_246,B_242,C_244,A_55,A_55,A_55) = k2_xboole_0(k1_enumset1(A_246,B_242,C_244),k1_tarski(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2908])).

tff(c_2975,plain,(
    ! [A_246,B_242,C_244,A_55] : k4_enumset1(A_246,B_242,C_244,A_55,A_55,A_55) = k2_enumset1(A_55,A_246,B_242,C_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_2964])).

tff(c_2033,plain,(
    ! [B_222,D_221,A_223,F_219,C_220] : k2_xboole_0(k1_tarski(F_219),k2_enumset1(A_223,B_222,C_220,D_221)) = k3_enumset1(A_223,B_222,C_220,D_221,F_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_2024,c_2])).

tff(c_34,plain,(
    ! [F_75,D_73,A_70,E_74,C_72,B_71] : k5_enumset1(A_70,A_70,B_71,C_72,D_73,E_74,F_75) = k4_enumset1(A_70,B_71,C_72,D_73,E_74,F_75) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1041,plain,(
    ! [F_163,D_166,A_165,G_167,C_164,B_162,E_161] : k2_xboole_0(k2_tarski(A_165,B_162),k3_enumset1(C_164,D_166,E_161,F_163,G_167)) = k5_enumset1(A_165,B_162,C_164,D_166,E_161,F_163,G_167) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6861,plain,(
    ! [C_337,A_341,B_339,D_338,B_336,A_340] : k5_enumset1(A_340,B_336,A_341,A_341,B_339,C_337,D_338) = k2_xboole_0(k2_tarski(A_340,B_336),k2_enumset1(A_341,B_339,C_337,D_338)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1041])).

tff(c_6952,plain,(
    ! [F_75,D_73,A_70,E_74,C_72] : k4_enumset1(A_70,C_72,C_72,D_73,E_74,F_75) = k2_xboole_0(k2_tarski(A_70,A_70),k2_enumset1(C_72,D_73,E_74,F_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6861])).

tff(c_6988,plain,(
    ! [F_75,D_73,A_70,E_74,C_72] : k4_enumset1(A_70,C_72,C_72,D_73,E_74,F_75) = k2_xboole_0(k1_tarski(A_70),k2_enumset1(C_72,D_73,E_74,F_75)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6952])).

tff(c_38285,plain,(
    ! [A_705,E_707,F_706,C_708,D_704] : k4_enumset1(A_705,C_708,C_708,D_704,E_707,F_706) = k3_enumset1(C_708,D_704,E_707,F_706,A_705) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_6988])).

tff(c_38365,plain,(
    ! [C_244,A_55,A_246] : k3_enumset1(C_244,A_55,A_55,A_55,A_246) = k2_enumset1(A_55,A_246,C_244,C_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_38285])).

tff(c_42634,plain,(
    ! [C_811,A_812,A_813] : k3_enumset1(C_811,A_812,A_812,A_812,A_813) = k1_enumset1(C_811,A_812,A_813) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_38365])).

tff(c_42796,plain,(
    ! [B_242,B_8,C_244] : k3_enumset1(B_242,B_8,B_242,B_242,C_244) = k1_enumset1(B_8,B_242,C_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_38065,c_42634])).

tff(c_1860,plain,(
    ! [A_215,B_212,A_56,B_57] : k3_enumset1(A_215,B_212,A_56,A_56,B_57) = k2_xboole_0(k2_tarski(A_215,B_212),k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1842])).

tff(c_195,plain,(
    ! [A_106,B_107] : k2_xboole_0(k1_tarski(A_106),k2_tarski(A_106,B_107)) = k1_enumset1(A_106,A_106,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_28])).

tff(c_233,plain,(
    ! [A_108,B_109] : k2_xboole_0(k1_tarski(A_108),k2_tarski(A_108,B_109)) = k2_tarski(A_108,B_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_195])).

tff(c_306,plain,(
    ! [B_118,A_119] : k2_xboole_0(k1_tarski(B_118),k2_tarski(A_119,B_118)) = k2_tarski(B_118,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_233])).

tff(c_316,plain,(
    ! [B_118,A_119] : k2_enumset1(B_118,A_119,A_119,B_118) = k2_tarski(B_118,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_176])).

tff(c_3942,plain,(
    ! [A_281,B_282] : k1_enumset1(A_281,B_282,B_282) = k2_tarski(B_282,A_281) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_3693])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3988,plain,(
    ! [A_15,B_282,A_281] : k2_xboole_0(k1_tarski(A_15),k2_tarski(B_282,A_281)) = k2_enumset1(A_15,A_281,B_282,B_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3942,c_12])).

tff(c_5534,plain,(
    ! [A_15,B_282,A_281] : k2_xboole_0(k1_tarski(A_15),k2_tarski(B_282,A_281)) = k1_enumset1(B_282,A_15,A_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3988])).

tff(c_832,plain,(
    ! [A_155,B_156,A_157] : k2_xboole_0(k1_tarski(A_155),k2_tarski(B_156,A_157)) = k2_xboole_0(k1_tarski(A_155),k2_tarski(A_157,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_176])).

tff(c_5586,plain,(
    ! [B_306,A_307,A_308] : k1_enumset1(B_306,A_307,A_308) = k1_enumset1(A_308,A_307,B_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5534,c_5534,c_832])).

tff(c_5763,plain,(
    ! [B_309,A_310,A_311] : k1_enumset1(B_309,A_310,A_311) = k1_enumset1(A_310,A_311,B_309) ),
    inference(superposition,[status(thm),theory(equality)],[c_5586,c_3690])).

tff(c_5535,plain,(
    ! [B_156,A_155,A_157] : k1_enumset1(B_156,A_155,A_157) = k1_enumset1(A_157,A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5534,c_5534,c_832])).

tff(c_5778,plain,(
    ! [B_309,A_311,A_310] : k1_enumset1(B_309,A_311,A_310) = k1_enumset1(B_309,A_310,A_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_5763,c_5535])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_38])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_39])).

tff(c_6051,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5778,c_40])).

tff(c_18708,plain,(
    k3_enumset1('#skF_1','#skF_3','#skF_1','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_6051])).

tff(c_44546,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42796,c_18708])).

tff(c_44549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3690,c_44546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.65/7.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.65/7.20  
% 13.65/7.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.65/7.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.65/7.20  
% 13.65/7.20  %Foreground sorts:
% 13.65/7.20  
% 13.65/7.20  
% 13.65/7.20  %Background operators:
% 13.65/7.20  
% 13.65/7.20  
% 13.65/7.20  %Foreground operators:
% 13.65/7.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.65/7.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.65/7.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.65/7.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.65/7.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.65/7.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.65/7.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.65/7.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.65/7.20  tff('#skF_2', type, '#skF_2': $i).
% 13.65/7.20  tff('#skF_3', type, '#skF_3': $i).
% 13.65/7.20  tff('#skF_1', type, '#skF_1': $i).
% 13.65/7.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.65/7.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.65/7.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.65/7.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.65/7.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.65/7.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.65/7.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.65/7.20  
% 13.65/7.22  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 13.65/7.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.65/7.22  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 13.65/7.22  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 13.65/7.22  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 13.65/7.22  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 13.65/7.22  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.65/7.22  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.65/7.22  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 13.65/7.22  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.65/7.22  tff(f_59, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 13.65/7.22  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 13.65/7.22  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 13.65/7.22  tff(c_28, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.65/7.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.65/7.22  tff(c_161, plain, (![A_101, B_102, C_103, D_104]: (k2_xboole_0(k1_tarski(A_101), k1_enumset1(B_102, C_103, D_104))=k2_enumset1(A_101, B_102, C_103, D_104))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.65/7.22  tff(c_179, plain, (![B_102, C_103, D_104, A_101]: (k2_xboole_0(k1_enumset1(B_102, C_103, D_104), k1_tarski(A_101))=k2_enumset1(A_101, B_102, C_103, D_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 13.65/7.22  tff(c_30, plain, (![A_61, B_62, C_63, D_64]: (k3_enumset1(A_61, A_61, B_62, C_63, D_64)=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.65/7.22  tff(c_32, plain, (![B_66, A_65, C_67, D_68, E_69]: (k4_enumset1(A_65, A_65, B_66, C_67, D_68, E_69)=k3_enumset1(A_65, B_66, C_67, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.65/7.22  tff(c_678, plain, (![C_140, A_143, D_145, B_142, E_141, F_144]: (k2_xboole_0(k3_enumset1(A_143, B_142, C_140, D_145, E_141), k1_tarski(F_144))=k4_enumset1(A_143, B_142, C_140, D_145, E_141, F_144))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.65/7.22  tff(c_693, plain, (![A_61, B_62, C_63, D_64, F_144]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, F_144)=k2_xboole_0(k2_enumset1(A_61, B_62, C_63, D_64), k1_tarski(F_144)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_678])).
% 13.65/7.22  tff(c_2024, plain, (![B_222, D_221, A_223, F_219, C_220]: (k2_xboole_0(k2_enumset1(A_223, B_222, C_220, D_221), k1_tarski(F_219))=k3_enumset1(A_223, B_222, C_220, D_221, F_219))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_693])).
% 13.65/7.22  tff(c_2078, plain, (![A_58, B_59, C_60, F_219]: (k3_enumset1(A_58, A_58, B_59, C_60, F_219)=k2_xboole_0(k1_enumset1(A_58, B_59, C_60), k1_tarski(F_219)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2024])).
% 13.65/7.22  tff(c_2088, plain, (![F_224, A_225, B_226, C_227]: (k2_enumset1(F_224, A_225, B_226, C_227)=k2_enumset1(A_225, B_226, C_227, F_224))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_30, c_2078])).
% 13.65/7.22  tff(c_2300, plain, (![C_60, A_58, B_59]: (k2_enumset1(C_60, A_58, A_58, B_59)=k1_enumset1(A_58, B_59, C_60))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2088])).
% 13.65/7.22  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.65/7.22  tff(c_26, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.65/7.22  tff(c_185, plain, (![A_105, A_106, B_107]: (k2_xboole_0(k1_tarski(A_105), k2_tarski(A_106, B_107))=k2_enumset1(A_105, A_106, A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 13.65/7.22  tff(c_787, plain, (![A_155, B_156, A_157]: (k2_xboole_0(k1_tarski(A_155), k2_tarski(B_156, A_157))=k2_enumset1(A_155, A_157, A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_8, c_185])).
% 13.65/7.22  tff(c_176, plain, (![A_101, A_56, B_57]: (k2_xboole_0(k1_tarski(A_101), k2_tarski(A_56, B_57))=k2_enumset1(A_101, A_56, A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 13.65/7.22  tff(c_835, plain, (![A_155, B_156, A_157]: (k2_enumset1(A_155, B_156, B_156, A_157)=k2_enumset1(A_155, A_157, A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_787, c_176])).
% 13.65/7.22  tff(c_3690, plain, (![B_156, A_157, A_155]: (k1_enumset1(B_156, A_157, A_155)=k1_enumset1(A_157, B_156, A_155))), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_2300, c_835])).
% 13.65/7.22  tff(c_490, plain, (![C_133, B_132, F_131, D_134, A_136, E_135]: (k2_xboole_0(k1_enumset1(A_136, B_132, C_133), k1_enumset1(D_134, E_135, F_131))=k4_enumset1(A_136, B_132, C_133, D_134, E_135, F_131))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.65/7.22  tff(c_511, plain, (![A_56, F_131, B_57, D_134, E_135]: (k4_enumset1(A_56, A_56, B_57, D_134, E_135, F_131)=k2_xboole_0(k2_tarski(A_56, B_57), k1_enumset1(D_134, E_135, F_131)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_490])).
% 13.65/7.22  tff(c_1842, plain, (![B_212, F_213, A_215, D_211, E_214]: (k2_xboole_0(k2_tarski(A_215, B_212), k1_enumset1(D_211, E_214, F_213))=k3_enumset1(A_215, B_212, D_211, E_214, F_213))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_511])).
% 13.65/7.22  tff(c_1848, plain, (![B_212, F_213, A_215, D_211, E_214]: (k2_xboole_0(k1_enumset1(D_211, E_214, F_213), k2_tarski(A_215, B_212))=k3_enumset1(A_215, B_212, D_211, E_214, F_213))), inference(superposition, [status(thm), theory('equality')], [c_1842, c_2])).
% 13.65/7.22  tff(c_524, plain, (![A_56, F_131, B_57, D_134, E_135]: (k2_xboole_0(k2_tarski(A_56, B_57), k1_enumset1(D_134, E_135, F_131))=k3_enumset1(A_56, B_57, D_134, E_135, F_131))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_511])).
% 13.65/7.22  tff(c_2908, plain, (![C_244, A_246, B_243, A_245, B_242]: (k4_enumset1(A_246, B_242, C_244, A_245, A_245, B_243)=k2_xboole_0(k1_enumset1(A_246, B_242, C_244), k2_tarski(A_245, B_243)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_490])).
% 13.65/7.22  tff(c_2927, plain, (![C_244, A_246, B_243, A_245, B_242]: (k4_enumset1(A_246, B_242, C_244, A_245, A_245, B_243)=k2_xboole_0(k2_tarski(A_245, B_243), k1_enumset1(A_246, B_242, C_244)))), inference(superposition, [status(thm), theory('equality')], [c_2908, c_2])).
% 13.65/7.22  tff(c_2968, plain, (![C_244, A_246, B_243, A_245, B_242]: (k4_enumset1(A_246, B_242, C_244, A_245, A_245, B_243)=k3_enumset1(A_245, B_243, A_246, B_242, C_244))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_2927])).
% 13.65/7.22  tff(c_2952, plain, (![C_244, A_246, A_7, B_242, B_8]: (k4_enumset1(A_246, B_242, C_244, A_7, A_7, B_8)=k2_xboole_0(k1_enumset1(A_246, B_242, C_244), k2_tarski(B_8, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2908])).
% 13.65/7.22  tff(c_38065, plain, (![C_244, A_246, A_7, B_242, B_8]: (k3_enumset1(B_8, A_7, A_246, B_242, C_244)=k3_enumset1(A_7, B_8, A_246, B_242, C_244))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_2968, c_2952])).
% 13.65/7.22  tff(c_3693, plain, (![C_270, A_271, B_272]: (k2_enumset1(C_270, A_271, A_271, B_272)=k1_enumset1(A_271, B_272, C_270))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2088])).
% 13.65/7.22  tff(c_2087, plain, (![F_219, A_58, B_59, C_60]: (k2_enumset1(F_219, A_58, B_59, C_60)=k2_enumset1(A_58, B_59, C_60, F_219))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_30, c_2078])).
% 13.65/7.22  tff(c_3730, plain, (![B_272, C_270, A_271]: (k2_enumset1(B_272, C_270, A_271, A_271)=k1_enumset1(A_271, B_272, C_270))), inference(superposition, [status(thm), theory('equality')], [c_3693, c_2087])).
% 13.65/7.22  tff(c_24, plain, (![A_55]: (k2_tarski(A_55, A_55)=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.65/7.22  tff(c_2964, plain, (![A_246, B_242, C_244, A_55]: (k4_enumset1(A_246, B_242, C_244, A_55, A_55, A_55)=k2_xboole_0(k1_enumset1(A_246, B_242, C_244), k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2908])).
% 13.65/7.22  tff(c_2975, plain, (![A_246, B_242, C_244, A_55]: (k4_enumset1(A_246, B_242, C_244, A_55, A_55, A_55)=k2_enumset1(A_55, A_246, B_242, C_244))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_2964])).
% 13.65/7.22  tff(c_2033, plain, (![B_222, D_221, A_223, F_219, C_220]: (k2_xboole_0(k1_tarski(F_219), k2_enumset1(A_223, B_222, C_220, D_221))=k3_enumset1(A_223, B_222, C_220, D_221, F_219))), inference(superposition, [status(thm), theory('equality')], [c_2024, c_2])).
% 13.65/7.22  tff(c_34, plain, (![F_75, D_73, A_70, E_74, C_72, B_71]: (k5_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75)=k4_enumset1(A_70, B_71, C_72, D_73, E_74, F_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.65/7.22  tff(c_1041, plain, (![F_163, D_166, A_165, G_167, C_164, B_162, E_161]: (k2_xboole_0(k2_tarski(A_165, B_162), k3_enumset1(C_164, D_166, E_161, F_163, G_167))=k5_enumset1(A_165, B_162, C_164, D_166, E_161, F_163, G_167))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.65/7.22  tff(c_6861, plain, (![C_337, A_341, B_339, D_338, B_336, A_340]: (k5_enumset1(A_340, B_336, A_341, A_341, B_339, C_337, D_338)=k2_xboole_0(k2_tarski(A_340, B_336), k2_enumset1(A_341, B_339, C_337, D_338)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1041])).
% 13.65/7.22  tff(c_6952, plain, (![F_75, D_73, A_70, E_74, C_72]: (k4_enumset1(A_70, C_72, C_72, D_73, E_74, F_75)=k2_xboole_0(k2_tarski(A_70, A_70), k2_enumset1(C_72, D_73, E_74, F_75)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6861])).
% 13.65/7.22  tff(c_6988, plain, (![F_75, D_73, A_70, E_74, C_72]: (k4_enumset1(A_70, C_72, C_72, D_73, E_74, F_75)=k2_xboole_0(k1_tarski(A_70), k2_enumset1(C_72, D_73, E_74, F_75)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6952])).
% 13.65/7.22  tff(c_38285, plain, (![A_705, E_707, F_706, C_708, D_704]: (k4_enumset1(A_705, C_708, C_708, D_704, E_707, F_706)=k3_enumset1(C_708, D_704, E_707, F_706, A_705))), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_6988])).
% 13.65/7.22  tff(c_38365, plain, (![C_244, A_55, A_246]: (k3_enumset1(C_244, A_55, A_55, A_55, A_246)=k2_enumset1(A_55, A_246, C_244, C_244))), inference(superposition, [status(thm), theory('equality')], [c_2975, c_38285])).
% 13.65/7.22  tff(c_42634, plain, (![C_811, A_812, A_813]: (k3_enumset1(C_811, A_812, A_812, A_812, A_813)=k1_enumset1(C_811, A_812, A_813))), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_38365])).
% 13.65/7.22  tff(c_42796, plain, (![B_242, B_8, C_244]: (k3_enumset1(B_242, B_8, B_242, B_242, C_244)=k1_enumset1(B_8, B_242, C_244))), inference(superposition, [status(thm), theory('equality')], [c_38065, c_42634])).
% 13.65/7.22  tff(c_1860, plain, (![A_215, B_212, A_56, B_57]: (k3_enumset1(A_215, B_212, A_56, A_56, B_57)=k2_xboole_0(k2_tarski(A_215, B_212), k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1842])).
% 13.65/7.22  tff(c_195, plain, (![A_106, B_107]: (k2_xboole_0(k1_tarski(A_106), k2_tarski(A_106, B_107))=k1_enumset1(A_106, A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_185, c_28])).
% 13.65/7.22  tff(c_233, plain, (![A_108, B_109]: (k2_xboole_0(k1_tarski(A_108), k2_tarski(A_108, B_109))=k2_tarski(A_108, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_195])).
% 13.65/7.22  tff(c_306, plain, (![B_118, A_119]: (k2_xboole_0(k1_tarski(B_118), k2_tarski(A_119, B_118))=k2_tarski(B_118, A_119))), inference(superposition, [status(thm), theory('equality')], [c_8, c_233])).
% 13.65/7.22  tff(c_316, plain, (![B_118, A_119]: (k2_enumset1(B_118, A_119, A_119, B_118)=k2_tarski(B_118, A_119))), inference(superposition, [status(thm), theory('equality')], [c_306, c_176])).
% 13.65/7.22  tff(c_3942, plain, (![A_281, B_282]: (k1_enumset1(A_281, B_282, B_282)=k2_tarski(B_282, A_281))), inference(superposition, [status(thm), theory('equality')], [c_316, c_3693])).
% 13.65/7.22  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.65/7.22  tff(c_3988, plain, (![A_15, B_282, A_281]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(B_282, A_281))=k2_enumset1(A_15, A_281, B_282, B_282))), inference(superposition, [status(thm), theory('equality')], [c_3942, c_12])).
% 13.65/7.22  tff(c_5534, plain, (![A_15, B_282, A_281]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(B_282, A_281))=k1_enumset1(B_282, A_15, A_281))), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3988])).
% 13.65/7.22  tff(c_832, plain, (![A_155, B_156, A_157]: (k2_xboole_0(k1_tarski(A_155), k2_tarski(B_156, A_157))=k2_xboole_0(k1_tarski(A_155), k2_tarski(A_157, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_787, c_176])).
% 13.65/7.22  tff(c_5586, plain, (![B_306, A_307, A_308]: (k1_enumset1(B_306, A_307, A_308)=k1_enumset1(A_308, A_307, B_306))), inference(demodulation, [status(thm), theory('equality')], [c_5534, c_5534, c_832])).
% 13.65/7.22  tff(c_5763, plain, (![B_309, A_310, A_311]: (k1_enumset1(B_309, A_310, A_311)=k1_enumset1(A_310, A_311, B_309))), inference(superposition, [status(thm), theory('equality')], [c_5586, c_3690])).
% 13.65/7.22  tff(c_5535, plain, (![B_156, A_155, A_157]: (k1_enumset1(B_156, A_155, A_157)=k1_enumset1(A_157, A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_5534, c_5534, c_832])).
% 13.65/7.22  tff(c_5778, plain, (![B_309, A_311, A_310]: (k1_enumset1(B_309, A_311, A_310)=k1_enumset1(B_309, A_310, A_311))), inference(superposition, [status(thm), theory('equality')], [c_5763, c_5535])).
% 13.65/7.22  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.65/7.22  tff(c_39, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_38])).
% 13.65/7.22  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_39])).
% 13.65/7.22  tff(c_6051, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5778, c_40])).
% 13.65/7.22  tff(c_18708, plain, (k3_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_6051])).
% 13.65/7.22  tff(c_44546, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42796, c_18708])).
% 13.65/7.22  tff(c_44549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3690, c_44546])).
% 13.65/7.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.65/7.22  
% 13.65/7.22  Inference rules
% 13.65/7.22  ----------------------
% 13.65/7.22  #Ref     : 0
% 13.65/7.22  #Sup     : 10589
% 13.65/7.22  #Fact    : 0
% 13.65/7.22  #Define  : 0
% 13.65/7.22  #Split   : 0
% 13.65/7.22  #Chain   : 0
% 13.65/7.22  #Close   : 0
% 13.65/7.22  
% 13.65/7.22  Ordering : KBO
% 13.65/7.22  
% 13.65/7.22  Simplification rules
% 13.65/7.22  ----------------------
% 13.65/7.22  #Subsume      : 2145
% 13.65/7.22  #Demod        : 10372
% 13.65/7.22  #Tautology    : 6598
% 13.65/7.22  #SimpNegUnit  : 0
% 13.65/7.22  #BackRed      : 18
% 13.65/7.22  
% 13.65/7.22  #Partial instantiations: 0
% 13.65/7.22  #Strategies tried      : 1
% 13.65/7.22  
% 13.65/7.22  Timing (in seconds)
% 13.65/7.22  ----------------------
% 13.65/7.22  Preprocessing        : 0.31
% 13.65/7.22  Parsing              : 0.16
% 13.65/7.22  CNF conversion       : 0.02
% 13.65/7.22  Main loop            : 6.12
% 13.65/7.22  Inferencing          : 1.20
% 13.65/7.22  Reduction            : 3.86
% 13.65/7.22  Demodulation         : 3.60
% 13.65/7.22  BG Simplification    : 0.12
% 13.65/7.22  Subsumption          : 0.72
% 13.65/7.23  Abstraction          : 0.24
% 13.65/7.23  MUC search           : 0.00
% 13.65/7.23  Cooper               : 0.00
% 13.65/7.23  Total                : 6.47
% 13.65/7.23  Index Insertion      : 0.00
% 13.65/7.23  Index Deletion       : 0.00
% 13.65/7.23  Index Matching       : 0.00
% 13.65/7.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

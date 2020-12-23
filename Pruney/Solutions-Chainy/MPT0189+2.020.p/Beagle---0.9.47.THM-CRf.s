%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 9.51s
% Output     : CNFRefutation 9.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 503 expanded)
%              Number of leaves         :   30 ( 181 expanded)
%              Depth                    :   15
%              Number of atoms          :   62 ( 485 expanded)
%              Number of equality atoms :   61 ( 484 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_21,C_23,D_24,B_22] : k2_enumset1(A_21,C_23,D_24,B_22) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_53,B_54,C_55,D_56] : k3_enumset1(A_53,A_53,B_54,C_55,D_56) = k2_enumset1(A_53,B_54,C_55,D_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_48,B_49] : k1_enumset1(A_48,A_48,B_49) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_346,plain,(
    ! [B_111,A_113,D_110,C_112,E_114] : k2_xboole_0(k1_enumset1(A_113,B_111,C_112),k2_tarski(D_110,E_114)) = k3_enumset1(A_113,B_111,C_112,D_110,E_114) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_367,plain,(
    ! [A_48,B_49,D_110,E_114] : k3_enumset1(A_48,A_48,B_49,D_110,E_114) = k2_xboole_0(k2_tarski(A_48,B_49),k2_tarski(D_110,E_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_346])).

tff(c_370,plain,(
    ! [A_48,B_49,D_110,E_114] : k2_xboole_0(k2_tarski(A_48,B_49),k2_tarski(D_110,E_114)) = k2_enumset1(A_48,B_49,D_110,E_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_367])).

tff(c_52,plain,(
    ! [B_79,C_80,A_81] : k1_enumset1(B_79,C_80,A_81) = k1_enumset1(A_81,B_79,C_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [B_79,C_80] : k1_enumset1(B_79,C_80,B_79) = k2_tarski(B_79,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_358,plain,(
    ! [B_79,C_80,D_110,E_114] : k3_enumset1(B_79,C_80,B_79,D_110,E_114) = k2_xboole_0(k2_tarski(B_79,C_80),k2_tarski(D_110,E_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_346])).

tff(c_400,plain,(
    ! [B_79,C_80,D_110,E_114] : k3_enumset1(B_79,C_80,B_79,D_110,E_114) = k2_enumset1(B_79,C_80,D_110,E_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_358])).

tff(c_26,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] : k4_enumset1(A_57,A_57,B_58,C_59,D_60,E_61) = k3_enumset1(A_57,B_58,C_59,D_60,E_61) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [B_63,E_66,F_67,C_64,A_62,D_65] : k5_enumset1(A_62,A_62,B_63,C_64,D_65,E_66,F_67) = k4_enumset1(A_62,B_63,C_64,D_65,E_66,F_67) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_25,G_31,F_30,E_29,C_27,D_28,B_26] : k2_xboole_0(k3_enumset1(A_25,B_26,C_27,D_28,E_29),k2_tarski(F_30,G_31)) = k5_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_678,plain,(
    ! [B_180,G_173,H_179,E_174,D_176,F_177,A_175,C_178] : k2_xboole_0(k3_enumset1(A_175,B_180,C_178,D_176,E_174),k1_enumset1(F_177,G_173,H_179)) = k6_enumset1(A_175,B_180,C_178,D_176,E_174,F_177,G_173,H_179) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_714,plain,(
    ! [B_180,B_49,E_174,A_48,D_176,A_175,C_178] : k6_enumset1(A_175,B_180,C_178,D_176,E_174,A_48,A_48,B_49) = k2_xboole_0(k3_enumset1(A_175,B_180,C_178,D_176,E_174),k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_678])).

tff(c_949,plain,(
    ! [D_217,A_213,B_216,E_212,B_214,A_215,C_218] : k6_enumset1(A_213,B_216,C_218,D_217,E_212,A_215,A_215,B_214) = k5_enumset1(A_213,B_216,C_218,D_217,E_212,A_215,B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_714])).

tff(c_30,plain,(
    ! [E_72,C_70,B_69,D_71,F_73,G_74,A_68] : k6_enumset1(A_68,A_68,B_69,C_70,D_71,E_72,F_73,G_74) = k5_enumset1(A_68,B_69,C_70,D_71,E_72,F_73,G_74) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_956,plain,(
    ! [D_217,B_216,E_212,B_214,A_215,C_218] : k5_enumset1(B_216,C_218,D_217,E_212,A_215,A_215,B_214) = k5_enumset1(B_216,B_216,C_218,D_217,E_212,A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_30])).

tff(c_968,plain,(
    ! [B_219,C_221,E_222,D_223,A_220,B_224] : k5_enumset1(B_219,C_221,D_223,E_222,A_220,A_220,B_224) = k4_enumset1(B_219,C_221,D_223,E_222,A_220,B_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_956])).

tff(c_975,plain,(
    ! [C_221,E_222,D_223,A_220,B_224] : k4_enumset1(C_221,D_223,E_222,A_220,A_220,B_224) = k4_enumset1(C_221,C_221,D_223,E_222,A_220,B_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_28])).

tff(c_1027,plain,(
    ! [C_234,E_233,B_236,A_237,D_235] : k4_enumset1(C_234,D_235,E_233,A_237,A_237,B_236) = k3_enumset1(C_234,D_235,E_233,A_237,B_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_975])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k2_tarski(D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_91,C_92,D_93,B_94] : k2_enumset1(A_91,C_92,D_93,B_94) = k2_enumset1(A_91,B_94,C_92,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_50,B_51,C_52] : k2_enumset1(A_50,A_50,B_51,C_52) = k1_enumset1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [C_92,B_94,D_93] : k2_enumset1(C_92,B_94,C_92,D_93) = k1_enumset1(C_92,D_93,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_22])).

tff(c_607,plain,(
    ! [C_158,D_155,G_156,F_159,A_157,B_160,E_161] : k2_xboole_0(k3_enumset1(A_157,B_160,C_158,D_155,E_161),k2_tarski(F_159,G_156)) = k5_enumset1(A_157,B_160,C_158,D_155,E_161,F_159,G_156) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_628,plain,(
    ! [A_53,G_156,D_56,F_159,C_55,B_54] : k5_enumset1(A_53,A_53,B_54,C_55,D_56,F_159,G_156) = k2_xboole_0(k2_enumset1(A_53,B_54,C_55,D_56),k2_tarski(F_159,G_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_607])).

tff(c_632,plain,(
    ! [G_165,C_163,D_166,B_167,F_162,A_164] : k2_xboole_0(k2_enumset1(A_164,B_167,C_163,D_166),k2_tarski(F_162,G_165)) = k4_enumset1(A_164,B_167,C_163,D_166,F_162,G_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_628])).

tff(c_641,plain,(
    ! [C_92,G_165,B_94,F_162,D_93] : k4_enumset1(C_92,B_94,C_92,D_93,F_162,G_165) = k2_xboole_0(k1_enumset1(C_92,D_93,B_94),k2_tarski(F_162,G_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_632])).

tff(c_656,plain,(
    ! [C_92,G_165,B_94,F_162,D_93] : k4_enumset1(C_92,B_94,C_92,D_93,F_162,G_165) = k3_enumset1(C_92,D_93,B_94,F_162,G_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_641])).

tff(c_1044,plain,(
    ! [E_233,D_235,A_237,B_236] : k3_enumset1(E_233,D_235,E_233,A_237,B_236) = k3_enumset1(E_233,A_237,D_235,A_237,B_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_656])).

tff(c_1080,plain,(
    ! [E_238,A_239,D_240,B_241] : k3_enumset1(E_238,A_239,D_240,A_239,B_241) = k2_enumset1(E_238,D_240,A_239,B_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_1044])).

tff(c_10,plain,(
    ! [B_19,C_20,A_18] : k1_enumset1(B_19,C_20,A_18) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_439,plain,(
    ! [B_137,C_136,E_133,D_134,A_135] : k2_xboole_0(k1_enumset1(B_137,C_136,A_135),k2_tarski(D_134,E_133)) = k3_enumset1(A_135,B_137,C_136,D_134,E_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_346])).

tff(c_445,plain,(
    ! [B_137,C_136,E_133,D_134,A_135] : k3_enumset1(B_137,C_136,A_135,D_134,E_133) = k3_enumset1(A_135,B_137,C_136,D_134,E_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_6])).

tff(c_1991,plain,(
    ! [D_280,E_281,A_282,B_283] : k3_enumset1(D_280,E_281,A_282,A_282,B_283) = k2_enumset1(E_281,D_280,A_282,B_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_445])).

tff(c_1048,plain,(
    ! [D_235,E_233,A_237,B_236] : k3_enumset1(D_235,E_233,A_237,A_237,B_236) = k3_enumset1(D_235,D_235,E_233,A_237,B_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_26])).

tff(c_1075,plain,(
    ! [D_235,E_233,A_237,B_236] : k3_enumset1(D_235,E_233,A_237,A_237,B_236) = k2_enumset1(D_235,E_233,A_237,B_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1048])).

tff(c_2079,plain,(
    ! [E_284,D_285,A_286,B_287] : k2_enumset1(E_284,D_285,A_286,B_287) = k2_enumset1(D_285,E_284,A_286,B_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_1075])).

tff(c_2269,plain,(
    ! [B_22,A_21,C_23,D_24] : k2_enumset1(B_22,A_21,C_23,D_24) = k2_enumset1(A_21,C_23,D_24,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2079])).

tff(c_2200,plain,(
    ! [E_284,B_287,D_285,A_286] : k2_enumset1(E_284,B_287,D_285,A_286) = k2_enumset1(D_285,E_284,A_286,B_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_12])).

tff(c_8017,plain,(
    ! [B_423,A_424,C_425,D_426] : k2_enumset1(B_423,A_424,C_425,D_426) = k2_enumset1(A_424,C_425,D_426,B_423) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2079])).

tff(c_11465,plain,(
    ! [E_451,B_452,D_453,A_454] : k2_enumset1(E_451,B_452,D_453,A_454) = k2_enumset1(B_452,D_453,E_451,A_454) ),
    inference(superposition,[status(thm),theory(equality)],[c_2200,c_8017])).

tff(c_11924,plain,(
    ! [A_21,C_23,D_24,B_22] : k2_enumset1(A_21,C_23,D_24,B_22) = k2_enumset1(A_21,C_23,B_22,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_11465])).

tff(c_1997,plain,(
    ! [E_281,D_280,A_282,B_283] : k2_enumset1(E_281,D_280,A_282,B_283) = k2_enumset1(D_280,E_281,A_282,B_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_1075])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_32])).

tff(c_2077,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_1997,c_33])).

tff(c_2078,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_2077])).

tff(c_17025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11924,c_2078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:36:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.51/3.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.54/3.60  
% 9.54/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.54/3.60  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.54/3.60  
% 9.54/3.60  %Foreground sorts:
% 9.54/3.60  
% 9.54/3.60  
% 9.54/3.60  %Background operators:
% 9.54/3.60  
% 9.54/3.60  
% 9.54/3.60  %Foreground operators:
% 9.54/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.54/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.54/3.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.54/3.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.54/3.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.54/3.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.54/3.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.54/3.60  tff('#skF_2', type, '#skF_2': $i).
% 9.54/3.60  tff('#skF_3', type, '#skF_3': $i).
% 9.54/3.60  tff('#skF_1', type, '#skF_1': $i).
% 9.54/3.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.54/3.60  tff('#skF_4', type, '#skF_4': $i).
% 9.54/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.54/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.54/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.54/3.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.60  
% 9.54/3.62  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 9.54/3.62  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 9.54/3.62  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.54/3.62  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 9.54/3.62  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 9.54/3.62  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 9.54/3.62  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 9.54/3.62  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 9.54/3.62  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 9.54/3.62  tff(f_55, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 9.54/3.62  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.54/3.62  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 9.54/3.62  tff(c_12, plain, (![A_21, C_23, D_24, B_22]: (k2_enumset1(A_21, C_23, D_24, B_22)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.54/3.62  tff(c_24, plain, (![A_53, B_54, C_55, D_56]: (k3_enumset1(A_53, A_53, B_54, C_55, D_56)=k2_enumset1(A_53, B_54, C_55, D_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.54/3.62  tff(c_20, plain, (![A_48, B_49]: (k1_enumset1(A_48, A_48, B_49)=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.54/3.62  tff(c_346, plain, (![B_111, A_113, D_110, C_112, E_114]: (k2_xboole_0(k1_enumset1(A_113, B_111, C_112), k2_tarski(D_110, E_114))=k3_enumset1(A_113, B_111, C_112, D_110, E_114))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.54/3.62  tff(c_367, plain, (![A_48, B_49, D_110, E_114]: (k3_enumset1(A_48, A_48, B_49, D_110, E_114)=k2_xboole_0(k2_tarski(A_48, B_49), k2_tarski(D_110, E_114)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_346])).
% 9.54/3.62  tff(c_370, plain, (![A_48, B_49, D_110, E_114]: (k2_xboole_0(k2_tarski(A_48, B_49), k2_tarski(D_110, E_114))=k2_enumset1(A_48, B_49, D_110, E_114))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_367])).
% 9.54/3.62  tff(c_52, plain, (![B_79, C_80, A_81]: (k1_enumset1(B_79, C_80, A_81)=k1_enumset1(A_81, B_79, C_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.54/3.62  tff(c_68, plain, (![B_79, C_80]: (k1_enumset1(B_79, C_80, B_79)=k2_tarski(B_79, C_80))), inference(superposition, [status(thm), theory('equality')], [c_52, c_20])).
% 9.54/3.62  tff(c_358, plain, (![B_79, C_80, D_110, E_114]: (k3_enumset1(B_79, C_80, B_79, D_110, E_114)=k2_xboole_0(k2_tarski(B_79, C_80), k2_tarski(D_110, E_114)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_346])).
% 9.54/3.62  tff(c_400, plain, (![B_79, C_80, D_110, E_114]: (k3_enumset1(B_79, C_80, B_79, D_110, E_114)=k2_enumset1(B_79, C_80, D_110, E_114))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_358])).
% 9.54/3.62  tff(c_26, plain, (![A_57, E_61, B_58, D_60, C_59]: (k4_enumset1(A_57, A_57, B_58, C_59, D_60, E_61)=k3_enumset1(A_57, B_58, C_59, D_60, E_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.54/3.62  tff(c_28, plain, (![B_63, E_66, F_67, C_64, A_62, D_65]: (k5_enumset1(A_62, A_62, B_63, C_64, D_65, E_66, F_67)=k4_enumset1(A_62, B_63, C_64, D_65, E_66, F_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.54/3.62  tff(c_14, plain, (![A_25, G_31, F_30, E_29, C_27, D_28, B_26]: (k2_xboole_0(k3_enumset1(A_25, B_26, C_27, D_28, E_29), k2_tarski(F_30, G_31))=k5_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.54/3.62  tff(c_678, plain, (![B_180, G_173, H_179, E_174, D_176, F_177, A_175, C_178]: (k2_xboole_0(k3_enumset1(A_175, B_180, C_178, D_176, E_174), k1_enumset1(F_177, G_173, H_179))=k6_enumset1(A_175, B_180, C_178, D_176, E_174, F_177, G_173, H_179))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.54/3.62  tff(c_714, plain, (![B_180, B_49, E_174, A_48, D_176, A_175, C_178]: (k6_enumset1(A_175, B_180, C_178, D_176, E_174, A_48, A_48, B_49)=k2_xboole_0(k3_enumset1(A_175, B_180, C_178, D_176, E_174), k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_678])).
% 9.54/3.62  tff(c_949, plain, (![D_217, A_213, B_216, E_212, B_214, A_215, C_218]: (k6_enumset1(A_213, B_216, C_218, D_217, E_212, A_215, A_215, B_214)=k5_enumset1(A_213, B_216, C_218, D_217, E_212, A_215, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_714])).
% 9.54/3.62  tff(c_30, plain, (![E_72, C_70, B_69, D_71, F_73, G_74, A_68]: (k6_enumset1(A_68, A_68, B_69, C_70, D_71, E_72, F_73, G_74)=k5_enumset1(A_68, B_69, C_70, D_71, E_72, F_73, G_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.54/3.62  tff(c_956, plain, (![D_217, B_216, E_212, B_214, A_215, C_218]: (k5_enumset1(B_216, C_218, D_217, E_212, A_215, A_215, B_214)=k5_enumset1(B_216, B_216, C_218, D_217, E_212, A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_949, c_30])).
% 9.54/3.62  tff(c_968, plain, (![B_219, C_221, E_222, D_223, A_220, B_224]: (k5_enumset1(B_219, C_221, D_223, E_222, A_220, A_220, B_224)=k4_enumset1(B_219, C_221, D_223, E_222, A_220, B_224))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_956])).
% 9.54/3.62  tff(c_975, plain, (![C_221, E_222, D_223, A_220, B_224]: (k4_enumset1(C_221, D_223, E_222, A_220, A_220, B_224)=k4_enumset1(C_221, C_221, D_223, E_222, A_220, B_224))), inference(superposition, [status(thm), theory('equality')], [c_968, c_28])).
% 9.54/3.62  tff(c_1027, plain, (![C_234, E_233, B_236, A_237, D_235]: (k4_enumset1(C_234, D_235, E_233, A_237, A_237, B_236)=k3_enumset1(C_234, D_235, E_233, A_237, B_236))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_975])).
% 9.54/3.62  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k2_tarski(D_8, E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.54/3.62  tff(c_199, plain, (![A_91, C_92, D_93, B_94]: (k2_enumset1(A_91, C_92, D_93, B_94)=k2_enumset1(A_91, B_94, C_92, D_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.54/3.62  tff(c_22, plain, (![A_50, B_51, C_52]: (k2_enumset1(A_50, A_50, B_51, C_52)=k1_enumset1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.54/3.62  tff(c_219, plain, (![C_92, B_94, D_93]: (k2_enumset1(C_92, B_94, C_92, D_93)=k1_enumset1(C_92, D_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_199, c_22])).
% 9.54/3.62  tff(c_607, plain, (![C_158, D_155, G_156, F_159, A_157, B_160, E_161]: (k2_xboole_0(k3_enumset1(A_157, B_160, C_158, D_155, E_161), k2_tarski(F_159, G_156))=k5_enumset1(A_157, B_160, C_158, D_155, E_161, F_159, G_156))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.54/3.62  tff(c_628, plain, (![A_53, G_156, D_56, F_159, C_55, B_54]: (k5_enumset1(A_53, A_53, B_54, C_55, D_56, F_159, G_156)=k2_xboole_0(k2_enumset1(A_53, B_54, C_55, D_56), k2_tarski(F_159, G_156)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_607])).
% 9.54/3.62  tff(c_632, plain, (![G_165, C_163, D_166, B_167, F_162, A_164]: (k2_xboole_0(k2_enumset1(A_164, B_167, C_163, D_166), k2_tarski(F_162, G_165))=k4_enumset1(A_164, B_167, C_163, D_166, F_162, G_165))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_628])).
% 9.54/3.62  tff(c_641, plain, (![C_92, G_165, B_94, F_162, D_93]: (k4_enumset1(C_92, B_94, C_92, D_93, F_162, G_165)=k2_xboole_0(k1_enumset1(C_92, D_93, B_94), k2_tarski(F_162, G_165)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_632])).
% 9.54/3.62  tff(c_656, plain, (![C_92, G_165, B_94, F_162, D_93]: (k4_enumset1(C_92, B_94, C_92, D_93, F_162, G_165)=k3_enumset1(C_92, D_93, B_94, F_162, G_165))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_641])).
% 9.54/3.62  tff(c_1044, plain, (![E_233, D_235, A_237, B_236]: (k3_enumset1(E_233, D_235, E_233, A_237, B_236)=k3_enumset1(E_233, A_237, D_235, A_237, B_236))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_656])).
% 9.54/3.62  tff(c_1080, plain, (![E_238, A_239, D_240, B_241]: (k3_enumset1(E_238, A_239, D_240, A_239, B_241)=k2_enumset1(E_238, D_240, A_239, B_241))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_1044])).
% 9.54/3.62  tff(c_10, plain, (![B_19, C_20, A_18]: (k1_enumset1(B_19, C_20, A_18)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.54/3.62  tff(c_439, plain, (![B_137, C_136, E_133, D_134, A_135]: (k2_xboole_0(k1_enumset1(B_137, C_136, A_135), k2_tarski(D_134, E_133))=k3_enumset1(A_135, B_137, C_136, D_134, E_133))), inference(superposition, [status(thm), theory('equality')], [c_10, c_346])).
% 9.54/3.62  tff(c_445, plain, (![B_137, C_136, E_133, D_134, A_135]: (k3_enumset1(B_137, C_136, A_135, D_134, E_133)=k3_enumset1(A_135, B_137, C_136, D_134, E_133))), inference(superposition, [status(thm), theory('equality')], [c_439, c_6])).
% 9.54/3.62  tff(c_1991, plain, (![D_280, E_281, A_282, B_283]: (k3_enumset1(D_280, E_281, A_282, A_282, B_283)=k2_enumset1(E_281, D_280, A_282, B_283))), inference(superposition, [status(thm), theory('equality')], [c_1080, c_445])).
% 9.54/3.62  tff(c_1048, plain, (![D_235, E_233, A_237, B_236]: (k3_enumset1(D_235, E_233, A_237, A_237, B_236)=k3_enumset1(D_235, D_235, E_233, A_237, B_236))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_26])).
% 9.54/3.62  tff(c_1075, plain, (![D_235, E_233, A_237, B_236]: (k3_enumset1(D_235, E_233, A_237, A_237, B_236)=k2_enumset1(D_235, E_233, A_237, B_236))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1048])).
% 9.54/3.62  tff(c_2079, plain, (![E_284, D_285, A_286, B_287]: (k2_enumset1(E_284, D_285, A_286, B_287)=k2_enumset1(D_285, E_284, A_286, B_287))), inference(superposition, [status(thm), theory('equality')], [c_1991, c_1075])).
% 9.54/3.62  tff(c_2269, plain, (![B_22, A_21, C_23, D_24]: (k2_enumset1(B_22, A_21, C_23, D_24)=k2_enumset1(A_21, C_23, D_24, B_22))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2079])).
% 9.54/3.62  tff(c_2200, plain, (![E_284, B_287, D_285, A_286]: (k2_enumset1(E_284, B_287, D_285, A_286)=k2_enumset1(D_285, E_284, A_286, B_287))), inference(superposition, [status(thm), theory('equality')], [c_2079, c_12])).
% 9.54/3.62  tff(c_8017, plain, (![B_423, A_424, C_425, D_426]: (k2_enumset1(B_423, A_424, C_425, D_426)=k2_enumset1(A_424, C_425, D_426, B_423))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2079])).
% 9.54/3.62  tff(c_11465, plain, (![E_451, B_452, D_453, A_454]: (k2_enumset1(E_451, B_452, D_453, A_454)=k2_enumset1(B_452, D_453, E_451, A_454))), inference(superposition, [status(thm), theory('equality')], [c_2200, c_8017])).
% 9.54/3.62  tff(c_11924, plain, (![A_21, C_23, D_24, B_22]: (k2_enumset1(A_21, C_23, D_24, B_22)=k2_enumset1(A_21, C_23, B_22, D_24))), inference(superposition, [status(thm), theory('equality')], [c_2269, c_11465])).
% 9.54/3.62  tff(c_1997, plain, (![E_281, D_280, A_282, B_283]: (k2_enumset1(E_281, D_280, A_282, B_283)=k2_enumset1(D_280, E_281, A_282, B_283))), inference(superposition, [status(thm), theory('equality')], [c_1991, c_1075])).
% 9.54/3.62  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.54/3.62  tff(c_33, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_32])).
% 9.54/3.62  tff(c_2077, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1997, c_1997, c_33])).
% 9.54/3.62  tff(c_2078, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_2077])).
% 9.54/3.62  tff(c_17025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11924, c_2078])).
% 9.54/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.54/3.62  
% 9.54/3.62  Inference rules
% 9.54/3.62  ----------------------
% 9.54/3.62  #Ref     : 0
% 9.54/3.62  #Sup     : 4331
% 9.54/3.62  #Fact    : 0
% 9.54/3.62  #Define  : 0
% 9.54/3.62  #Split   : 0
% 9.54/3.62  #Chain   : 0
% 9.54/3.62  #Close   : 0
% 9.54/3.62  
% 9.54/3.62  Ordering : KBO
% 9.54/3.62  
% 9.54/3.62  Simplification rules
% 9.54/3.62  ----------------------
% 9.54/3.62  #Subsume      : 904
% 9.54/3.62  #Demod        : 2970
% 9.54/3.62  #Tautology    : 2152
% 9.54/3.62  #SimpNegUnit  : 0
% 9.54/3.62  #BackRed      : 2
% 9.54/3.62  
% 9.54/3.62  #Partial instantiations: 0
% 9.54/3.62  #Strategies tried      : 1
% 9.54/3.62  
% 9.54/3.62  Timing (in seconds)
% 9.54/3.62  ----------------------
% 9.68/3.62  Preprocessing        : 0.32
% 9.68/3.62  Parsing              : 0.17
% 9.68/3.62  CNF conversion       : 0.02
% 9.68/3.62  Main loop            : 2.54
% 9.68/3.62  Inferencing          : 0.63
% 9.68/3.62  Reduction            : 1.49
% 9.68/3.62  Demodulation         : 1.37
% 9.68/3.62  BG Simplification    : 0.08
% 9.68/3.62  Subsumption          : 0.26
% 9.68/3.62  Abstraction          : 0.14
% 9.68/3.62  MUC search           : 0.00
% 9.68/3.62  Cooper               : 0.00
% 9.68/3.62  Total                : 2.90
% 9.68/3.62  Index Insertion      : 0.00
% 9.68/3.62  Index Deletion       : 0.00
% 9.68/3.62  Index Matching       : 0.00
% 9.68/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------

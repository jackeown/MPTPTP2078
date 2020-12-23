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
% DateTime   : Thu Dec  3 09:51:59 EST 2020

% Result     : Theorem 37.27s
% Output     : CNFRefutation 37.27s
% Verified   : 
% Statistics : Number of formulae       :  132 (1059 expanded)
%              Number of leaves         :   43 ( 381 expanded)
%              Depth                    :   17
%              Number of atoms          :  112 (1039 expanded)
%              Number of equality atoms :  111 (1038 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_726,plain,(
    ! [A_165,B_166] : k5_xboole_0(k5_xboole_0(A_165,B_166),k2_xboole_0(A_165,B_166)) = k3_xboole_0(A_165,B_166) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_753,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_726])).

tff(c_763,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_753])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_852,plain,(
    ! [A_170,B_171,C_172] : k5_xboole_0(k5_xboole_0(A_170,B_171),C_172) = k5_xboole_0(A_170,k5_xboole_0(B_171,C_172)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1077,plain,(
    ! [A_177,B_178] : k5_xboole_0(A_177,k5_xboole_0(B_178,k5_xboole_0(A_177,B_178))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_14])).

tff(c_909,plain,(
    ! [A_13,C_172] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_172)) = k5_xboole_0(k1_xboole_0,C_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_852])).

tff(c_922,plain,(
    ! [A_13,C_172] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_172)) = C_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_909])).

tff(c_1085,plain,(
    ! [B_178,A_177] : k5_xboole_0(B_178,k5_xboole_0(A_177,B_178)) = k5_xboole_0(A_177,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_922])).

tff(c_1179,plain,(
    ! [B_179,A_180] : k5_xboole_0(B_179,k5_xboole_0(A_180,B_179)) = A_180 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1085])).

tff(c_1188,plain,(
    ! [B_179,A_180] : k5_xboole_0(B_179,A_180) = k5_xboole_0(A_180,B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_922])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_750,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),k1_xboole_0) = k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_726])).

tff(c_1025,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_922])).

tff(c_2177,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_1188,c_1025])).

tff(c_1159,plain,(
    ! [B_178,A_177] : k5_xboole_0(B_178,k5_xboole_0(A_177,B_178)) = A_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1085])).

tff(c_1182,plain,(
    ! [A_180,B_179] : k5_xboole_0(k5_xboole_0(A_180,B_179),A_180) = B_179 ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_1159])).

tff(c_2184,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k5_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_1182])).

tff(c_2199,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_2184])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2218,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2199,c_8])).

tff(c_2222,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2218])).

tff(c_153,plain,(
    ! [B_132,C_133,A_134] : k1_enumset1(B_132,C_133,A_134) = k1_enumset1(A_134,B_132,C_133) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_88,B_89] : k1_enumset1(A_88,A_88,B_89) = k2_tarski(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [A_134,C_133] : k1_enumset1(A_134,C_133,C_133) = k2_tarski(C_133,A_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_42])).

tff(c_431,plain,(
    ! [A_155,C_156,B_157,D_158] : k2_enumset1(A_155,C_156,B_157,D_158) = k2_enumset1(A_155,B_157,C_156,D_158) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_90,B_91,C_92] : k2_enumset1(A_90,A_90,B_91,C_92) = k1_enumset1(A_90,B_91,C_92) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_467,plain,(
    ! [B_157,C_156,D_158] : k2_enumset1(B_157,C_156,B_157,D_158) = k1_enumset1(B_157,C_156,D_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_44])).

tff(c_46,plain,(
    ! [A_93,B_94,C_95,D_96] : k3_enumset1(A_93,A_93,B_94,C_95,D_96) = k2_enumset1(A_93,B_94,C_95,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_351,plain,(
    ! [A_148,B_149,D_150,C_151] : k2_enumset1(A_148,B_149,D_150,C_151) = k2_enumset1(A_148,B_149,C_151,D_150) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_367,plain,(
    ! [B_149,D_150,C_151] : k2_enumset1(B_149,B_149,D_150,C_151) = k1_enumset1(B_149,C_151,D_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_44])).

tff(c_48,plain,(
    ! [C_99,B_98,D_100,E_101,A_97] : k4_enumset1(A_97,A_97,B_98,C_99,D_100,E_101) = k3_enumset1(A_97,B_98,C_99,D_100,E_101) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2234,plain,(
    ! [C_215,F_214,E_217,D_216,B_218,A_219] : k2_xboole_0(k3_enumset1(A_219,B_218,C_215,D_216,E_217),k1_tarski(F_214)) = k4_enumset1(A_219,B_218,C_215,D_216,E_217,F_214) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2246,plain,(
    ! [F_214,D_96,C_95,B_94,A_93] : k4_enumset1(A_93,A_93,B_94,C_95,D_96,F_214) = k2_xboole_0(k2_enumset1(A_93,B_94,C_95,D_96),k1_tarski(F_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2234])).

tff(c_10059,plain,(
    ! [B_368,A_369,F_372,D_371,C_370] : k2_xboole_0(k2_enumset1(A_369,B_368,C_370,D_371),k1_tarski(F_372)) = k3_enumset1(A_369,B_368,C_370,D_371,F_372) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2246])).

tff(c_10119,plain,(
    ! [B_149,D_150,C_151,F_372] : k3_enumset1(B_149,B_149,D_150,C_151,F_372) = k2_xboole_0(k1_enumset1(B_149,C_151,D_150),k1_tarski(F_372)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_10059])).

tff(c_76785,plain,(
    ! [B_779,C_780,D_781,F_782] : k2_xboole_0(k1_enumset1(B_779,C_780,D_781),k1_tarski(F_782)) = k2_enumset1(B_779,D_781,C_780,F_782) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10119])).

tff(c_76899,plain,(
    ! [A_88,B_89,F_782] : k2_xboole_0(k2_tarski(A_88,B_89),k1_tarski(F_782)) = k2_enumset1(A_88,B_89,A_88,F_782) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_76785])).

tff(c_76904,plain,(
    ! [A_88,B_89,F_782] : k2_xboole_0(k2_tarski(A_88,B_89),k1_tarski(F_782)) = k1_enumset1(A_88,B_89,F_782) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_76899])).

tff(c_10128,plain,(
    ! [A_90,B_91,C_92,F_372] : k3_enumset1(A_90,A_90,B_91,C_92,F_372) = k2_xboole_0(k1_enumset1(A_90,B_91,C_92),k1_tarski(F_372)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10059])).

tff(c_88095,plain,(
    ! [A_810,B_811,C_812,F_813] : k2_xboole_0(k1_enumset1(A_810,B_811,C_812),k1_tarski(F_813)) = k2_enumset1(A_810,B_811,C_812,F_813) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10128])).

tff(c_88209,plain,(
    ! [C_133,A_134,F_813] : k2_xboole_0(k2_tarski(C_133,A_134),k1_tarski(F_813)) = k2_enumset1(A_134,C_133,C_133,F_813) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_88095])).

tff(c_91477,plain,(
    ! [A_828,C_829,F_830] : k2_enumset1(A_828,C_829,C_829,F_830) = k1_enumset1(C_829,A_828,F_830) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76904,c_88209])).

tff(c_20,plain,(
    ! [A_19,B_20,D_22,C_21] : k2_enumset1(A_19,B_20,D_22,C_21) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3145,plain,(
    ! [C_272,B_273,D_274] : k2_enumset1(C_272,B_273,C_272,D_274) = k1_enumset1(C_272,D_274,B_273) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_367])).

tff(c_3204,plain,(
    ! [C_21,B_20,D_22] : k2_enumset1(C_21,B_20,D_22,C_21) = k1_enumset1(C_21,D_22,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3145])).

tff(c_91538,plain,(
    ! [F_830,C_829] : k1_enumset1(F_830,C_829,C_829) = k1_enumset1(C_829,F_830,F_830) ),
    inference(superposition,[status(thm),theory(equality)],[c_91477,c_3204])).

tff(c_91657,plain,(
    ! [F_831,C_832] : k2_tarski(F_831,C_832) = k2_tarski(C_832,F_831) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_91538])).

tff(c_54,plain,(
    ! [A_115,B_116] : k3_tarski(k2_tarski(A_115,B_116)) = k2_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_91765,plain,(
    ! [F_833,C_834] : k3_tarski(k2_tarski(F_833,C_834)) = k2_xboole_0(C_834,F_833) ),
    inference(superposition,[status(thm),theory(equality)],[c_91657,c_54])).

tff(c_91794,plain,(
    ! [F_835,C_836] : k2_xboole_0(F_835,C_836) = k2_xboole_0(C_836,F_835) ),
    inference(superposition,[status(thm),theory(equality)],[c_91765,c_54])).

tff(c_92207,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91794,c_58])).

tff(c_92445,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_92207])).

tff(c_50,plain,(
    ! [A_102,C_104,B_103,F_107,E_106,D_105] : k5_enumset1(A_102,A_102,B_103,C_104,D_105,E_106,F_107) = k4_enumset1(A_102,B_103,C_104,D_105,E_106,F_107) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ! [C_110,A_108,F_113,D_111,B_109,G_114,E_112] : k6_enumset1(A_108,A_108,B_109,C_110,D_111,E_112,F_113,G_114) = k5_enumset1(A_108,B_109,C_110,D_111,E_112,F_113,G_114) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_87] : k2_tarski(A_87,A_87) = k1_tarski(A_87) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4254,plain,(
    ! [H_315,B_316,E_313,C_317,F_312,G_310,A_311,D_314] : k2_xboole_0(k2_tarski(A_311,B_316),k4_enumset1(C_317,D_314,E_313,F_312,G_310,H_315)) = k6_enumset1(A_311,B_316,C_317,D_314,E_313,F_312,G_310,H_315) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4278,plain,(
    ! [A_87,H_315,E_313,C_317,F_312,G_310,D_314] : k6_enumset1(A_87,A_87,C_317,D_314,E_313,F_312,G_310,H_315) = k2_xboole_0(k1_tarski(A_87),k4_enumset1(C_317,D_314,E_313,F_312,G_310,H_315)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4254])).

tff(c_43760,plain,(
    ! [H_545,F_546,C_543,G_542,D_540,E_544,A_541] : k2_xboole_0(k1_tarski(A_541),k4_enumset1(C_543,D_540,E_544,F_546,G_542,H_545)) = k5_enumset1(A_541,C_543,D_540,E_544,F_546,G_542,H_545) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4278])).

tff(c_56,plain,(
    ! [A_117,B_118] : k2_xboole_0(k1_tarski(A_117),B_118) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43825,plain,(
    ! [D_548,H_550,E_549,A_553,G_547,F_551,C_552] : k5_enumset1(A_553,C_552,D_548,E_549,F_551,G_547,H_550) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43760,c_56])).

tff(c_43830,plain,(
    ! [D_555,B_557,C_554,A_558,E_556,F_559] : k4_enumset1(A_558,B_557,C_554,D_555,E_556,F_559) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_43825])).

tff(c_43833,plain,(
    ! [B_563,D_564,C_562,E_560,A_561] : k3_enumset1(A_561,B_563,C_562,D_564,E_560) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_43830])).

tff(c_43837,plain,(
    ! [A_565,B_566,C_567,D_568] : k2_enumset1(A_565,B_566,C_567,D_568) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_43833])).

tff(c_43866,plain,(
    ! [C_569,D_570,B_571] : k1_enumset1(C_569,D_570,B_571) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3204,c_43837])).

tff(c_43880,plain,(
    ! [C_133,A_134] : k2_tarski(C_133,A_134) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_43866])).

tff(c_92459,plain,(
    ! [C_133,A_134] : k2_tarski(C_133,A_134) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92445,c_43880])).

tff(c_295,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k3_xboole_0(A_141,B_142)) = k4_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_304,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_295])).

tff(c_308,plain,(
    ! [A_143] : k4_xboole_0(A_143,A_143) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_304])).

tff(c_313,plain,(
    ! [A_143] : k2_xboole_0(A_143,k1_xboole_0) = k2_xboole_0(A_143,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_8])).

tff(c_317,plain,(
    ! [A_143] : k2_xboole_0(A_143,k1_xboole_0) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_313])).

tff(c_766,plain,(
    ! [A_167] : k5_xboole_0(k1_xboole_0,A_167) = A_167 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_753])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1658,plain,(
    ! [A_191] : k5_xboole_0(A_191,k2_xboole_0(k1_xboole_0,A_191)) = k3_xboole_0(k1_xboole_0,A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_16])).

tff(c_1857,plain,(
    ! [A_200] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_200),k3_xboole_0(k1_xboole_0,A_200)) = A_200 ),
    inference(superposition,[status(thm),theory(equality)],[c_1658,c_1159])).

tff(c_1872,plain,(
    ! [A_200] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_200),A_200) = k3_xboole_0(k1_xboole_0,A_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_922])).

tff(c_92168,plain,(
    ! [C_836] : k5_xboole_0(k2_xboole_0(C_836,k1_xboole_0),C_836) = k3_xboole_0(k1_xboole_0,C_836) ),
    inference(superposition,[status(thm),theory(equality)],[c_91794,c_1872])).

tff(c_92440,plain,(
    ! [C_836] : k3_xboole_0(k1_xboole_0,C_836) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_317,c_92168])).

tff(c_96424,plain,(
    ! [C_836] : k3_xboole_0('#skF_3',C_836) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92445,c_92445,c_92440])).

tff(c_2228,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') = k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_16])).

tff(c_2231,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_2228])).

tff(c_96425,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96424,c_2231])).

tff(c_97579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92459,c_96425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.27/27.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.27/27.38  
% 37.27/27.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.27/27.38  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 37.27/27.38  
% 37.27/27.38  %Foreground sorts:
% 37.27/27.38  
% 37.27/27.38  
% 37.27/27.38  %Background operators:
% 37.27/27.38  
% 37.27/27.38  
% 37.27/27.38  %Foreground operators:
% 37.27/27.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.27/27.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 37.27/27.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 37.27/27.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.27/27.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 37.27/27.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 37.27/27.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 37.27/27.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 37.27/27.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 37.27/27.38  tff('#skF_2', type, '#skF_2': $i).
% 37.27/27.38  tff('#skF_3', type, '#skF_3': $i).
% 37.27/27.38  tff('#skF_1', type, '#skF_1': $i).
% 37.27/27.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 37.27/27.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 37.27/27.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.27/27.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 37.27/27.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.27/27.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 37.27/27.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 37.27/27.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 37.27/27.38  
% 37.27/27.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 37.27/27.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 37.27/27.40  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 37.27/27.40  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 37.27/27.40  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 37.27/27.40  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 37.27/27.40  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 37.27/27.40  tff(f_86, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 37.27/27.40  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 37.27/27.40  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 37.27/27.40  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 37.27/27.40  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 37.27/27.40  tff(f_69, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 37.27/27.40  tff(f_71, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 37.27/27.40  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 37.27/27.40  tff(f_73, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 37.27/27.40  tff(f_49, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 37.27/27.40  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 37.27/27.40  tff(f_75, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 37.27/27.40  tff(f_77, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 37.27/27.40  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 37.27/27.40  tff(f_55, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 37.27/27.40  tff(f_82, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 37.27/27.40  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 37.27/27.40  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 37.27/27.40  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 37.27/27.40  tff(c_726, plain, (![A_165, B_166]: (k5_xboole_0(k5_xboole_0(A_165, B_166), k2_xboole_0(A_165, B_166))=k3_xboole_0(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_41])).
% 37.27/27.40  tff(c_753, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_726])).
% 37.27/27.40  tff(c_763, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_753])).
% 37.27/27.40  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.27/27.40  tff(c_12, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 37.27/27.40  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 37.27/27.40  tff(c_852, plain, (![A_170, B_171, C_172]: (k5_xboole_0(k5_xboole_0(A_170, B_171), C_172)=k5_xboole_0(A_170, k5_xboole_0(B_171, C_172)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 37.27/27.40  tff(c_1077, plain, (![A_177, B_178]: (k5_xboole_0(A_177, k5_xboole_0(B_178, k5_xboole_0(A_177, B_178)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_852, c_14])).
% 37.27/27.40  tff(c_909, plain, (![A_13, C_172]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_172))=k5_xboole_0(k1_xboole_0, C_172))), inference(superposition, [status(thm), theory('equality')], [c_14, c_852])).
% 37.27/27.40  tff(c_922, plain, (![A_13, C_172]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_172))=C_172)), inference(demodulation, [status(thm), theory('equality')], [c_763, c_909])).
% 37.27/27.40  tff(c_1085, plain, (![B_178, A_177]: (k5_xboole_0(B_178, k5_xboole_0(A_177, B_178))=k5_xboole_0(A_177, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_922])).
% 37.27/27.40  tff(c_1179, plain, (![B_179, A_180]: (k5_xboole_0(B_179, k5_xboole_0(A_180, B_179))=A_180)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1085])).
% 37.27/27.40  tff(c_1188, plain, (![B_179, A_180]: (k5_xboole_0(B_179, A_180)=k5_xboole_0(A_180, B_179))), inference(superposition, [status(thm), theory('equality')], [c_1179, c_922])).
% 37.27/27.40  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 37.27/27.40  tff(c_750, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), k1_xboole_0)=k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_726])).
% 37.27/27.40  tff(c_1025, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_750, c_922])).
% 37.27/27.40  tff(c_2177, plain, (k5_xboole_0('#skF_3', k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_1188, c_1025])).
% 37.27/27.40  tff(c_1159, plain, (![B_178, A_177]: (k5_xboole_0(B_178, k5_xboole_0(A_177, B_178))=A_177)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1085])).
% 37.27/27.40  tff(c_1182, plain, (![A_180, B_179]: (k5_xboole_0(k5_xboole_0(A_180, B_179), A_180)=B_179)), inference(superposition, [status(thm), theory('equality')], [c_1179, c_1159])).
% 37.27/27.40  tff(c_2184, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k5_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2177, c_1182])).
% 37.27/27.40  tff(c_2199, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_763, c_2184])).
% 37.27/27.40  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 37.27/27.40  tff(c_2218, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2199, c_8])).
% 37.27/27.40  tff(c_2222, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2218])).
% 37.27/27.40  tff(c_153, plain, (![B_132, C_133, A_134]: (k1_enumset1(B_132, C_133, A_134)=k1_enumset1(A_134, B_132, C_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.27/27.40  tff(c_42, plain, (![A_88, B_89]: (k1_enumset1(A_88, A_88, B_89)=k2_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 37.27/27.40  tff(c_173, plain, (![A_134, C_133]: (k1_enumset1(A_134, C_133, C_133)=k2_tarski(C_133, A_134))), inference(superposition, [status(thm), theory('equality')], [c_153, c_42])).
% 37.27/27.40  tff(c_431, plain, (![A_155, C_156, B_157, D_158]: (k2_enumset1(A_155, C_156, B_157, D_158)=k2_enumset1(A_155, B_157, C_156, D_158))), inference(cnfTransformation, [status(thm)], [f_47])).
% 37.27/27.40  tff(c_44, plain, (![A_90, B_91, C_92]: (k2_enumset1(A_90, A_90, B_91, C_92)=k1_enumset1(A_90, B_91, C_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 37.27/27.40  tff(c_467, plain, (![B_157, C_156, D_158]: (k2_enumset1(B_157, C_156, B_157, D_158)=k1_enumset1(B_157, C_156, D_158))), inference(superposition, [status(thm), theory('equality')], [c_431, c_44])).
% 37.27/27.40  tff(c_46, plain, (![A_93, B_94, C_95, D_96]: (k3_enumset1(A_93, A_93, B_94, C_95, D_96)=k2_enumset1(A_93, B_94, C_95, D_96))), inference(cnfTransformation, [status(thm)], [f_71])).
% 37.27/27.40  tff(c_351, plain, (![A_148, B_149, D_150, C_151]: (k2_enumset1(A_148, B_149, D_150, C_151)=k2_enumset1(A_148, B_149, C_151, D_150))), inference(cnfTransformation, [status(thm)], [f_45])).
% 37.27/27.40  tff(c_367, plain, (![B_149, D_150, C_151]: (k2_enumset1(B_149, B_149, D_150, C_151)=k1_enumset1(B_149, C_151, D_150))), inference(superposition, [status(thm), theory('equality')], [c_351, c_44])).
% 37.27/27.40  tff(c_48, plain, (![C_99, B_98, D_100, E_101, A_97]: (k4_enumset1(A_97, A_97, B_98, C_99, D_100, E_101)=k3_enumset1(A_97, B_98, C_99, D_100, E_101))), inference(cnfTransformation, [status(thm)], [f_73])).
% 37.27/27.40  tff(c_2234, plain, (![C_215, F_214, E_217, D_216, B_218, A_219]: (k2_xboole_0(k3_enumset1(A_219, B_218, C_215, D_216, E_217), k1_tarski(F_214))=k4_enumset1(A_219, B_218, C_215, D_216, E_217, F_214))), inference(cnfTransformation, [status(thm)], [f_49])).
% 37.27/27.40  tff(c_2246, plain, (![F_214, D_96, C_95, B_94, A_93]: (k4_enumset1(A_93, A_93, B_94, C_95, D_96, F_214)=k2_xboole_0(k2_enumset1(A_93, B_94, C_95, D_96), k1_tarski(F_214)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2234])).
% 37.27/27.40  tff(c_10059, plain, (![B_368, A_369, F_372, D_371, C_370]: (k2_xboole_0(k2_enumset1(A_369, B_368, C_370, D_371), k1_tarski(F_372))=k3_enumset1(A_369, B_368, C_370, D_371, F_372))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2246])).
% 37.27/27.40  tff(c_10119, plain, (![B_149, D_150, C_151, F_372]: (k3_enumset1(B_149, B_149, D_150, C_151, F_372)=k2_xboole_0(k1_enumset1(B_149, C_151, D_150), k1_tarski(F_372)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_10059])).
% 37.27/27.40  tff(c_76785, plain, (![B_779, C_780, D_781, F_782]: (k2_xboole_0(k1_enumset1(B_779, C_780, D_781), k1_tarski(F_782))=k2_enumset1(B_779, D_781, C_780, F_782))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10119])).
% 37.27/27.40  tff(c_76899, plain, (![A_88, B_89, F_782]: (k2_xboole_0(k2_tarski(A_88, B_89), k1_tarski(F_782))=k2_enumset1(A_88, B_89, A_88, F_782))), inference(superposition, [status(thm), theory('equality')], [c_42, c_76785])).
% 37.27/27.40  tff(c_76904, plain, (![A_88, B_89, F_782]: (k2_xboole_0(k2_tarski(A_88, B_89), k1_tarski(F_782))=k1_enumset1(A_88, B_89, F_782))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_76899])).
% 37.27/27.40  tff(c_10128, plain, (![A_90, B_91, C_92, F_372]: (k3_enumset1(A_90, A_90, B_91, C_92, F_372)=k2_xboole_0(k1_enumset1(A_90, B_91, C_92), k1_tarski(F_372)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10059])).
% 37.27/27.40  tff(c_88095, plain, (![A_810, B_811, C_812, F_813]: (k2_xboole_0(k1_enumset1(A_810, B_811, C_812), k1_tarski(F_813))=k2_enumset1(A_810, B_811, C_812, F_813))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10128])).
% 37.27/27.40  tff(c_88209, plain, (![C_133, A_134, F_813]: (k2_xboole_0(k2_tarski(C_133, A_134), k1_tarski(F_813))=k2_enumset1(A_134, C_133, C_133, F_813))), inference(superposition, [status(thm), theory('equality')], [c_173, c_88095])).
% 37.27/27.40  tff(c_91477, plain, (![A_828, C_829, F_830]: (k2_enumset1(A_828, C_829, C_829, F_830)=k1_enumset1(C_829, A_828, F_830))), inference(demodulation, [status(thm), theory('equality')], [c_76904, c_88209])).
% 37.27/27.40  tff(c_20, plain, (![A_19, B_20, D_22, C_21]: (k2_enumset1(A_19, B_20, D_22, C_21)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 37.27/27.40  tff(c_3145, plain, (![C_272, B_273, D_274]: (k2_enumset1(C_272, B_273, C_272, D_274)=k1_enumset1(C_272, D_274, B_273))), inference(superposition, [status(thm), theory('equality')], [c_431, c_367])).
% 37.27/27.40  tff(c_3204, plain, (![C_21, B_20, D_22]: (k2_enumset1(C_21, B_20, D_22, C_21)=k1_enumset1(C_21, D_22, B_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3145])).
% 37.27/27.40  tff(c_91538, plain, (![F_830, C_829]: (k1_enumset1(F_830, C_829, C_829)=k1_enumset1(C_829, F_830, F_830))), inference(superposition, [status(thm), theory('equality')], [c_91477, c_3204])).
% 37.27/27.40  tff(c_91657, plain, (![F_831, C_832]: (k2_tarski(F_831, C_832)=k2_tarski(C_832, F_831))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_91538])).
% 37.27/27.40  tff(c_54, plain, (![A_115, B_116]: (k3_tarski(k2_tarski(A_115, B_116))=k2_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_79])).
% 37.27/27.40  tff(c_91765, plain, (![F_833, C_834]: (k3_tarski(k2_tarski(F_833, C_834))=k2_xboole_0(C_834, F_833))), inference(superposition, [status(thm), theory('equality')], [c_91657, c_54])).
% 37.27/27.40  tff(c_91794, plain, (![F_835, C_836]: (k2_xboole_0(F_835, C_836)=k2_xboole_0(C_836, F_835))), inference(superposition, [status(thm), theory('equality')], [c_91765, c_54])).
% 37.27/27.40  tff(c_92207, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91794, c_58])).
% 37.27/27.40  tff(c_92445, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2222, c_92207])).
% 37.27/27.40  tff(c_50, plain, (![A_102, C_104, B_103, F_107, E_106, D_105]: (k5_enumset1(A_102, A_102, B_103, C_104, D_105, E_106, F_107)=k4_enumset1(A_102, B_103, C_104, D_105, E_106, F_107))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.27/27.40  tff(c_52, plain, (![C_110, A_108, F_113, D_111, B_109, G_114, E_112]: (k6_enumset1(A_108, A_108, B_109, C_110, D_111, E_112, F_113, G_114)=k5_enumset1(A_108, B_109, C_110, D_111, E_112, F_113, G_114))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.27/27.40  tff(c_40, plain, (![A_87]: (k2_tarski(A_87, A_87)=k1_tarski(A_87))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.27/27.40  tff(c_4254, plain, (![H_315, B_316, E_313, C_317, F_312, G_310, A_311, D_314]: (k2_xboole_0(k2_tarski(A_311, B_316), k4_enumset1(C_317, D_314, E_313, F_312, G_310, H_315))=k6_enumset1(A_311, B_316, C_317, D_314, E_313, F_312, G_310, H_315))), inference(cnfTransformation, [status(thm)], [f_55])).
% 37.27/27.40  tff(c_4278, plain, (![A_87, H_315, E_313, C_317, F_312, G_310, D_314]: (k6_enumset1(A_87, A_87, C_317, D_314, E_313, F_312, G_310, H_315)=k2_xboole_0(k1_tarski(A_87), k4_enumset1(C_317, D_314, E_313, F_312, G_310, H_315)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4254])).
% 37.27/27.40  tff(c_43760, plain, (![H_545, F_546, C_543, G_542, D_540, E_544, A_541]: (k2_xboole_0(k1_tarski(A_541), k4_enumset1(C_543, D_540, E_544, F_546, G_542, H_545))=k5_enumset1(A_541, C_543, D_540, E_544, F_546, G_542, H_545))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4278])).
% 37.27/27.40  tff(c_56, plain, (![A_117, B_118]: (k2_xboole_0(k1_tarski(A_117), B_118)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 37.27/27.40  tff(c_43825, plain, (![D_548, H_550, E_549, A_553, G_547, F_551, C_552]: (k5_enumset1(A_553, C_552, D_548, E_549, F_551, G_547, H_550)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43760, c_56])).
% 37.27/27.40  tff(c_43830, plain, (![D_555, B_557, C_554, A_558, E_556, F_559]: (k4_enumset1(A_558, B_557, C_554, D_555, E_556, F_559)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_43825])).
% 37.27/27.40  tff(c_43833, plain, (![B_563, D_564, C_562, E_560, A_561]: (k3_enumset1(A_561, B_563, C_562, D_564, E_560)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_43830])).
% 37.27/27.40  tff(c_43837, plain, (![A_565, B_566, C_567, D_568]: (k2_enumset1(A_565, B_566, C_567, D_568)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_43833])).
% 37.27/27.40  tff(c_43866, plain, (![C_569, D_570, B_571]: (k1_enumset1(C_569, D_570, B_571)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3204, c_43837])).
% 37.27/27.40  tff(c_43880, plain, (![C_133, A_134]: (k2_tarski(C_133, A_134)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_43866])).
% 37.27/27.40  tff(c_92459, plain, (![C_133, A_134]: (k2_tarski(C_133, A_134)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92445, c_43880])).
% 37.27/27.40  tff(c_295, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k3_xboole_0(A_141, B_142))=k4_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.27/27.40  tff(c_304, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_295])).
% 37.27/27.40  tff(c_308, plain, (![A_143]: (k4_xboole_0(A_143, A_143)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_304])).
% 37.27/27.40  tff(c_313, plain, (![A_143]: (k2_xboole_0(A_143, k1_xboole_0)=k2_xboole_0(A_143, A_143))), inference(superposition, [status(thm), theory('equality')], [c_308, c_8])).
% 37.27/27.40  tff(c_317, plain, (![A_143]: (k2_xboole_0(A_143, k1_xboole_0)=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_313])).
% 37.27/27.40  tff(c_766, plain, (![A_167]: (k5_xboole_0(k1_xboole_0, A_167)=A_167)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_753])).
% 37.27/27.40  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 37.27/27.40  tff(c_1658, plain, (![A_191]: (k5_xboole_0(A_191, k2_xboole_0(k1_xboole_0, A_191))=k3_xboole_0(k1_xboole_0, A_191))), inference(superposition, [status(thm), theory('equality')], [c_766, c_16])).
% 37.27/27.40  tff(c_1857, plain, (![A_200]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_200), k3_xboole_0(k1_xboole_0, A_200))=A_200)), inference(superposition, [status(thm), theory('equality')], [c_1658, c_1159])).
% 37.27/27.40  tff(c_1872, plain, (![A_200]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_200), A_200)=k3_xboole_0(k1_xboole_0, A_200))), inference(superposition, [status(thm), theory('equality')], [c_1857, c_922])).
% 37.27/27.40  tff(c_92168, plain, (![C_836]: (k5_xboole_0(k2_xboole_0(C_836, k1_xboole_0), C_836)=k3_xboole_0(k1_xboole_0, C_836))), inference(superposition, [status(thm), theory('equality')], [c_91794, c_1872])).
% 37.27/27.40  tff(c_92440, plain, (![C_836]: (k3_xboole_0(k1_xboole_0, C_836)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_317, c_92168])).
% 37.27/27.40  tff(c_96424, plain, (![C_836]: (k3_xboole_0('#skF_3', C_836)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92445, c_92445, c_92440])).
% 37.27/27.40  tff(c_2228, plain, (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')=k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2222, c_16])).
% 37.27/27.40  tff(c_2231, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_2228])).
% 37.27/27.40  tff(c_96425, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96424, c_2231])).
% 37.27/27.40  tff(c_97579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92459, c_96425])).
% 37.27/27.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.27/27.40  
% 37.27/27.40  Inference rules
% 37.27/27.40  ----------------------
% 37.27/27.40  #Ref     : 0
% 37.27/27.40  #Sup     : 25569
% 37.27/27.40  #Fact    : 0
% 37.27/27.40  #Define  : 0
% 37.27/27.40  #Split   : 0
% 37.27/27.40  #Chain   : 0
% 37.27/27.40  #Close   : 0
% 37.27/27.40  
% 37.27/27.40  Ordering : KBO
% 37.27/27.40  
% 37.27/27.40  Simplification rules
% 37.27/27.40  ----------------------
% 37.27/27.40  #Subsume      : 1867
% 37.27/27.40  #Demod        : 43021
% 37.27/27.40  #Tautology    : 9058
% 37.27/27.40  #SimpNegUnit  : 1
% 37.27/27.40  #BackRed      : 84
% 37.27/27.40  
% 37.27/27.40  #Partial instantiations: 0
% 37.27/27.40  #Strategies tried      : 1
% 37.27/27.40  
% 37.27/27.40  Timing (in seconds)
% 37.27/27.40  ----------------------
% 37.27/27.40  Preprocessing        : 0.35
% 37.27/27.40  Parsing              : 0.19
% 37.27/27.40  CNF conversion       : 0.02
% 37.27/27.40  Main loop            : 26.27
% 37.27/27.40  Inferencing          : 2.30
% 37.27/27.40  Reduction            : 19.79
% 37.27/27.40  Demodulation         : 19.00
% 37.27/27.40  BG Simplification    : 0.44
% 37.27/27.40  Subsumption          : 2.97
% 37.27/27.40  Abstraction          : 0.74
% 37.27/27.40  MUC search           : 0.00
% 37.27/27.40  Cooper               : 0.00
% 37.27/27.41  Total                : 26.67
% 37.27/27.41  Index Insertion      : 0.00
% 37.27/27.41  Index Deletion       : 0.00
% 37.27/27.41  Index Matching       : 0.00
% 37.27/27.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

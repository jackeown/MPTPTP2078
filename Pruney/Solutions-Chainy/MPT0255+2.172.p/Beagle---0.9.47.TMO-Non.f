%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:59 EST 2020

% Result     : Timeout 59.11s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  135 (1293 expanded)
%              Number of leaves         :   42 ( 459 expanded)
%              Depth                    :   18
%              Number of atoms          :  115 (1273 expanded)
%              Number of equality atoms :  114 (1272 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_74,axiom,(
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

tff(c_368,plain,(
    ! [A_126,B_127] : k5_xboole_0(k5_xboole_0(A_126,B_127),k2_xboole_0(A_126,B_127)) = k3_xboole_0(A_126,B_127) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_417,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_368])).

tff(c_427,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_417])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_214,plain,(
    ! [A_120,B_121,C_122] : k5_xboole_0(k5_xboole_0(A_120,B_121),C_122) = k5_xboole_0(A_120,k5_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_232,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k5_xboole_0(B_121,k5_xboole_0(A_120,B_121))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_14])).

tff(c_255,plain,(
    ! [A_13,C_122] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_122)) = k5_xboole_0(k1_xboole_0,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_214])).

tff(c_677,plain,(
    ! [A_137,C_138] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_138)) = C_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_255])).

tff(c_730,plain,(
    ! [B_121,A_120] : k5_xboole_0(B_121,k5_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_677])).

tff(c_770,plain,(
    ! [B_139,A_140] : k5_xboole_0(B_139,k5_xboole_0(A_140,B_139)) = A_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_730])).

tff(c_676,plain,(
    ! [A_13,C_122] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_122)) = C_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_255])).

tff(c_779,plain,(
    ! [B_139,A_140] : k5_xboole_0(B_139,A_140) = k5_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_676])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_414,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),k1_xboole_0) = k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_368])).

tff(c_717,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_677])).

tff(c_1915,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_779,c_717])).

tff(c_763,plain,(
    ! [B_121,A_120] : k5_xboole_0(B_121,k5_xboole_0(A_120,B_121)) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_730])).

tff(c_773,plain,(
    ! [A_140,B_139] : k5_xboole_0(k5_xboole_0(A_140,B_139),A_140) = B_139 ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_763])).

tff(c_1922,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k5_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_773])).

tff(c_1937,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_1922])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1956,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1937,c_8])).

tff(c_1960,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1956])).

tff(c_34,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_81,F_86,D_84,B_82,E_85,C_83] : k5_enumset1(A_81,A_81,B_82,C_83,D_84,E_85,F_86) = k4_enumset1(A_81,B_82,C_83,D_84,E_85,F_86) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [A_69,B_70,C_71] : k2_enumset1(A_69,A_69,B_70,C_71) = k1_enumset1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_87,C_89,G_93,B_88,E_91,F_92,D_90] : k6_enumset1(A_87,A_87,B_88,C_89,D_90,E_91,F_92,G_93) = k5_enumset1(A_87,B_88,C_89,D_90,E_91,F_92,G_93) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_72,B_73,C_74,D_75] : k3_enumset1(A_72,A_72,B_73,C_74,D_75) = k2_enumset1(A_72,B_73,C_74,D_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2375,plain,(
    ! [B_208,H_211,E_206,C_213,A_210,D_207,F_212,G_209] : k2_xboole_0(k3_enumset1(A_210,B_208,C_213,D_207,E_206),k1_enumset1(F_212,G_209,H_211)) = k6_enumset1(A_210,B_208,C_213,D_207,E_206,F_212,G_209,H_211) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2390,plain,(
    ! [H_211,B_73,C_74,A_72,F_212,D_75,G_209] : k6_enumset1(A_72,A_72,B_73,C_74,D_75,F_212,G_209,H_211) = k2_xboole_0(k2_enumset1(A_72,B_73,C_74,D_75),k1_enumset1(F_212,G_209,H_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2375])).

tff(c_36204,plain,(
    ! [F_513,B_510,D_516,C_514,H_515,A_512,G_511] : k2_xboole_0(k2_enumset1(A_512,B_510,C_514,D_516),k1_enumset1(F_513,G_511,H_515)) = k5_enumset1(A_512,B_510,C_514,D_516,F_513,G_511,H_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2390])).

tff(c_36288,plain,(
    ! [F_513,B_70,H_515,C_71,A_69,G_511] : k5_enumset1(A_69,A_69,B_70,C_71,F_513,G_511,H_515) = k2_xboole_0(k1_enumset1(A_69,B_70,C_71),k1_enumset1(F_513,G_511,H_515)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_36204])).

tff(c_108234,plain,(
    ! [G_800,B_798,F_803,C_801,A_799,H_802] : k2_xboole_0(k1_enumset1(A_799,B_798,C_801),k1_enumset1(F_803,G_800,H_802)) = k4_enumset1(A_799,B_798,C_801,F_803,G_800,H_802) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36288])).

tff(c_137567,plain,(
    ! [A_910,B_911,C_912] : k4_enumset1(A_910,B_911,C_912,A_910,B_911,C_912) = k1_enumset1(A_910,B_911,C_912) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108234])).

tff(c_40,plain,(
    ! [B_77,A_76,C_78,E_80,D_79] : k4_enumset1(A_76,A_76,B_77,C_78,D_79,E_80) = k3_enumset1(A_76,B_77,C_78,D_79,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2094,plain,(
    ! [E_188,A_191,F_185,B_189,D_187,G_190,C_186] : k2_xboole_0(k3_enumset1(A_191,B_189,C_186,D_187,E_188),k2_tarski(F_185,G_190)) = k5_enumset1(A_191,B_189,C_186,D_187,E_188,F_185,G_190) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2106,plain,(
    ! [F_185,B_73,C_74,A_72,D_75,G_190] : k5_enumset1(A_72,A_72,B_73,C_74,D_75,F_185,G_190) = k2_xboole_0(k2_enumset1(A_72,B_73,C_74,D_75),k2_tarski(F_185,G_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2094])).

tff(c_18774,plain,(
    ! [A_353,G_355,C_354,F_352,D_356,B_351] : k2_xboole_0(k2_enumset1(A_353,B_351,C_354,D_356),k2_tarski(F_352,G_355)) = k4_enumset1(A_353,B_351,C_354,D_356,F_352,G_355) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2106])).

tff(c_18834,plain,(
    ! [B_70,G_355,F_352,C_71,A_69] : k4_enumset1(A_69,A_69,B_70,C_71,F_352,G_355) = k2_xboole_0(k1_enumset1(A_69,B_70,C_71),k2_tarski(F_352,G_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_18774])).

tff(c_18840,plain,(
    ! [B_70,G_355,F_352,C_71,A_69] : k2_xboole_0(k1_enumset1(A_69,B_70,C_71),k2_tarski(F_352,G_355)) = k3_enumset1(A_69,B_70,C_71,F_352,G_355) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18834])).

tff(c_541,plain,(
    ! [B_131,D_132,A_133,C_134] : k2_enumset1(B_131,D_132,A_133,C_134) = k2_enumset1(A_133,B_131,C_134,D_132) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_576,plain,(
    ! [B_70,A_69,C_71] : k2_enumset1(B_70,A_69,C_71,A_69) = k1_enumset1(A_69,B_70,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_541])).

tff(c_18822,plain,(
    ! [B_70,G_355,F_352,C_71,A_69] : k4_enumset1(B_70,A_69,C_71,A_69,F_352,G_355) = k2_xboole_0(k1_enumset1(A_69,B_70,C_71),k2_tarski(F_352,G_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_18774])).

tff(c_90556,plain,(
    ! [B_70,G_355,F_352,C_71,A_69] : k4_enumset1(B_70,A_69,C_71,A_69,F_352,G_355) = k3_enumset1(A_69,B_70,C_71,F_352,G_355) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18840,c_18822])).

tff(c_137586,plain,(
    ! [A_910,C_912] : k3_enumset1(A_910,A_910,C_912,A_910,C_912) = k1_enumset1(A_910,A_910,C_912) ),
    inference(superposition,[status(thm),theory(equality)],[c_137567,c_90556])).

tff(c_137675,plain,(
    ! [A_913,C_914] : k3_enumset1(A_913,A_913,C_914,A_913,C_914) = k2_tarski(A_913,C_914) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137586])).

tff(c_138374,plain,(
    ! [A_919,C_920] : k2_enumset1(A_919,C_920,A_919,C_920) = k2_tarski(A_919,C_920) ),
    inference(superposition,[status(thm),theory(equality)],[c_137675,c_38])).

tff(c_138437,plain,(
    ! [C_920,A_919] : k1_enumset1(C_920,A_919,A_919) = k2_tarski(A_919,C_920) ),
    inference(superposition,[status(thm),theory(equality)],[c_138374,c_576])).

tff(c_2400,plain,(
    ! [B_214,A_215,C_216] : k2_enumset1(B_214,A_215,C_216,A_215) = k1_enumset1(A_215,B_214,C_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_541])).

tff(c_557,plain,(
    ! [B_131,D_132,C_134] : k2_enumset1(B_131,D_132,B_131,C_134) = k1_enumset1(B_131,C_134,D_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_36])).

tff(c_2407,plain,(
    ! [C_216,A_215] : k1_enumset1(C_216,A_215,A_215) = k1_enumset1(A_215,C_216,C_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_557])).

tff(c_138585,plain,(
    ! [C_923,A_924] : k2_tarski(C_923,A_924) = k2_tarski(A_924,C_923) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138437,c_138437,c_2407])).

tff(c_46,plain,(
    ! [A_94,B_95] : k3_tarski(k2_tarski(A_94,B_95)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138842,plain,(
    ! [A_927,C_928] : k3_tarski(k2_tarski(A_927,C_928)) = k2_xboole_0(C_928,A_927) ),
    inference(superposition,[status(thm),theory(equality)],[c_138585,c_46])).

tff(c_138873,plain,(
    ! [C_929,A_930] : k2_xboole_0(C_929,A_930) = k2_xboole_0(A_930,C_929) ),
    inference(superposition,[status(thm),theory(equality)],[c_138842,c_46])).

tff(c_139356,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138873,c_50])).

tff(c_139626,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1960,c_139356])).

tff(c_2321,plain,(
    ! [B_201,D_202,C_203] : k2_enumset1(B_201,D_202,B_201,C_203) = k1_enumset1(B_201,C_203,D_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_36])).

tff(c_2334,plain,(
    ! [D_202,C_203] : k1_enumset1(D_202,D_202,C_203) = k1_enumset1(D_202,C_203,D_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_2321,c_36])).

tff(c_2352,plain,(
    ! [D_202,C_203] : k1_enumset1(D_202,C_203,D_202) = k2_tarski(D_202,C_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2334])).

tff(c_32,plain,(
    ! [A_66] : k2_tarski(A_66,A_66) = k1_tarski(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2227,plain,(
    ! [E_197,G_194,F_199,C_193,D_196,A_198,B_195] : k2_xboole_0(k2_tarski(A_198,B_195),k3_enumset1(C_193,D_196,E_197,F_199,G_194)) = k5_enumset1(A_198,B_195,C_193,D_196,E_197,F_199,G_194) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2242,plain,(
    ! [E_197,G_194,F_199,C_193,D_196,A_66] : k5_enumset1(A_66,A_66,C_193,D_196,E_197,F_199,G_194) = k2_xboole_0(k1_tarski(A_66),k3_enumset1(C_193,D_196,E_197,F_199,G_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2227])).

tff(c_24690,plain,(
    ! [C_381,G_382,D_377,A_378,F_379,E_380] : k2_xboole_0(k1_tarski(A_378),k3_enumset1(C_381,D_377,E_380,F_379,G_382)) = k4_enumset1(A_378,C_381,D_377,E_380,F_379,G_382) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2242])).

tff(c_48,plain,(
    ! [A_96,B_97] : k2_xboole_0(k1_tarski(A_96),B_97) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24743,plain,(
    ! [D_387,A_386,F_383,G_384,E_388,C_385] : k4_enumset1(A_386,C_385,D_387,E_388,F_383,G_384) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24690,c_48])).

tff(c_24746,plain,(
    ! [A_391,D_393,E_390,B_389,C_392] : k3_enumset1(A_391,B_389,C_392,D_393,E_390) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_24743])).

tff(c_24749,plain,(
    ! [A_394,B_395,C_396,D_397] : k2_enumset1(A_394,B_395,C_396,D_397) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_24746])).

tff(c_24767,plain,(
    ! [A_398,B_399,C_400] : k1_enumset1(A_398,B_399,C_400) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_24749])).

tff(c_24773,plain,(
    ! [D_202,C_203] : k2_tarski(D_202,C_203) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_24767])).

tff(c_139654,plain,(
    ! [D_202,C_203] : k2_tarski(D_202,C_203) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139626,c_24773])).

tff(c_158,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_158])).

tff(c_171,plain,(
    ! [A_115] : k4_xboole_0(A_115,A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_176,plain,(
    ! [A_115] : k2_xboole_0(A_115,k1_xboole_0) = k2_xboole_0(A_115,A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_180,plain,(
    ! [A_115] : k2_xboole_0(A_115,k1_xboole_0) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_432,plain,(
    ! [A_128] : k5_xboole_0(k1_xboole_0,A_128) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_417])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1248,plain,(
    ! [A_151] : k5_xboole_0(A_151,k2_xboole_0(k1_xboole_0,A_151)) = k3_xboole_0(k1_xboole_0,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_16])).

tff(c_1447,plain,(
    ! [A_160] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_160),k3_xboole_0(k1_xboole_0,A_160)) = A_160 ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_763])).

tff(c_1462,plain,(
    ! [A_160] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_160),A_160) = k3_xboole_0(k1_xboole_0,A_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_676])).

tff(c_139305,plain,(
    ! [C_929] : k5_xboole_0(k2_xboole_0(C_929,k1_xboole_0),C_929) = k3_xboole_0(k1_xboole_0,C_929) ),
    inference(superposition,[status(thm),theory(equality)],[c_138873,c_1462])).

tff(c_139618,plain,(
    ! [C_929] : k3_xboole_0(k1_xboole_0,C_929) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_180,c_139305])).

tff(c_143047,plain,(
    ! [C_929] : k3_xboole_0('#skF_3',C_929) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139626,c_139626,c_139618])).

tff(c_1966,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') = k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_16])).

tff(c_1969,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_1966])).

tff(c_143048,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143047,c_1969])).

tff(c_144937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139654,c_143048])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.11/48.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.11/48.06  
% 59.11/48.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.11/48.07  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 59.11/48.07  
% 59.11/48.07  %Foreground sorts:
% 59.11/48.07  
% 59.11/48.07  
% 59.11/48.07  %Background operators:
% 59.11/48.07  
% 59.11/48.07  
% 59.11/48.07  %Foreground operators:
% 59.11/48.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.11/48.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 59.11/48.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 59.11/48.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 59.11/48.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 59.11/48.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 59.11/48.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 59.11/48.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 59.11/48.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 59.11/48.07  tff('#skF_2', type, '#skF_2': $i).
% 59.11/48.07  tff('#skF_3', type, '#skF_3': $i).
% 59.11/48.07  tff('#skF_1', type, '#skF_1': $i).
% 59.11/48.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 59.11/48.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 59.11/48.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.11/48.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 59.11/48.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.11/48.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 59.11/48.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 59.11/48.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 59.11/48.07  
% 59.11/48.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 59.11/48.09  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 59.11/48.09  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 59.11/48.09  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 59.11/48.09  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 59.11/48.09  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 59.11/48.09  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 59.11/48.09  tff(f_78, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 59.11/48.09  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 59.11/48.09  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 59.11/48.09  tff(f_67, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 59.11/48.09  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 59.11/48.09  tff(f_69, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 59.11/48.09  tff(f_63, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 59.11/48.09  tff(f_51, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 59.11/48.09  tff(f_65, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 59.11/48.09  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 59.11/48.09  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 59.11/48.09  tff(f_71, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 59.11/48.09  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 59.11/48.09  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 59.11/48.09  tff(f_74, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 59.11/48.09  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 59.11/48.09  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 59.11/48.09  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 59.11/48.09  tff(c_368, plain, (![A_126, B_127]: (k5_xboole_0(k5_xboole_0(A_126, B_127), k2_xboole_0(A_126, B_127))=k3_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_41])).
% 59.11/48.09  tff(c_417, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_368])).
% 59.11/48.09  tff(c_427, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_417])).
% 59.11/48.09  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.11/48.09  tff(c_12, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 59.11/48.09  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 59.11/48.09  tff(c_214, plain, (![A_120, B_121, C_122]: (k5_xboole_0(k5_xboole_0(A_120, B_121), C_122)=k5_xboole_0(A_120, k5_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 59.11/48.09  tff(c_232, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k5_xboole_0(B_121, k5_xboole_0(A_120, B_121)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_214, c_14])).
% 59.11/48.09  tff(c_255, plain, (![A_13, C_122]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_122))=k5_xboole_0(k1_xboole_0, C_122))), inference(superposition, [status(thm), theory('equality')], [c_14, c_214])).
% 59.11/48.09  tff(c_677, plain, (![A_137, C_138]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_138))=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_255])).
% 59.11/48.09  tff(c_730, plain, (![B_121, A_120]: (k5_xboole_0(B_121, k5_xboole_0(A_120, B_121))=k5_xboole_0(A_120, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_232, c_677])).
% 59.11/48.09  tff(c_770, plain, (![B_139, A_140]: (k5_xboole_0(B_139, k5_xboole_0(A_140, B_139))=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_730])).
% 59.11/48.09  tff(c_676, plain, (![A_13, C_122]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_122))=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_255])).
% 59.11/48.09  tff(c_779, plain, (![B_139, A_140]: (k5_xboole_0(B_139, A_140)=k5_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_770, c_676])).
% 59.11/48.09  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 59.11/48.09  tff(c_414, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), k1_xboole_0)=k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_368])).
% 59.11/48.09  tff(c_717, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_414, c_677])).
% 59.11/48.09  tff(c_1915, plain, (k5_xboole_0('#skF_3', k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_779, c_717])).
% 59.11/48.09  tff(c_763, plain, (![B_121, A_120]: (k5_xboole_0(B_121, k5_xboole_0(A_120, B_121))=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_730])).
% 59.11/48.09  tff(c_773, plain, (![A_140, B_139]: (k5_xboole_0(k5_xboole_0(A_140, B_139), A_140)=B_139)), inference(superposition, [status(thm), theory('equality')], [c_770, c_763])).
% 59.11/48.09  tff(c_1922, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k5_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1915, c_773])).
% 59.11/48.09  tff(c_1937, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_1922])).
% 59.11/48.09  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 59.11/48.09  tff(c_1956, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1937, c_8])).
% 59.11/48.09  tff(c_1960, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1956])).
% 59.11/48.09  tff(c_34, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 59.11/48.09  tff(c_42, plain, (![A_81, F_86, D_84, B_82, E_85, C_83]: (k5_enumset1(A_81, A_81, B_82, C_83, D_84, E_85, F_86)=k4_enumset1(A_81, B_82, C_83, D_84, E_85, F_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 59.11/48.09  tff(c_36, plain, (![A_69, B_70, C_71]: (k2_enumset1(A_69, A_69, B_70, C_71)=k1_enumset1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 59.11/48.09  tff(c_44, plain, (![A_87, C_89, G_93, B_88, E_91, F_92, D_90]: (k6_enumset1(A_87, A_87, B_88, C_89, D_90, E_91, F_92, G_93)=k5_enumset1(A_87, B_88, C_89, D_90, E_91, F_92, G_93))), inference(cnfTransformation, [status(thm)], [f_69])).
% 59.11/48.09  tff(c_38, plain, (![A_72, B_73, C_74, D_75]: (k3_enumset1(A_72, A_72, B_73, C_74, D_75)=k2_enumset1(A_72, B_73, C_74, D_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 59.11/48.09  tff(c_2375, plain, (![B_208, H_211, E_206, C_213, A_210, D_207, F_212, G_209]: (k2_xboole_0(k3_enumset1(A_210, B_208, C_213, D_207, E_206), k1_enumset1(F_212, G_209, H_211))=k6_enumset1(A_210, B_208, C_213, D_207, E_206, F_212, G_209, H_211))), inference(cnfTransformation, [status(thm)], [f_51])).
% 59.11/48.09  tff(c_2390, plain, (![H_211, B_73, C_74, A_72, F_212, D_75, G_209]: (k6_enumset1(A_72, A_72, B_73, C_74, D_75, F_212, G_209, H_211)=k2_xboole_0(k2_enumset1(A_72, B_73, C_74, D_75), k1_enumset1(F_212, G_209, H_211)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2375])).
% 59.11/48.09  tff(c_36204, plain, (![F_513, B_510, D_516, C_514, H_515, A_512, G_511]: (k2_xboole_0(k2_enumset1(A_512, B_510, C_514, D_516), k1_enumset1(F_513, G_511, H_515))=k5_enumset1(A_512, B_510, C_514, D_516, F_513, G_511, H_515))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2390])).
% 59.11/48.09  tff(c_36288, plain, (![F_513, B_70, H_515, C_71, A_69, G_511]: (k5_enumset1(A_69, A_69, B_70, C_71, F_513, G_511, H_515)=k2_xboole_0(k1_enumset1(A_69, B_70, C_71), k1_enumset1(F_513, G_511, H_515)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_36204])).
% 59.11/48.09  tff(c_108234, plain, (![G_800, B_798, F_803, C_801, A_799, H_802]: (k2_xboole_0(k1_enumset1(A_799, B_798, C_801), k1_enumset1(F_803, G_800, H_802))=k4_enumset1(A_799, B_798, C_801, F_803, G_800, H_802))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36288])).
% 59.11/48.09  tff(c_137567, plain, (![A_910, B_911, C_912]: (k4_enumset1(A_910, B_911, C_912, A_910, B_911, C_912)=k1_enumset1(A_910, B_911, C_912))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108234])).
% 59.11/48.09  tff(c_40, plain, (![B_77, A_76, C_78, E_80, D_79]: (k4_enumset1(A_76, A_76, B_77, C_78, D_79, E_80)=k3_enumset1(A_76, B_77, C_78, D_79, E_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 59.11/48.09  tff(c_2094, plain, (![E_188, A_191, F_185, B_189, D_187, G_190, C_186]: (k2_xboole_0(k3_enumset1(A_191, B_189, C_186, D_187, E_188), k2_tarski(F_185, G_190))=k5_enumset1(A_191, B_189, C_186, D_187, E_188, F_185, G_190))), inference(cnfTransformation, [status(thm)], [f_47])).
% 59.11/48.09  tff(c_2106, plain, (![F_185, B_73, C_74, A_72, D_75, G_190]: (k5_enumset1(A_72, A_72, B_73, C_74, D_75, F_185, G_190)=k2_xboole_0(k2_enumset1(A_72, B_73, C_74, D_75), k2_tarski(F_185, G_190)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2094])).
% 59.11/48.09  tff(c_18774, plain, (![A_353, G_355, C_354, F_352, D_356, B_351]: (k2_xboole_0(k2_enumset1(A_353, B_351, C_354, D_356), k2_tarski(F_352, G_355))=k4_enumset1(A_353, B_351, C_354, D_356, F_352, G_355))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2106])).
% 59.11/48.09  tff(c_18834, plain, (![B_70, G_355, F_352, C_71, A_69]: (k4_enumset1(A_69, A_69, B_70, C_71, F_352, G_355)=k2_xboole_0(k1_enumset1(A_69, B_70, C_71), k2_tarski(F_352, G_355)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_18774])).
% 59.11/48.09  tff(c_18840, plain, (![B_70, G_355, F_352, C_71, A_69]: (k2_xboole_0(k1_enumset1(A_69, B_70, C_71), k2_tarski(F_352, G_355))=k3_enumset1(A_69, B_70, C_71, F_352, G_355))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18834])).
% 59.11/48.09  tff(c_541, plain, (![B_131, D_132, A_133, C_134]: (k2_enumset1(B_131, D_132, A_133, C_134)=k2_enumset1(A_133, B_131, C_134, D_132))), inference(cnfTransformation, [status(thm)], [f_43])).
% 59.11/48.09  tff(c_576, plain, (![B_70, A_69, C_71]: (k2_enumset1(B_70, A_69, C_71, A_69)=k1_enumset1(A_69, B_70, C_71))), inference(superposition, [status(thm), theory('equality')], [c_36, c_541])).
% 59.11/48.09  tff(c_18822, plain, (![B_70, G_355, F_352, C_71, A_69]: (k4_enumset1(B_70, A_69, C_71, A_69, F_352, G_355)=k2_xboole_0(k1_enumset1(A_69, B_70, C_71), k2_tarski(F_352, G_355)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_18774])).
% 59.11/48.09  tff(c_90556, plain, (![B_70, G_355, F_352, C_71, A_69]: (k4_enumset1(B_70, A_69, C_71, A_69, F_352, G_355)=k3_enumset1(A_69, B_70, C_71, F_352, G_355))), inference(demodulation, [status(thm), theory('equality')], [c_18840, c_18822])).
% 59.11/48.09  tff(c_137586, plain, (![A_910, C_912]: (k3_enumset1(A_910, A_910, C_912, A_910, C_912)=k1_enumset1(A_910, A_910, C_912))), inference(superposition, [status(thm), theory('equality')], [c_137567, c_90556])).
% 59.11/48.09  tff(c_137675, plain, (![A_913, C_914]: (k3_enumset1(A_913, A_913, C_914, A_913, C_914)=k2_tarski(A_913, C_914))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_137586])).
% 59.11/48.09  tff(c_138374, plain, (![A_919, C_920]: (k2_enumset1(A_919, C_920, A_919, C_920)=k2_tarski(A_919, C_920))), inference(superposition, [status(thm), theory('equality')], [c_137675, c_38])).
% 59.11/48.09  tff(c_138437, plain, (![C_920, A_919]: (k1_enumset1(C_920, A_919, A_919)=k2_tarski(A_919, C_920))), inference(superposition, [status(thm), theory('equality')], [c_138374, c_576])).
% 59.11/48.09  tff(c_2400, plain, (![B_214, A_215, C_216]: (k2_enumset1(B_214, A_215, C_216, A_215)=k1_enumset1(A_215, B_214, C_216))), inference(superposition, [status(thm), theory('equality')], [c_36, c_541])).
% 59.11/48.09  tff(c_557, plain, (![B_131, D_132, C_134]: (k2_enumset1(B_131, D_132, B_131, C_134)=k1_enumset1(B_131, C_134, D_132))), inference(superposition, [status(thm), theory('equality')], [c_541, c_36])).
% 59.11/48.09  tff(c_2407, plain, (![C_216, A_215]: (k1_enumset1(C_216, A_215, A_215)=k1_enumset1(A_215, C_216, C_216))), inference(superposition, [status(thm), theory('equality')], [c_2400, c_557])).
% 59.11/48.09  tff(c_138585, plain, (![C_923, A_924]: (k2_tarski(C_923, A_924)=k2_tarski(A_924, C_923))), inference(demodulation, [status(thm), theory('equality')], [c_138437, c_138437, c_2407])).
% 59.11/48.09  tff(c_46, plain, (![A_94, B_95]: (k3_tarski(k2_tarski(A_94, B_95))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 59.11/48.09  tff(c_138842, plain, (![A_927, C_928]: (k3_tarski(k2_tarski(A_927, C_928))=k2_xboole_0(C_928, A_927))), inference(superposition, [status(thm), theory('equality')], [c_138585, c_46])).
% 59.11/48.09  tff(c_138873, plain, (![C_929, A_930]: (k2_xboole_0(C_929, A_930)=k2_xboole_0(A_930, C_929))), inference(superposition, [status(thm), theory('equality')], [c_138842, c_46])).
% 59.11/48.09  tff(c_139356, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_138873, c_50])).
% 59.11/48.09  tff(c_139626, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1960, c_139356])).
% 59.11/48.09  tff(c_2321, plain, (![B_201, D_202, C_203]: (k2_enumset1(B_201, D_202, B_201, C_203)=k1_enumset1(B_201, C_203, D_202))), inference(superposition, [status(thm), theory('equality')], [c_541, c_36])).
% 59.11/48.09  tff(c_2334, plain, (![D_202, C_203]: (k1_enumset1(D_202, D_202, C_203)=k1_enumset1(D_202, C_203, D_202))), inference(superposition, [status(thm), theory('equality')], [c_2321, c_36])).
% 59.11/48.09  tff(c_2352, plain, (![D_202, C_203]: (k1_enumset1(D_202, C_203, D_202)=k2_tarski(D_202, C_203))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2334])).
% 59.11/48.09  tff(c_32, plain, (![A_66]: (k2_tarski(A_66, A_66)=k1_tarski(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 59.11/48.09  tff(c_2227, plain, (![E_197, G_194, F_199, C_193, D_196, A_198, B_195]: (k2_xboole_0(k2_tarski(A_198, B_195), k3_enumset1(C_193, D_196, E_197, F_199, G_194))=k5_enumset1(A_198, B_195, C_193, D_196, E_197, F_199, G_194))), inference(cnfTransformation, [status(thm)], [f_45])).
% 59.11/48.09  tff(c_2242, plain, (![E_197, G_194, F_199, C_193, D_196, A_66]: (k5_enumset1(A_66, A_66, C_193, D_196, E_197, F_199, G_194)=k2_xboole_0(k1_tarski(A_66), k3_enumset1(C_193, D_196, E_197, F_199, G_194)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2227])).
% 59.11/48.09  tff(c_24690, plain, (![C_381, G_382, D_377, A_378, F_379, E_380]: (k2_xboole_0(k1_tarski(A_378), k3_enumset1(C_381, D_377, E_380, F_379, G_382))=k4_enumset1(A_378, C_381, D_377, E_380, F_379, G_382))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2242])).
% 59.11/48.09  tff(c_48, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), B_97)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 59.11/48.09  tff(c_24743, plain, (![D_387, A_386, F_383, G_384, E_388, C_385]: (k4_enumset1(A_386, C_385, D_387, E_388, F_383, G_384)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24690, c_48])).
% 59.11/48.09  tff(c_24746, plain, (![A_391, D_393, E_390, B_389, C_392]: (k3_enumset1(A_391, B_389, C_392, D_393, E_390)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_24743])).
% 59.11/48.09  tff(c_24749, plain, (![A_394, B_395, C_396, D_397]: (k2_enumset1(A_394, B_395, C_396, D_397)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_24746])).
% 59.11/48.09  tff(c_24767, plain, (![A_398, B_399, C_400]: (k1_enumset1(A_398, B_399, C_400)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_24749])).
% 59.11/48.09  tff(c_24773, plain, (![D_202, C_203]: (k2_tarski(D_202, C_203)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2352, c_24767])).
% 59.11/48.09  tff(c_139654, plain, (![D_202, C_203]: (k2_tarski(D_202, C_203)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139626, c_24773])).
% 59.11/48.09  tff(c_158, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.11/48.09  tff(c_167, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_158])).
% 59.11/48.09  tff(c_171, plain, (![A_115]: (k4_xboole_0(A_115, A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_167])).
% 59.11/48.09  tff(c_176, plain, (![A_115]: (k2_xboole_0(A_115, k1_xboole_0)=k2_xboole_0(A_115, A_115))), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 59.11/48.09  tff(c_180, plain, (![A_115]: (k2_xboole_0(A_115, k1_xboole_0)=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_176])).
% 59.11/48.09  tff(c_432, plain, (![A_128]: (k5_xboole_0(k1_xboole_0, A_128)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_417])).
% 59.11/48.09  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 59.11/48.09  tff(c_1248, plain, (![A_151]: (k5_xboole_0(A_151, k2_xboole_0(k1_xboole_0, A_151))=k3_xboole_0(k1_xboole_0, A_151))), inference(superposition, [status(thm), theory('equality')], [c_432, c_16])).
% 59.11/48.09  tff(c_1447, plain, (![A_160]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_160), k3_xboole_0(k1_xboole_0, A_160))=A_160)), inference(superposition, [status(thm), theory('equality')], [c_1248, c_763])).
% 59.11/48.09  tff(c_1462, plain, (![A_160]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_160), A_160)=k3_xboole_0(k1_xboole_0, A_160))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_676])).
% 59.11/48.09  tff(c_139305, plain, (![C_929]: (k5_xboole_0(k2_xboole_0(C_929, k1_xboole_0), C_929)=k3_xboole_0(k1_xboole_0, C_929))), inference(superposition, [status(thm), theory('equality')], [c_138873, c_1462])).
% 59.11/48.09  tff(c_139618, plain, (![C_929]: (k3_xboole_0(k1_xboole_0, C_929)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_180, c_139305])).
% 59.11/48.09  tff(c_143047, plain, (![C_929]: (k3_xboole_0('#skF_3', C_929)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139626, c_139626, c_139618])).
% 59.11/48.09  tff(c_1966, plain, (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')=k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1960, c_16])).
% 59.11/48.09  tff(c_1969, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_1966])).
% 59.11/48.09  tff(c_143048, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143047, c_1969])).
% 59.11/48.09  tff(c_144937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139654, c_143048])).
% 59.11/48.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.11/48.09  
% 59.11/48.09  Inference rules
% 59.11/48.09  ----------------------
% 59.11/48.09  #Ref     : 0
% 59.11/48.09  #Sup     : 37475
% 59.11/48.09  #Fact    : 0
% 59.11/48.09  #Define  : 0
% 59.11/48.09  #Split   : 0
% 59.11/48.09  #Chain   : 0
% 59.11/48.09  #Close   : 0
% 59.11/48.09  
% 59.11/48.09  Ordering : KBO
% 59.11/48.09  
% 59.11/48.09  Simplification rules
% 59.11/48.09  ----------------------
% 59.11/48.09  #Subsume      : 2579
% 59.11/48.09  #Demod        : 76817
% 59.11/48.09  #Tautology    : 13784
% 59.11/48.09  #SimpNegUnit  : 1
% 59.11/48.09  #BackRed      : 113
% 59.11/48.09  
% 59.11/48.09  #Partial instantiations: 0
% 59.11/48.09  #Strategies tried      : 1
% 59.11/48.09  
% 59.11/48.09  Timing (in seconds)
% 59.11/48.09  ----------------------
% 59.11/48.10  Preprocessing        : 0.33
% 59.11/48.10  Parsing              : 0.17
% 59.11/48.10  CNF conversion       : 0.02
% 59.11/48.10  Main loop            : 46.97
% 59.11/48.10  Inferencing          : 3.44
% 59.11/48.10  Reduction            : 36.50
% 59.11/48.10  Demodulation         : 35.20
% 59.11/48.10  BG Simplification    : 0.65
% 59.11/48.10  Subsumption          : 4.91
% 59.11/48.10  Abstraction          : 1.24
% 59.11/48.10  MUC search           : 0.00
% 59.11/48.10  Cooper               : 0.00
% 59.11/48.10  Total                : 47.36
% 59.11/48.10  Index Insertion      : 0.00
% 59.11/48.10  Index Deletion       : 0.00
% 59.11/48.10  Index Matching       : 0.00
% 59.11/48.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 11.89s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 255 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 238 expanded)
%              Number of equality atoms :   65 ( 237 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_30,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_529,plain,(
    ! [A_98,D_99,C_100,B_101] : k2_enumset1(A_98,D_99,C_100,B_101) = k2_enumset1(A_98,B_101,C_100,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_669,plain,(
    ! [A_102,C_103,B_104] : k2_enumset1(A_102,C_103,B_104,A_102) = k1_enumset1(A_102,B_104,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_529])).

tff(c_182,plain,(
    ! [A_77,C_78,D_79,B_80] : k2_enumset1(A_77,C_78,D_79,B_80) = k2_enumset1(A_77,B_80,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [B_80,C_78,D_79] : k2_enumset1(B_80,C_78,D_79,B_80) = k1_enumset1(B_80,C_78,D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_30])).

tff(c_695,plain,(
    ! [A_102,C_103,B_104] : k1_enumset1(A_102,C_103,B_104) = k1_enumset1(A_102,B_104,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_198])).

tff(c_12,plain,(
    ! [A_12,C_14,D_15,B_13] : k2_enumset1(A_12,C_14,D_15,B_13) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_enumset1(A_52,A_52,B_53,C_54,D_55) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [D_59,A_56,B_57,C_58,E_60] : k4_enumset1(A_56,A_56,B_57,C_58,D_59,E_60) = k3_enumset1(A_56,B_57,C_58,D_59,E_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1814,plain,(
    ! [E_143,B_144,D_148,F_145,A_147,C_146] : k2_xboole_0(k2_enumset1(A_147,B_144,C_146,D_148),k2_tarski(E_143,F_145)) = k4_enumset1(A_147,B_144,C_146,D_148,E_143,F_145) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1874,plain,(
    ! [E_143,C_51,F_145,B_50,A_49] : k4_enumset1(A_49,A_49,B_50,C_51,E_143,F_145) = k2_xboole_0(k1_enumset1(A_49,B_50,C_51),k2_tarski(E_143,F_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1814])).

tff(c_8881,plain,(
    ! [E_239,B_238,C_237,A_240,F_241] : k2_xboole_0(k1_enumset1(A_240,B_238,C_237),k2_tarski(E_239,F_241)) = k3_enumset1(A_240,B_238,C_237,E_239,F_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1874])).

tff(c_8905,plain,(
    ! [A_47,B_48,E_239,F_241] : k3_enumset1(A_47,A_47,B_48,E_239,F_241) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(E_239,F_241)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8881])).

tff(c_8911,plain,(
    ! [A_47,B_48,E_239,F_241] : k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(E_239,F_241)) = k2_enumset1(A_47,B_48,E_239,F_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8905])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_764,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2735,plain,(
    ! [A_170,B_171,C_172] : k5_xboole_0(k5_xboole_0(A_170,B_171),C_172) = k5_xboole_0(B_171,k5_xboole_0(A_170,C_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_764])).

tff(c_17528,plain,(
    ! [A_389,B_390,C_391] : k5_xboole_0(k3_xboole_0(A_389,B_390),k5_xboole_0(B_390,C_391)) = k5_xboole_0(k4_xboole_0(B_390,A_389),C_391) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_2735])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1905,plain,(
    ! [A_158,B_159,A_157] : k5_xboole_0(A_158,k5_xboole_0(B_159,A_157)) = k5_xboole_0(A_157,k5_xboole_0(A_158,B_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_764])).

tff(c_2008,plain,(
    ! [A_5,B_6,A_158] : k5_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_158,A_5)) = k5_xboole_0(A_158,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1905])).

tff(c_17547,plain,(
    ! [B_390,C_391] : k5_xboole_0(k4_xboole_0(B_390,C_391),C_391) = k5_xboole_0(B_390,k4_xboole_0(C_391,B_390)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17528,c_2008])).

tff(c_17849,plain,(
    ! [B_392,C_393] : k5_xboole_0(k4_xboole_0(B_392,C_393),C_393) = k2_xboole_0(B_392,C_393) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17547])).

tff(c_18017,plain,(
    ! [C_394,B_395] : k5_xboole_0(C_394,k4_xboole_0(B_395,C_394)) = k2_xboole_0(B_395,C_394) ),
    inference(superposition,[status(thm),theory(equality)],[c_17849,c_4])).

tff(c_18113,plain,(
    ! [C_394,B_395] : k2_xboole_0(C_394,B_395) = k2_xboole_0(B_395,C_394) ),
    inference(superposition,[status(thm),theory(equality)],[c_18017,c_10])).

tff(c_327,plain,(
    ! [D_89,C_90,B_91,A_92] : k2_enumset1(D_89,C_90,B_91,A_92) = k2_enumset1(A_92,B_91,C_90,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_371,plain,(
    ! [D_89,C_90,B_91] : k2_enumset1(D_89,C_90,B_91,B_91) = k1_enumset1(B_91,C_90,D_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_30])).

tff(c_20,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9679,plain,(
    ! [A_252,B_251,D_249,A_248,C_250] : k4_enumset1(A_248,B_251,C_250,D_249,A_252,A_252) = k2_xboole_0(k2_enumset1(A_248,B_251,C_250,D_249),k1_tarski(A_252)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1814])).

tff(c_9783,plain,(
    ! [A_56,B_57,C_58,E_60] : k3_enumset1(A_56,B_57,C_58,E_60,E_60) = k2_xboole_0(k2_enumset1(A_56,A_56,B_57,C_58),k1_tarski(E_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9679])).

tff(c_11748,plain,(
    ! [A_309,B_310,C_311,E_312] : k3_enumset1(A_309,B_310,C_311,E_312,E_312) = k2_enumset1(A_309,B_310,C_311,E_312) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_9783])).

tff(c_11758,plain,(
    ! [B_310,C_311,E_312] : k2_enumset1(B_310,C_311,E_312,E_312) = k2_enumset1(B_310,B_310,C_311,E_312) ),
    inference(superposition,[status(thm),theory(equality)],[c_11748,c_32])).

tff(c_11771,plain,(
    ! [E_313,C_314,B_315] : k1_enumset1(E_313,C_314,B_315) = k1_enumset1(B_315,C_314,E_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_30,c_11758])).

tff(c_427,plain,(
    ! [D_93,C_94,B_95] : k2_enumset1(D_93,C_94,B_95,B_95) = k1_enumset1(B_95,C_94,D_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_30])).

tff(c_454,plain,(
    ! [C_94,B_95] : k1_enumset1(C_94,B_95,B_95) = k1_enumset1(B_95,C_94,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_30])).

tff(c_11811,plain,(
    ! [E_313,B_315] : k1_enumset1(E_313,E_313,B_315) = k1_enumset1(E_313,B_315,B_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_11771,c_454])).

tff(c_11878,plain,(
    ! [E_313,B_315] : k1_enumset1(E_313,B_315,B_315) = k2_tarski(E_313,B_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11811])).

tff(c_11890,plain,(
    ! [C_94,B_95] : k2_tarski(C_94,B_95) = k2_tarski(B_95,C_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11878,c_11878,c_454])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_834,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_36])).

tff(c_11941,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11890,c_11890,c_834])).

tff(c_18144,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18113,c_11941])).

tff(c_20194,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8911,c_18144])).

tff(c_20197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_30,c_12,c_20194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.89/4.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/4.86  
% 11.95/4.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/4.86  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.95/4.86  
% 11.95/4.86  %Foreground sorts:
% 11.95/4.86  
% 11.95/4.86  
% 11.95/4.86  %Background operators:
% 11.95/4.86  
% 11.95/4.86  
% 11.95/4.86  %Foreground operators:
% 11.95/4.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/4.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.95/4.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.95/4.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.95/4.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.95/4.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.95/4.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/4.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.95/4.86  tff('#skF_2', type, '#skF_2': $i).
% 11.95/4.86  tff('#skF_3', type, '#skF_3': $i).
% 11.95/4.86  tff('#skF_1', type, '#skF_1': $i).
% 11.95/4.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.95/4.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.95/4.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/4.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/4.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.95/4.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.95/4.87  
% 11.95/4.88  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 11.95/4.88  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 11.95/4.88  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 11.95/4.88  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 11.95/4.88  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.95/4.88  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 11.95/4.88  tff(f_47, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 11.95/4.88  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.95/4.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.95/4.88  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.95/4.88  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.95/4.88  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.95/4.88  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 11.95/4.88  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 11.95/4.88  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.95/4.88  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 11.95/4.88  tff(c_30, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.95/4.88  tff(c_529, plain, (![A_98, D_99, C_100, B_101]: (k2_enumset1(A_98, D_99, C_100, B_101)=k2_enumset1(A_98, B_101, C_100, D_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.95/4.88  tff(c_669, plain, (![A_102, C_103, B_104]: (k2_enumset1(A_102, C_103, B_104, A_102)=k1_enumset1(A_102, B_104, C_103))), inference(superposition, [status(thm), theory('equality')], [c_30, c_529])).
% 11.95/4.88  tff(c_182, plain, (![A_77, C_78, D_79, B_80]: (k2_enumset1(A_77, C_78, D_79, B_80)=k2_enumset1(A_77, B_80, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/4.88  tff(c_198, plain, (![B_80, C_78, D_79]: (k2_enumset1(B_80, C_78, D_79, B_80)=k1_enumset1(B_80, C_78, D_79))), inference(superposition, [status(thm), theory('equality')], [c_182, c_30])).
% 11.95/4.88  tff(c_695, plain, (![A_102, C_103, B_104]: (k1_enumset1(A_102, C_103, B_104)=k1_enumset1(A_102, B_104, C_103))), inference(superposition, [status(thm), theory('equality')], [c_669, c_198])).
% 11.95/4.88  tff(c_12, plain, (![A_12, C_14, D_15, B_13]: (k2_enumset1(A_12, C_14, D_15, B_13)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/4.88  tff(c_32, plain, (![A_52, B_53, C_54, D_55]: (k3_enumset1(A_52, A_52, B_53, C_54, D_55)=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.95/4.88  tff(c_28, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.95/4.88  tff(c_34, plain, (![D_59, A_56, B_57, C_58, E_60]: (k4_enumset1(A_56, A_56, B_57, C_58, D_59, E_60)=k3_enumset1(A_56, B_57, C_58, D_59, E_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.95/4.88  tff(c_1814, plain, (![E_143, B_144, D_148, F_145, A_147, C_146]: (k2_xboole_0(k2_enumset1(A_147, B_144, C_146, D_148), k2_tarski(E_143, F_145))=k4_enumset1(A_147, B_144, C_146, D_148, E_143, F_145))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.95/4.88  tff(c_1874, plain, (![E_143, C_51, F_145, B_50, A_49]: (k4_enumset1(A_49, A_49, B_50, C_51, E_143, F_145)=k2_xboole_0(k1_enumset1(A_49, B_50, C_51), k2_tarski(E_143, F_145)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1814])).
% 11.95/4.88  tff(c_8881, plain, (![E_239, B_238, C_237, A_240, F_241]: (k2_xboole_0(k1_enumset1(A_240, B_238, C_237), k2_tarski(E_239, F_241))=k3_enumset1(A_240, B_238, C_237, E_239, F_241))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1874])).
% 11.95/4.88  tff(c_8905, plain, (![A_47, B_48, E_239, F_241]: (k3_enumset1(A_47, A_47, B_48, E_239, F_241)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(E_239, F_241)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8881])).
% 11.95/4.88  tff(c_8911, plain, (![A_47, B_48, E_239, F_241]: (k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(E_239, F_241))=k2_enumset1(A_47, B_48, E_239, F_241))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8905])).
% 11.95/4.88  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.95/4.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.95/4.88  tff(c_121, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.95/4.88  tff(c_133, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 11.95/4.88  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.95/4.88  tff(c_764, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.95/4.88  tff(c_2735, plain, (![A_170, B_171, C_172]: (k5_xboole_0(k5_xboole_0(A_170, B_171), C_172)=k5_xboole_0(B_171, k5_xboole_0(A_170, C_172)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_764])).
% 11.95/4.88  tff(c_17528, plain, (![A_389, B_390, C_391]: (k5_xboole_0(k3_xboole_0(A_389, B_390), k5_xboole_0(B_390, C_391))=k5_xboole_0(k4_xboole_0(B_390, A_389), C_391))), inference(superposition, [status(thm), theory('equality')], [c_133, c_2735])).
% 11.95/4.88  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.95/4.88  tff(c_1905, plain, (![A_158, B_159, A_157]: (k5_xboole_0(A_158, k5_xboole_0(B_159, A_157))=k5_xboole_0(A_157, k5_xboole_0(A_158, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_764])).
% 11.95/4.88  tff(c_2008, plain, (![A_5, B_6, A_158]: (k5_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_158, A_5))=k5_xboole_0(A_158, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1905])).
% 11.95/4.88  tff(c_17547, plain, (![B_390, C_391]: (k5_xboole_0(k4_xboole_0(B_390, C_391), C_391)=k5_xboole_0(B_390, k4_xboole_0(C_391, B_390)))), inference(superposition, [status(thm), theory('equality')], [c_17528, c_2008])).
% 11.95/4.88  tff(c_17849, plain, (![B_392, C_393]: (k5_xboole_0(k4_xboole_0(B_392, C_393), C_393)=k2_xboole_0(B_392, C_393))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_17547])).
% 11.95/4.88  tff(c_18017, plain, (![C_394, B_395]: (k5_xboole_0(C_394, k4_xboole_0(B_395, C_394))=k2_xboole_0(B_395, C_394))), inference(superposition, [status(thm), theory('equality')], [c_17849, c_4])).
% 11.95/4.88  tff(c_18113, plain, (![C_394, B_395]: (k2_xboole_0(C_394, B_395)=k2_xboole_0(B_395, C_394))), inference(superposition, [status(thm), theory('equality')], [c_18017, c_10])).
% 11.95/4.88  tff(c_327, plain, (![D_89, C_90, B_91, A_92]: (k2_enumset1(D_89, C_90, B_91, A_92)=k2_enumset1(A_92, B_91, C_90, D_89))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.95/4.88  tff(c_371, plain, (![D_89, C_90, B_91]: (k2_enumset1(D_89, C_90, B_91, B_91)=k1_enumset1(B_91, C_90, D_89))), inference(superposition, [status(thm), theory('equality')], [c_327, c_30])).
% 11.95/4.88  tff(c_20, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.95/4.88  tff(c_26, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.95/4.88  tff(c_9679, plain, (![A_252, B_251, D_249, A_248, C_250]: (k4_enumset1(A_248, B_251, C_250, D_249, A_252, A_252)=k2_xboole_0(k2_enumset1(A_248, B_251, C_250, D_249), k1_tarski(A_252)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1814])).
% 11.95/4.88  tff(c_9783, plain, (![A_56, B_57, C_58, E_60]: (k3_enumset1(A_56, B_57, C_58, E_60, E_60)=k2_xboole_0(k2_enumset1(A_56, A_56, B_57, C_58), k1_tarski(E_60)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9679])).
% 11.95/4.88  tff(c_11748, plain, (![A_309, B_310, C_311, E_312]: (k3_enumset1(A_309, B_310, C_311, E_312, E_312)=k2_enumset1(A_309, B_310, C_311, E_312))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_9783])).
% 11.95/4.88  tff(c_11758, plain, (![B_310, C_311, E_312]: (k2_enumset1(B_310, C_311, E_312, E_312)=k2_enumset1(B_310, B_310, C_311, E_312))), inference(superposition, [status(thm), theory('equality')], [c_11748, c_32])).
% 11.95/4.88  tff(c_11771, plain, (![E_313, C_314, B_315]: (k1_enumset1(E_313, C_314, B_315)=k1_enumset1(B_315, C_314, E_313))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_30, c_11758])).
% 11.95/4.88  tff(c_427, plain, (![D_93, C_94, B_95]: (k2_enumset1(D_93, C_94, B_95, B_95)=k1_enumset1(B_95, C_94, D_93))), inference(superposition, [status(thm), theory('equality')], [c_327, c_30])).
% 11.95/4.88  tff(c_454, plain, (![C_94, B_95]: (k1_enumset1(C_94, B_95, B_95)=k1_enumset1(B_95, C_94, C_94))), inference(superposition, [status(thm), theory('equality')], [c_427, c_30])).
% 11.95/4.88  tff(c_11811, plain, (![E_313, B_315]: (k1_enumset1(E_313, E_313, B_315)=k1_enumset1(E_313, B_315, B_315))), inference(superposition, [status(thm), theory('equality')], [c_11771, c_454])).
% 11.95/4.88  tff(c_11878, plain, (![E_313, B_315]: (k1_enumset1(E_313, B_315, B_315)=k2_tarski(E_313, B_315))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_11811])).
% 11.95/4.88  tff(c_11890, plain, (![C_94, B_95]: (k2_tarski(C_94, B_95)=k2_tarski(B_95, C_94))), inference(demodulation, [status(thm), theory('equality')], [c_11878, c_11878, c_454])).
% 11.95/4.88  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.95/4.88  tff(c_834, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_36])).
% 11.95/4.88  tff(c_11941, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11890, c_11890, c_834])).
% 11.95/4.88  tff(c_18144, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18113, c_11941])).
% 11.95/4.88  tff(c_20194, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8911, c_18144])).
% 11.95/4.88  tff(c_20197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_30, c_12, c_20194])).
% 11.95/4.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/4.88  
% 11.95/4.88  Inference rules
% 11.95/4.88  ----------------------
% 11.95/4.88  #Ref     : 0
% 11.95/4.88  #Sup     : 5252
% 11.95/4.88  #Fact    : 0
% 11.95/4.88  #Define  : 0
% 11.95/4.88  #Split   : 0
% 11.95/4.88  #Chain   : 0
% 11.95/4.88  #Close   : 0
% 11.95/4.88  
% 11.95/4.88  Ordering : KBO
% 11.95/4.88  
% 11.95/4.88  Simplification rules
% 11.95/4.88  ----------------------
% 11.95/4.88  #Subsume      : 1189
% 11.95/4.88  #Demod        : 3034
% 11.95/4.88  #Tautology    : 2048
% 11.95/4.88  #SimpNegUnit  : 0
% 11.95/4.88  #BackRed      : 5
% 11.95/4.88  
% 11.95/4.88  #Partial instantiations: 0
% 11.95/4.88  #Strategies tried      : 1
% 11.95/4.88  
% 11.95/4.88  Timing (in seconds)
% 11.95/4.88  ----------------------
% 11.95/4.89  Preprocessing        : 0.32
% 11.95/4.89  Parsing              : 0.17
% 11.95/4.89  CNF conversion       : 0.02
% 11.95/4.89  Main loop            : 3.74
% 11.95/4.89  Inferencing          : 0.76
% 11.95/4.89  Reduction            : 2.33
% 11.95/4.89  Demodulation         : 2.18
% 11.95/4.89  BG Simplification    : 0.11
% 11.95/4.89  Subsumption          : 0.38
% 11.95/4.89  Abstraction          : 0.16
% 11.95/4.89  MUC search           : 0.00
% 11.95/4.89  Cooper               : 0.00
% 11.95/4.89  Total                : 4.10
% 11.95/4.89  Index Insertion      : 0.00
% 11.95/4.89  Index Deletion       : 0.00
% 11.95/4.89  Index Matching       : 0.00
% 11.95/4.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------

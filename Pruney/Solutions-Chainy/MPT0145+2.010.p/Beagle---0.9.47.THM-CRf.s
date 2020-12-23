%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:54 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 138 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 ( 118 expanded)
%              Number of equality atoms :   41 ( 117 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k1_tarski(E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_52,B_53,C_54,D_55] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_52,B_53),C_54),D_55) = k2_xboole_0(A_52,k2_xboole_0(k2_xboole_0(B_53,C_54),D_55)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_96,D_95,C_94,C_97,B_93] : k2_xboole_0(k2_tarski(A_96,B_93),k2_xboole_0(k2_xboole_0(k1_tarski(C_94),C_97),D_95)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_96,B_93,C_94),C_97),D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_233,plain,(
    ! [A_96,A_7,D_95,B_93,B_8] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_96,B_93,A_7),k1_tarski(B_8)),D_95) = k2_xboole_0(k2_tarski(A_96,B_93),k2_xboole_0(k2_tarski(A_7,B_8),D_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_206])).

tff(c_239,plain,(
    ! [B_98,A_99,B_102,A_100,D_101] : k2_xboole_0(k2_tarski(A_99,B_102),k2_xboole_0(k2_tarski(A_100,B_98),D_101)) = k2_xboole_0(k2_enumset1(A_99,B_102,A_100,B_98),D_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_233])).

tff(c_263,plain,(
    ! [C_11,A_99,B_10,B_102,A_9] : k2_xboole_0(k2_enumset1(A_99,B_102,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k2_tarski(A_99,B_102),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_239])).

tff(c_331,plain,(
    ! [B_107,C_108,A_109,A_105,B_106] : k2_xboole_0(k2_tarski(A_105,B_106),k1_enumset1(A_109,B_107,C_108)) = k3_enumset1(A_105,B_106,A_109,B_107,C_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_263])).

tff(c_119,plain,(
    ! [A_67,B_68,C_69,D_70] : k2_xboole_0(k1_tarski(A_67),k2_xboole_0(k2_xboole_0(k1_tarski(B_68),C_69),D_70)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_67,B_68),C_69),D_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_63])).

tff(c_137,plain,(
    ! [A_67,A_7,B_8,D_70] : k2_xboole_0(k2_xboole_0(k2_tarski(A_67,A_7),k1_tarski(B_8)),D_70) = k2_xboole_0(k1_tarski(A_67),k2_xboole_0(k2_tarski(A_7,B_8),D_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_119])).

tff(c_143,plain,(
    ! [A_67,A_7,B_8,D_70] : k2_xboole_0(k1_tarski(A_67),k2_xboole_0(k2_tarski(A_7,B_8),D_70)) = k2_xboole_0(k1_enumset1(A_67,A_7,B_8),D_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_343,plain,(
    ! [B_107,C_108,A_109,A_105,A_67,B_106] : k2_xboole_0(k1_enumset1(A_67,A_105,B_106),k1_enumset1(A_109,B_107,C_108)) = k2_xboole_0(k1_tarski(A_67),k3_enumset1(A_105,B_106,A_109,B_107,C_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_143])).

tff(c_14,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k1_tarski(F_26)) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_528,plain,(
    ! [D_130,C_133,D_132,A_129,C_131,B_128] : k2_xboole_0(k1_enumset1(A_129,B_128,C_131),k2_xboole_0(k2_xboole_0(k1_tarski(D_130),C_133),D_132)) = k2_xboole_0(k2_xboole_0(k2_enumset1(A_129,B_128,C_131,D_130),C_133),D_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_565,plain,(
    ! [A_7,D_132,A_129,B_8,C_131,B_128] : k2_xboole_0(k2_xboole_0(k2_enumset1(A_129,B_128,C_131,A_7),k1_tarski(B_8)),D_132) = k2_xboole_0(k1_enumset1(A_129,B_128,C_131),k2_xboole_0(k2_tarski(A_7,B_8),D_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_528])).

tff(c_575,plain,(
    ! [A_137,B_135,A_136,C_138,D_139,B_134] : k2_xboole_0(k1_enumset1(A_137,B_135,C_138),k2_xboole_0(k2_tarski(A_136,B_134),D_139)) = k2_xboole_0(k3_enumset1(A_137,B_135,C_138,A_136,B_134),D_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_565])).

tff(c_605,plain,(
    ! [C_11,B_10,A_137,B_135,C_138,A_9] : k2_xboole_0(k3_enumset1(A_137,B_135,C_138,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k1_enumset1(A_137,B_135,C_138),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_575])).

tff(c_610,plain,(
    ! [C_11,B_10,A_137,B_135,C_138,A_9] : k2_xboole_0(k1_tarski(A_137),k3_enumset1(B_135,C_138,A_9,B_10,C_11)) = k4_enumset1(A_137,B_135,C_138,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_14,c_605])).

tff(c_611,plain,(
    ! [B_107,C_108,A_109,A_105,A_67,B_106] : k2_xboole_0(k1_enumset1(A_67,A_105,B_106),k1_enumset1(A_109,B_107,C_108)) = k4_enumset1(A_67,A_105,B_106,A_109,B_107,C_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_343])).

tff(c_18,plain,(
    ! [D_37,A_34,F_39,B_35,G_40,C_36,E_38] : k2_xboole_0(k2_enumset1(A_34,B_35,C_36,D_37),k1_enumset1(E_38,F_39,G_40)) = k5_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_238,plain,(
    ! [A_96,A_7,D_95,B_93,B_8] : k2_xboole_0(k2_tarski(A_96,B_93),k2_xboole_0(k2_tarski(A_7,B_8),D_95)) = k2_xboole_0(k2_enumset1(A_96,B_93,A_7,B_8),D_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_233])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_1,B_2),C_3),D_4) = k2_xboole_0(A_1,k2_xboole_0(k2_xboole_0(B_2,C_3),D_4)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_354,plain,(
    ! [B_111,C_114,A_110,D_112,D_113] : k2_xboole_0(k2_xboole_0(A_110,k2_xboole_0(k2_xboole_0(B_111,C_114),D_113)),D_112) = k2_xboole_0(k2_xboole_0(A_110,B_111),k2_xboole_0(k2_xboole_0(C_114,D_113),D_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2])).

tff(c_659,plain,(
    ! [A_152,D_155,A_154,D_156,B_153] : k2_xboole_0(k2_xboole_0(A_152,k1_tarski(A_154)),k2_xboole_0(k2_xboole_0(k1_tarski(B_153),D_156),D_155)) = k2_xboole_0(k2_xboole_0(A_152,k2_xboole_0(k2_tarski(A_154,B_153),D_156)),D_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_354])).

tff(c_756,plain,(
    ! [A_152,D_155,A_7,A_154,B_8] : k2_xboole_0(k2_xboole_0(A_152,k2_xboole_0(k2_tarski(A_154,A_7),k1_tarski(B_8))),D_155) = k2_xboole_0(k2_xboole_0(A_152,k1_tarski(A_154)),k2_xboole_0(k2_tarski(A_7,B_8),D_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_659])).

tff(c_782,plain,(
    ! [A_159,D_160,A_161,A_157,B_158] : k2_xboole_0(k2_xboole_0(A_157,k1_tarski(A_161)),k2_xboole_0(k2_tarski(A_159,B_158),D_160)) = k2_xboole_0(k2_xboole_0(A_157,k1_enumset1(A_161,A_159,B_158)),D_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_756])).

tff(c_884,plain,(
    ! [A_163,C_165,A_166,B_164,A_162] : k2_xboole_0(k2_xboole_0(A_162,k1_enumset1(A_163,A_166,B_164)),k1_tarski(C_165)) = k2_xboole_0(k2_xboole_0(A_162,k1_tarski(A_163)),k1_enumset1(A_166,B_164,C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_782])).

tff(c_87,plain,(
    ! [D_55,C_11,B_10,C_54,A_9] : k2_xboole_0(k2_tarski(A_9,B_10),k2_xboole_0(k2_xboole_0(k1_tarski(C_11),C_54),D_55)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_9,B_10,C_11),C_54),D_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_914,plain,(
    ! [A_163,C_165,C_11,B_10,A_166,B_164,A_9] : k2_xboole_0(k2_tarski(A_9,B_10),k2_xboole_0(k2_xboole_0(k1_tarski(C_11),k1_tarski(A_163)),k1_enumset1(A_166,B_164,C_165))) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(A_163,A_166,B_164)),k1_tarski(C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_87])).

tff(c_963,plain,(
    ! [A_163,C_165,C_11,B_10,A_166,B_164,A_9] : k2_xboole_0(k4_enumset1(A_9,B_10,C_11,A_163,A_166,B_164),k1_tarski(C_165)) = k5_enumset1(A_9,B_10,C_11,A_163,A_166,B_164,C_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_18,c_238,c_6,c_914])).

tff(c_20,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.66  
% 3.57/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.66  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.57/1.66  
% 3.57/1.66  %Foreground sorts:
% 3.57/1.66  
% 3.57/1.66  
% 3.57/1.66  %Background operators:
% 3.57/1.66  
% 3.57/1.66  
% 3.57/1.66  %Foreground operators:
% 3.57/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.57/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.57/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.57/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.57/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.57/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.57/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.66  
% 3.57/1.67  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.57/1.67  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.57/1.67  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.57/1.67  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.57/1.67  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 3.57/1.67  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.57/1.67  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 3.57/1.67  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 3.57/1.67  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k1_tarski(E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.67  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.57/1.67  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.67  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.67  tff(c_63, plain, (![A_52, B_53, C_54, D_55]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_52, B_53), C_54), D_55)=k2_xboole_0(A_52, k2_xboole_0(k2_xboole_0(B_53, C_54), D_55)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.67  tff(c_206, plain, (![A_96, D_95, C_94, C_97, B_93]: (k2_xboole_0(k2_tarski(A_96, B_93), k2_xboole_0(k2_xboole_0(k1_tarski(C_94), C_97), D_95))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_96, B_93, C_94), C_97), D_95))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 3.57/1.67  tff(c_233, plain, (![A_96, A_7, D_95, B_93, B_8]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_96, B_93, A_7), k1_tarski(B_8)), D_95)=k2_xboole_0(k2_tarski(A_96, B_93), k2_xboole_0(k2_tarski(A_7, B_8), D_95)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_206])).
% 3.57/1.67  tff(c_239, plain, (![B_98, A_99, B_102, A_100, D_101]: (k2_xboole_0(k2_tarski(A_99, B_102), k2_xboole_0(k2_tarski(A_100, B_98), D_101))=k2_xboole_0(k2_enumset1(A_99, B_102, A_100, B_98), D_101))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_233])).
% 3.57/1.67  tff(c_263, plain, (![C_11, A_99, B_10, B_102, A_9]: (k2_xboole_0(k2_enumset1(A_99, B_102, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k2_tarski(A_99, B_102), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_239])).
% 3.57/1.67  tff(c_331, plain, (![B_107, C_108, A_109, A_105, B_106]: (k2_xboole_0(k2_tarski(A_105, B_106), k1_enumset1(A_109, B_107, C_108))=k3_enumset1(A_105, B_106, A_109, B_107, C_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_263])).
% 3.57/1.67  tff(c_119, plain, (![A_67, B_68, C_69, D_70]: (k2_xboole_0(k1_tarski(A_67), k2_xboole_0(k2_xboole_0(k1_tarski(B_68), C_69), D_70))=k2_xboole_0(k2_xboole_0(k2_tarski(A_67, B_68), C_69), D_70))), inference(superposition, [status(thm), theory('equality')], [c_6, c_63])).
% 3.57/1.67  tff(c_137, plain, (![A_67, A_7, B_8, D_70]: (k2_xboole_0(k2_xboole_0(k2_tarski(A_67, A_7), k1_tarski(B_8)), D_70)=k2_xboole_0(k1_tarski(A_67), k2_xboole_0(k2_tarski(A_7, B_8), D_70)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_119])).
% 3.57/1.67  tff(c_143, plain, (![A_67, A_7, B_8, D_70]: (k2_xboole_0(k1_tarski(A_67), k2_xboole_0(k2_tarski(A_7, B_8), D_70))=k2_xboole_0(k1_enumset1(A_67, A_7, B_8), D_70))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 3.57/1.67  tff(c_343, plain, (![B_107, C_108, A_109, A_105, A_67, B_106]: (k2_xboole_0(k1_enumset1(A_67, A_105, B_106), k1_enumset1(A_109, B_107, C_108))=k2_xboole_0(k1_tarski(A_67), k3_enumset1(A_105, B_106, A_109, B_107, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_331, c_143])).
% 3.57/1.67  tff(c_14, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k1_tarski(F_26))=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.67  tff(c_528, plain, (![D_130, C_133, D_132, A_129, C_131, B_128]: (k2_xboole_0(k1_enumset1(A_129, B_128, C_131), k2_xboole_0(k2_xboole_0(k1_tarski(D_130), C_133), D_132))=k2_xboole_0(k2_xboole_0(k2_enumset1(A_129, B_128, C_131, D_130), C_133), D_132))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 3.57/1.67  tff(c_565, plain, (![A_7, D_132, A_129, B_8, C_131, B_128]: (k2_xboole_0(k2_xboole_0(k2_enumset1(A_129, B_128, C_131, A_7), k1_tarski(B_8)), D_132)=k2_xboole_0(k1_enumset1(A_129, B_128, C_131), k2_xboole_0(k2_tarski(A_7, B_8), D_132)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_528])).
% 3.57/1.67  tff(c_575, plain, (![A_137, B_135, A_136, C_138, D_139, B_134]: (k2_xboole_0(k1_enumset1(A_137, B_135, C_138), k2_xboole_0(k2_tarski(A_136, B_134), D_139))=k2_xboole_0(k3_enumset1(A_137, B_135, C_138, A_136, B_134), D_139))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_565])).
% 3.57/1.67  tff(c_605, plain, (![C_11, B_10, A_137, B_135, C_138, A_9]: (k2_xboole_0(k3_enumset1(A_137, B_135, C_138, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k1_enumset1(A_137, B_135, C_138), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_575])).
% 3.57/1.67  tff(c_610, plain, (![C_11, B_10, A_137, B_135, C_138, A_9]: (k2_xboole_0(k1_tarski(A_137), k3_enumset1(B_135, C_138, A_9, B_10, C_11))=k4_enumset1(A_137, B_135, C_138, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_14, c_605])).
% 3.57/1.67  tff(c_611, plain, (![B_107, C_108, A_109, A_105, A_67, B_106]: (k2_xboole_0(k1_enumset1(A_67, A_105, B_106), k1_enumset1(A_109, B_107, C_108))=k4_enumset1(A_67, A_105, B_106, A_109, B_107, C_108))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_343])).
% 3.57/1.67  tff(c_18, plain, (![D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (k2_xboole_0(k2_enumset1(A_34, B_35, C_36, D_37), k1_enumset1(E_38, F_39, G_40))=k5_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.67  tff(c_238, plain, (![A_96, A_7, D_95, B_93, B_8]: (k2_xboole_0(k2_tarski(A_96, B_93), k2_xboole_0(k2_tarski(A_7, B_8), D_95))=k2_xboole_0(k2_enumset1(A_96, B_93, A_7, B_8), D_95))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_233])).
% 3.57/1.67  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_1, B_2), C_3), D_4)=k2_xboole_0(A_1, k2_xboole_0(k2_xboole_0(B_2, C_3), D_4)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.67  tff(c_354, plain, (![B_111, C_114, A_110, D_112, D_113]: (k2_xboole_0(k2_xboole_0(A_110, k2_xboole_0(k2_xboole_0(B_111, C_114), D_113)), D_112)=k2_xboole_0(k2_xboole_0(A_110, B_111), k2_xboole_0(k2_xboole_0(C_114, D_113), D_112)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_2])).
% 3.57/1.67  tff(c_659, plain, (![A_152, D_155, A_154, D_156, B_153]: (k2_xboole_0(k2_xboole_0(A_152, k1_tarski(A_154)), k2_xboole_0(k2_xboole_0(k1_tarski(B_153), D_156), D_155))=k2_xboole_0(k2_xboole_0(A_152, k2_xboole_0(k2_tarski(A_154, B_153), D_156)), D_155))), inference(superposition, [status(thm), theory('equality')], [c_6, c_354])).
% 3.57/1.67  tff(c_756, plain, (![A_152, D_155, A_7, A_154, B_8]: (k2_xboole_0(k2_xboole_0(A_152, k2_xboole_0(k2_tarski(A_154, A_7), k1_tarski(B_8))), D_155)=k2_xboole_0(k2_xboole_0(A_152, k1_tarski(A_154)), k2_xboole_0(k2_tarski(A_7, B_8), D_155)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_659])).
% 3.57/1.67  tff(c_782, plain, (![A_159, D_160, A_161, A_157, B_158]: (k2_xboole_0(k2_xboole_0(A_157, k1_tarski(A_161)), k2_xboole_0(k2_tarski(A_159, B_158), D_160))=k2_xboole_0(k2_xboole_0(A_157, k1_enumset1(A_161, A_159, B_158)), D_160))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_756])).
% 3.57/1.67  tff(c_884, plain, (![A_163, C_165, A_166, B_164, A_162]: (k2_xboole_0(k2_xboole_0(A_162, k1_enumset1(A_163, A_166, B_164)), k1_tarski(C_165))=k2_xboole_0(k2_xboole_0(A_162, k1_tarski(A_163)), k1_enumset1(A_166, B_164, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_782])).
% 3.57/1.67  tff(c_87, plain, (![D_55, C_11, B_10, C_54, A_9]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_xboole_0(k2_xboole_0(k1_tarski(C_11), C_54), D_55))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_9, B_10, C_11), C_54), D_55))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 3.57/1.67  tff(c_914, plain, (![A_163, C_165, C_11, B_10, A_166, B_164, A_9]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_xboole_0(k2_xboole_0(k1_tarski(C_11), k1_tarski(A_163)), k1_enumset1(A_166, B_164, C_165)))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(A_163, A_166, B_164)), k1_tarski(C_165)))), inference(superposition, [status(thm), theory('equality')], [c_884, c_87])).
% 3.57/1.67  tff(c_963, plain, (![A_163, C_165, C_11, B_10, A_166, B_164, A_9]: (k2_xboole_0(k4_enumset1(A_9, B_10, C_11, A_163, A_166, B_164), k1_tarski(C_165))=k5_enumset1(A_9, B_10, C_11, A_163, A_166, B_164, C_165))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_18, c_238, c_6, c_914])).
% 3.57/1.67  tff(c_20, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.57/1.67  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_963, c_20])).
% 3.57/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.67  
% 3.57/1.67  Inference rules
% 3.57/1.67  ----------------------
% 3.57/1.67  #Ref     : 0
% 3.57/1.67  #Sup     : 244
% 3.57/1.67  #Fact    : 0
% 3.57/1.67  #Define  : 0
% 3.57/1.67  #Split   : 0
% 3.57/1.67  #Chain   : 0
% 3.57/1.67  #Close   : 0
% 3.57/1.67  
% 3.57/1.67  Ordering : KBO
% 3.57/1.67  
% 3.57/1.67  Simplification rules
% 3.57/1.67  ----------------------
% 3.57/1.67  #Subsume      : 0
% 3.57/1.67  #Demod        : 256
% 3.57/1.67  #Tautology    : 101
% 3.57/1.67  #SimpNegUnit  : 0
% 3.57/1.67  #BackRed      : 2
% 3.57/1.67  
% 3.57/1.67  #Partial instantiations: 0
% 3.57/1.67  #Strategies tried      : 1
% 3.57/1.67  
% 3.57/1.67  Timing (in seconds)
% 3.57/1.67  ----------------------
% 3.57/1.68  Preprocessing        : 0.33
% 3.57/1.68  Parsing              : 0.19
% 3.57/1.68  CNF conversion       : 0.02
% 3.57/1.68  Main loop            : 0.49
% 3.57/1.68  Inferencing          : 0.20
% 3.57/1.68  Reduction            : 0.20
% 3.57/1.68  Demodulation         : 0.17
% 3.57/1.68  BG Simplification    : 0.03
% 3.57/1.68  Subsumption          : 0.04
% 3.57/1.68  Abstraction          : 0.05
% 3.57/1.68  MUC search           : 0.00
% 3.57/1.68  Cooper               : 0.00
% 3.57/1.68  Total                : 0.86
% 3.57/1.68  Index Insertion      : 0.00
% 3.57/1.68  Index Deletion       : 0.00
% 3.57/1.68  Index Matching       : 0.00
% 3.57/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

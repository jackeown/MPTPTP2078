%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 107 expanded)
%              Number of equality atoms :   51 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_10,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_tarski(A_17),k1_enumset1(B_18,C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_64,B_65,C_66] : k2_enumset1(A_64,A_64,B_65,C_66) = k1_enumset1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    ! [A_86,B_87,C_88,D_89] : k2_xboole_0(k2_tarski(A_86,B_87),k2_tarski(C_88,D_89)) = k2_enumset1(A_86,B_87,C_88,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_61,C_88,D_89] : k2_xboole_0(k1_tarski(A_61),k2_tarski(C_88,D_89)) = k2_enumset1(A_61,A_61,C_88,D_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_147])).

tff(c_162,plain,(
    ! [A_61,C_88,D_89] : k2_xboole_0(k1_tarski(A_61),k2_tarski(C_88,D_89)) = k1_enumset1(A_61,C_88,D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_156])).

tff(c_26,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_77,B_78,C_79,D_80] : k2_xboole_0(k1_tarski(A_77),k1_enumset1(B_78,C_79,D_80)) = k2_enumset1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [A_81,A_82,B_83] : k2_xboole_0(k1_tarski(A_81),k2_tarski(A_82,B_83)) = k2_enumset1(A_81,A_82,A_82,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_108,plain,(
    ! [B_65,C_66] : k2_xboole_0(k1_tarski(B_65),k2_tarski(B_65,C_66)) = k1_enumset1(B_65,B_65,C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_186,plain,(
    ! [B_91,C_92] : k2_xboole_0(k1_tarski(B_91),k2_tarski(B_91,C_92)) = k2_tarski(B_91,C_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_85,plain,(
    ! [A_77,A_62,B_63] : k2_xboole_0(k1_tarski(A_77),k2_tarski(A_62,B_63)) = k2_enumset1(A_77,A_62,A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_192,plain,(
    ! [B_91,C_92] : k2_enumset1(B_91,B_91,B_91,C_92) = k2_tarski(B_91,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_85])).

tff(c_261,plain,(
    ! [A_96,E_100,B_99,D_97,C_98] : k2_xboole_0(k1_tarski(A_96),k2_enumset1(B_99,C_98,D_97,E_100)) = k3_enumset1(A_96,B_99,C_98,D_97,E_100) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_270,plain,(
    ! [A_96,B_91,C_92] : k3_enumset1(A_96,B_91,B_91,B_91,C_92) = k2_xboole_0(k1_tarski(A_96),k2_tarski(B_91,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_261])).

tff(c_623,plain,(
    ! [A_149,B_150,C_151] : k3_enumset1(A_149,B_150,B_150,B_150,C_151) = k1_enumset1(A_149,B_150,C_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_270])).

tff(c_14,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] : k2_xboole_0(k1_tarski(A_26),k3_enumset1(B_27,C_28,D_29,E_30,F_31)) = k4_enumset1(A_26,B_27,C_28,D_29,E_30,F_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_640,plain,(
    ! [A_26,A_149,B_150,C_151] : k4_enumset1(A_26,A_149,B_150,B_150,B_150,C_151) = k2_xboole_0(k1_tarski(A_26),k1_enumset1(A_149,B_150,C_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_14])).

tff(c_670,plain,(
    ! [A_26,A_149,B_150,C_151] : k4_enumset1(A_26,A_149,B_150,B_150,B_150,C_151) = k2_enumset1(A_26,A_149,B_150,C_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_640])).

tff(c_8,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_81,A_61] : k2_xboole_0(k1_tarski(A_81),k1_tarski(A_61)) = k2_enumset1(A_81,A_61,A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_88])).

tff(c_118,plain,(
    ! [A_81,A_61] : k2_enumset1(A_81,A_61,A_61,A_61) = k2_tarski(A_81,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_273,plain,(
    ! [A_96,A_81,A_61] : k3_enumset1(A_96,A_81,A_61,A_61,A_61) = k2_xboole_0(k1_tarski(A_96),k2_tarski(A_81,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_261])).

tff(c_544,plain,(
    ! [A_139,A_140,A_141] : k3_enumset1(A_139,A_140,A_141,A_141,A_141) = k1_enumset1(A_139,A_140,A_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_273])).

tff(c_16,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k2_xboole_0(k3_enumset1(A_32,B_33,C_34,D_35,E_36),k1_tarski(F_37)) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_563,plain,(
    ! [A_139,A_140,A_141,F_37] : k4_enumset1(A_139,A_140,A_141,A_141,A_141,F_37) = k2_xboole_0(k1_enumset1(A_139,A_140,A_141),k1_tarski(F_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_16])).

tff(c_840,plain,(
    ! [A_139,A_140,A_141,F_37] : k2_xboole_0(k1_enumset1(A_139,A_140,A_141),k1_tarski(F_37)) = k2_enumset1(A_139,A_140,A_141,F_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_563])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k1_tarski(A_21),k2_enumset1(B_22,C_23,D_24,E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_279,plain,(
    ! [A_96,A_64,B_65,C_66] : k3_enumset1(A_96,A_64,A_64,B_65,C_66) = k2_xboole_0(k1_tarski(A_96),k1_enumset1(A_64,B_65,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_261])).

tff(c_282,plain,(
    ! [A_96,A_64,B_65,C_66] : k3_enumset1(A_96,A_64,A_64,B_65,C_66) = k2_enumset1(A_96,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_279])).

tff(c_468,plain,(
    ! [B_126,A_127,E_130,F_128,D_125,C_129] : k2_xboole_0(k1_tarski(A_127),k3_enumset1(B_126,C_129,D_125,E_130,F_128)) = k4_enumset1(A_127,B_126,C_129,D_125,E_130,F_128) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_477,plain,(
    ! [A_96,A_127,C_66,A_64,B_65] : k4_enumset1(A_127,A_96,A_64,A_64,B_65,C_66) = k2_xboole_0(k1_tarski(A_127),k2_enumset1(A_96,A_64,B_65,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_468])).

tff(c_480,plain,(
    ! [A_96,A_127,C_66,A_64,B_65] : k4_enumset1(A_127,A_96,A_64,A_64,B_65,C_66) = k3_enumset1(A_127,A_96,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_477])).

tff(c_349,plain,(
    ! [A_112,A_113,B_114] : k2_enumset1(A_112,A_113,A_113,B_114) = k1_enumset1(A_112,A_113,B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_85])).

tff(c_355,plain,(
    ! [A_21,A_112,A_113,B_114] : k3_enumset1(A_21,A_112,A_113,A_113,B_114) = k2_xboole_0(k1_tarski(A_21),k1_enumset1(A_112,A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_12])).

tff(c_481,plain,(
    ! [A_131,A_132,A_133,B_134] : k3_enumset1(A_131,A_132,A_133,A_133,B_134) = k2_enumset1(A_131,A_132,A_133,B_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_355])).

tff(c_494,plain,(
    ! [A_133,A_132,F_37,A_131,B_134] : k4_enumset1(A_131,A_132,A_133,A_133,B_134,F_37) = k2_xboole_0(k2_enumset1(A_131,A_132,A_133,B_134),k1_tarski(F_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_16])).

tff(c_1397,plain,(
    ! [A_228,A_230,F_229,B_231,A_227] : k2_xboole_0(k2_enumset1(A_227,A_228,A_230,B_231),k1_tarski(F_229)) = k3_enumset1(A_227,A_228,A_230,B_231,F_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_494])).

tff(c_1418,plain,(
    ! [A_64,B_65,C_66,F_229] : k3_enumset1(A_64,A_64,B_65,C_66,F_229) = k2_xboole_0(k1_enumset1(A_64,B_65,C_66),k1_tarski(F_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1397])).

tff(c_1425,plain,(
    ! [A_64,B_65,C_66,F_229] : k3_enumset1(A_64,A_64,B_65,C_66,F_229) = k2_enumset1(A_64,B_65,C_66,F_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_1418])).

tff(c_30,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.49  
% 3.28/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.49  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.28/1.49  
% 3.28/1.49  %Foreground sorts:
% 3.28/1.49  
% 3.28/1.49  
% 3.28/1.49  %Background operators:
% 3.28/1.49  
% 3.28/1.49  
% 3.28/1.49  %Foreground operators:
% 3.28/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.49  
% 3.28/1.51  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.28/1.51  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.28/1.51  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.28/1.51  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.28/1.51  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.28/1.51  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.28/1.51  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.28/1.51  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.28/1.51  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.28/1.51  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.28/1.51  tff(c_10, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_tarski(A_17), k1_enumset1(B_18, C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.51  tff(c_28, plain, (![A_64, B_65, C_66]: (k2_enumset1(A_64, A_64, B_65, C_66)=k1_enumset1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.51  tff(c_24, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.51  tff(c_147, plain, (![A_86, B_87, C_88, D_89]: (k2_xboole_0(k2_tarski(A_86, B_87), k2_tarski(C_88, D_89))=k2_enumset1(A_86, B_87, C_88, D_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.51  tff(c_156, plain, (![A_61, C_88, D_89]: (k2_xboole_0(k1_tarski(A_61), k2_tarski(C_88, D_89))=k2_enumset1(A_61, A_61, C_88, D_89))), inference(superposition, [status(thm), theory('equality')], [c_24, c_147])).
% 3.28/1.51  tff(c_162, plain, (![A_61, C_88, D_89]: (k2_xboole_0(k1_tarski(A_61), k2_tarski(C_88, D_89))=k1_enumset1(A_61, C_88, D_89))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_156])).
% 3.28/1.51  tff(c_26, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.51  tff(c_76, plain, (![A_77, B_78, C_79, D_80]: (k2_xboole_0(k1_tarski(A_77), k1_enumset1(B_78, C_79, D_80))=k2_enumset1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.51  tff(c_88, plain, (![A_81, A_82, B_83]: (k2_xboole_0(k1_tarski(A_81), k2_tarski(A_82, B_83))=k2_enumset1(A_81, A_82, A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76])).
% 3.28/1.51  tff(c_108, plain, (![B_65, C_66]: (k2_xboole_0(k1_tarski(B_65), k2_tarski(B_65, C_66))=k1_enumset1(B_65, B_65, C_66))), inference(superposition, [status(thm), theory('equality')], [c_28, c_88])).
% 3.28/1.51  tff(c_186, plain, (![B_91, C_92]: (k2_xboole_0(k1_tarski(B_91), k2_tarski(B_91, C_92))=k2_tarski(B_91, C_92))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108])).
% 3.28/1.51  tff(c_85, plain, (![A_77, A_62, B_63]: (k2_xboole_0(k1_tarski(A_77), k2_tarski(A_62, B_63))=k2_enumset1(A_77, A_62, A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76])).
% 3.28/1.51  tff(c_192, plain, (![B_91, C_92]: (k2_enumset1(B_91, B_91, B_91, C_92)=k2_tarski(B_91, C_92))), inference(superposition, [status(thm), theory('equality')], [c_186, c_85])).
% 3.28/1.51  tff(c_261, plain, (![A_96, E_100, B_99, D_97, C_98]: (k2_xboole_0(k1_tarski(A_96), k2_enumset1(B_99, C_98, D_97, E_100))=k3_enumset1(A_96, B_99, C_98, D_97, E_100))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.51  tff(c_270, plain, (![A_96, B_91, C_92]: (k3_enumset1(A_96, B_91, B_91, B_91, C_92)=k2_xboole_0(k1_tarski(A_96), k2_tarski(B_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_192, c_261])).
% 3.28/1.51  tff(c_623, plain, (![A_149, B_150, C_151]: (k3_enumset1(A_149, B_150, B_150, B_150, C_151)=k1_enumset1(A_149, B_150, C_151))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_270])).
% 3.28/1.51  tff(c_14, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k2_xboole_0(k1_tarski(A_26), k3_enumset1(B_27, C_28, D_29, E_30, F_31))=k4_enumset1(A_26, B_27, C_28, D_29, E_30, F_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.51  tff(c_640, plain, (![A_26, A_149, B_150, C_151]: (k4_enumset1(A_26, A_149, B_150, B_150, B_150, C_151)=k2_xboole_0(k1_tarski(A_26), k1_enumset1(A_149, B_150, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_623, c_14])).
% 3.28/1.51  tff(c_670, plain, (![A_26, A_149, B_150, C_151]: (k4_enumset1(A_26, A_149, B_150, B_150, B_150, C_151)=k2_enumset1(A_26, A_149, B_150, C_151))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_640])).
% 3.28/1.51  tff(c_8, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.51  tff(c_111, plain, (![A_81, A_61]: (k2_xboole_0(k1_tarski(A_81), k1_tarski(A_61))=k2_enumset1(A_81, A_61, A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_24, c_88])).
% 3.28/1.51  tff(c_118, plain, (![A_81, A_61]: (k2_enumset1(A_81, A_61, A_61, A_61)=k2_tarski(A_81, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 3.28/1.51  tff(c_273, plain, (![A_96, A_81, A_61]: (k3_enumset1(A_96, A_81, A_61, A_61, A_61)=k2_xboole_0(k1_tarski(A_96), k2_tarski(A_81, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_261])).
% 3.28/1.51  tff(c_544, plain, (![A_139, A_140, A_141]: (k3_enumset1(A_139, A_140, A_141, A_141, A_141)=k1_enumset1(A_139, A_140, A_141))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_273])).
% 3.28/1.51  tff(c_16, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k2_xboole_0(k3_enumset1(A_32, B_33, C_34, D_35, E_36), k1_tarski(F_37))=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.51  tff(c_563, plain, (![A_139, A_140, A_141, F_37]: (k4_enumset1(A_139, A_140, A_141, A_141, A_141, F_37)=k2_xboole_0(k1_enumset1(A_139, A_140, A_141), k1_tarski(F_37)))), inference(superposition, [status(thm), theory('equality')], [c_544, c_16])).
% 3.28/1.51  tff(c_840, plain, (![A_139, A_140, A_141, F_37]: (k2_xboole_0(k1_enumset1(A_139, A_140, A_141), k1_tarski(F_37))=k2_enumset1(A_139, A_140, A_141, F_37))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_563])).
% 3.28/1.51  tff(c_12, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k1_tarski(A_21), k2_enumset1(B_22, C_23, D_24, E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.51  tff(c_279, plain, (![A_96, A_64, B_65, C_66]: (k3_enumset1(A_96, A_64, A_64, B_65, C_66)=k2_xboole_0(k1_tarski(A_96), k1_enumset1(A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_261])).
% 3.28/1.51  tff(c_282, plain, (![A_96, A_64, B_65, C_66]: (k3_enumset1(A_96, A_64, A_64, B_65, C_66)=k2_enumset1(A_96, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_279])).
% 3.28/1.51  tff(c_468, plain, (![B_126, A_127, E_130, F_128, D_125, C_129]: (k2_xboole_0(k1_tarski(A_127), k3_enumset1(B_126, C_129, D_125, E_130, F_128))=k4_enumset1(A_127, B_126, C_129, D_125, E_130, F_128))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.51  tff(c_477, plain, (![A_96, A_127, C_66, A_64, B_65]: (k4_enumset1(A_127, A_96, A_64, A_64, B_65, C_66)=k2_xboole_0(k1_tarski(A_127), k2_enumset1(A_96, A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_468])).
% 3.28/1.51  tff(c_480, plain, (![A_96, A_127, C_66, A_64, B_65]: (k4_enumset1(A_127, A_96, A_64, A_64, B_65, C_66)=k3_enumset1(A_127, A_96, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_477])).
% 3.28/1.51  tff(c_349, plain, (![A_112, A_113, B_114]: (k2_enumset1(A_112, A_113, A_113, B_114)=k1_enumset1(A_112, A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_85])).
% 3.28/1.51  tff(c_355, plain, (![A_21, A_112, A_113, B_114]: (k3_enumset1(A_21, A_112, A_113, A_113, B_114)=k2_xboole_0(k1_tarski(A_21), k1_enumset1(A_112, A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_349, c_12])).
% 3.28/1.51  tff(c_481, plain, (![A_131, A_132, A_133, B_134]: (k3_enumset1(A_131, A_132, A_133, A_133, B_134)=k2_enumset1(A_131, A_132, A_133, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_355])).
% 3.28/1.51  tff(c_494, plain, (![A_133, A_132, F_37, A_131, B_134]: (k4_enumset1(A_131, A_132, A_133, A_133, B_134, F_37)=k2_xboole_0(k2_enumset1(A_131, A_132, A_133, B_134), k1_tarski(F_37)))), inference(superposition, [status(thm), theory('equality')], [c_481, c_16])).
% 3.28/1.51  tff(c_1397, plain, (![A_228, A_230, F_229, B_231, A_227]: (k2_xboole_0(k2_enumset1(A_227, A_228, A_230, B_231), k1_tarski(F_229))=k3_enumset1(A_227, A_228, A_230, B_231, F_229))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_494])).
% 3.28/1.51  tff(c_1418, plain, (![A_64, B_65, C_66, F_229]: (k3_enumset1(A_64, A_64, B_65, C_66, F_229)=k2_xboole_0(k1_enumset1(A_64, B_65, C_66), k1_tarski(F_229)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1397])).
% 3.28/1.51  tff(c_1425, plain, (![A_64, B_65, C_66, F_229]: (k3_enumset1(A_64, A_64, B_65, C_66, F_229)=k2_enumset1(A_64, B_65, C_66, F_229))), inference(demodulation, [status(thm), theory('equality')], [c_840, c_1418])).
% 3.28/1.51  tff(c_30, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.51  tff(c_1651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1425, c_30])).
% 3.28/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.51  
% 3.28/1.51  Inference rules
% 3.28/1.51  ----------------------
% 3.28/1.51  #Ref     : 0
% 3.28/1.51  #Sup     : 365
% 3.28/1.51  #Fact    : 0
% 3.28/1.51  #Define  : 0
% 3.28/1.51  #Split   : 0
% 3.28/1.51  #Chain   : 0
% 3.28/1.51  #Close   : 0
% 3.28/1.51  
% 3.28/1.51  Ordering : KBO
% 3.28/1.51  
% 3.28/1.51  Simplification rules
% 3.28/1.51  ----------------------
% 3.28/1.51  #Subsume      : 0
% 3.28/1.51  #Demod        : 367
% 3.28/1.51  #Tautology    : 288
% 3.28/1.51  #SimpNegUnit  : 0
% 3.28/1.51  #BackRed      : 3
% 3.28/1.51  
% 3.28/1.51  #Partial instantiations: 0
% 3.28/1.51  #Strategies tried      : 1
% 3.28/1.51  
% 3.28/1.51  Timing (in seconds)
% 3.28/1.51  ----------------------
% 3.28/1.51  Preprocessing        : 0.30
% 3.28/1.51  Parsing              : 0.16
% 3.28/1.51  CNF conversion       : 0.02
% 3.28/1.51  Main loop            : 0.44
% 3.28/1.51  Inferencing          : 0.18
% 3.28/1.51  Reduction            : 0.17
% 3.28/1.51  Demodulation         : 0.14
% 3.28/1.51  BG Simplification    : 0.03
% 3.28/1.51  Subsumption          : 0.04
% 3.28/1.51  Abstraction          : 0.03
% 3.28/1.51  MUC search           : 0.00
% 3.28/1.51  Cooper               : 0.00
% 3.28/1.51  Total                : 0.77
% 3.28/1.51  Index Insertion      : 0.00
% 3.28/1.51  Index Deletion       : 0.00
% 3.28/1.51  Index Matching       : 0.00
% 3.28/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

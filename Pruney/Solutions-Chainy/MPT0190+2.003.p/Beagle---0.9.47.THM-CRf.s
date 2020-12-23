%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 9.06s
% Output     : CNFRefutation 9.06s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 219 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 203 expanded)
%              Number of equality atoms :   65 ( 202 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_tarski(D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_397,plain,(
    ! [C_89,A_88,D_87,B_90,E_86] : k2_xboole_0(k1_enumset1(A_88,B_90,C_89),k2_tarski(D_87,E_86)) = k3_enumset1(A_88,B_90,C_89,D_87,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_418,plain,(
    ! [A_88,B_90,C_89,A_20] : k3_enumset1(A_88,B_90,C_89,A_20,A_20) = k2_xboole_0(k1_enumset1(A_88,B_90,C_89),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_397])).

tff(c_422,plain,(
    ! [A_88,B_90,C_89,A_20] : k3_enumset1(A_88,B_90,C_89,A_20,A_20) = k2_enumset1(A_88,B_90,C_89,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_418])).

tff(c_92,plain,(
    ! [A_46,B_47,C_48,D_49] : k3_enumset1(A_46,A_46,B_47,C_48,D_49) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_33,B_34] : k3_enumset1(A_33,A_33,A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [C_50,D_51] : k2_enumset1(C_50,C_50,C_50,D_51) = k2_tarski(C_50,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_20])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [C_50,D_51] : k1_enumset1(C_50,C_50,D_51) = k2_tarski(C_50,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_14])).

tff(c_6,plain,(
    ! [C_10,B_9,A_8] : k1_enumset1(C_10,B_9,A_8) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [C_70,A_74,E_73,B_72,D_71] : k2_xboole_0(k2_tarski(A_74,B_72),k1_enumset1(C_70,D_71,E_73)) = k3_enumset1(A_74,B_72,C_70,D_71,E_73) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1356,plain,(
    ! [C_130,A_126,B_127,A_129,B_128] : k2_xboole_0(k2_tarski(A_129,B_127),k1_enumset1(A_126,B_128,C_130)) = k3_enumset1(A_129,B_127,C_130,B_128,A_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_242])).

tff(c_1401,plain,(
    ! [A_129,B_127,D_51,C_50] : k3_enumset1(A_129,B_127,D_51,C_50,C_50) = k2_xboole_0(k2_tarski(A_129,B_127),k2_tarski(C_50,D_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1356])).

tff(c_1415,plain,(
    ! [A_129,B_127,C_50,D_51] : k2_xboole_0(k2_tarski(A_129,B_127),k2_tarski(C_50,D_51)) = k2_enumset1(A_129,B_127,D_51,C_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_1401])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k2_tarski(D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_943,plain,(
    ! [B_115,D_116,E_117,A_114,C_118] : k2_xboole_0(k1_enumset1(A_114,B_115,C_118),k2_tarski(D_116,E_117)) = k3_enumset1(C_118,B_115,A_114,D_116,E_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_397])).

tff(c_3148,plain,(
    ! [C_171,A_170,B_172,D_169,E_168] : k3_enumset1(C_171,B_172,A_170,D_169,E_168) = k3_enumset1(A_170,B_172,C_171,D_169,E_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_943])).

tff(c_3197,plain,(
    ! [B_25,A_24,C_26,D_27] : k3_enumset1(B_25,A_24,A_24,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3148])).

tff(c_979,plain,(
    ! [D_51,C_50,D_116,E_117] : k3_enumset1(D_51,C_50,C_50,D_116,E_117) = k2_xboole_0(k2_tarski(C_50,D_51),k2_tarski(D_116,E_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_943])).

tff(c_16474,plain,(
    ! [C_50,D_51,E_117,D_116] : k2_enumset1(C_50,D_51,E_117,D_116) = k2_enumset1(C_50,D_51,D_116,E_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_3197,c_979])).

tff(c_147,plain,(
    ! [A_54,B_55,C_56,D_57] : k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k1_tarski(D_57)) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,(
    ! [C_50,D_51,D_57] : k2_xboole_0(k2_tarski(C_50,D_51),k1_tarski(D_57)) = k2_enumset1(C_50,C_50,D_51,D_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_147])).

tff(c_165,plain,(
    ! [C_50,D_51,D_57] : k2_xboole_0(k2_tarski(C_50,D_51),k1_tarski(D_57)) = k1_enumset1(C_50,D_51,D_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_124,plain,(
    ! [C_52,D_53] : k1_enumset1(C_52,C_52,D_53) = k2_tarski(C_52,D_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_14])).

tff(c_167,plain,(
    ! [C_58,B_59] : k1_enumset1(C_58,B_59,B_59) = k2_tarski(B_59,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_173,plain,(
    ! [B_59,C_58,D_14] : k2_xboole_0(k2_tarski(B_59,C_58),k1_tarski(D_14)) = k2_enumset1(C_58,B_59,B_59,D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_267,plain,(
    ! [C_58,B_59,D_14] : k2_enumset1(C_58,B_59,B_59,D_14) = k1_enumset1(B_59,C_58,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_173])).

tff(c_220,plain,(
    ! [C_65,D_66,D_67] : k2_xboole_0(k2_tarski(C_65,D_66),k1_tarski(D_67)) = k1_enumset1(C_65,D_66,D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_229,plain,(
    ! [A_20,D_67] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_67)) = k1_enumset1(A_20,A_20,D_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_220])).

tff(c_232,plain,(
    ! [A_20,D_67] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_67)) = k2_tarski(A_20,D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_229])).

tff(c_423,plain,(
    ! [A_91,B_92,C_93,A_94] : k3_enumset1(A_91,B_92,C_93,A_94,A_94) = k2_enumset1(A_91,B_92,C_93,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_418])).

tff(c_434,plain,(
    ! [A_94] : k2_enumset1(A_94,A_94,A_94,A_94) = k2_tarski(A_94,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_20])).

tff(c_452,plain,(
    ! [A_95] : k2_enumset1(A_95,A_95,A_95,A_95) = k1_tarski(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_434])).

tff(c_464,plain,(
    ! [A_95] : k1_enumset1(A_95,A_95,A_95) = k1_tarski(A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_14])).

tff(c_263,plain,(
    ! [A_20,C_70,D_71,E_73] : k3_enumset1(A_20,A_20,C_70,D_71,E_73) = k2_xboole_0(k1_tarski(A_20),k1_enumset1(C_70,D_71,E_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_242])).

tff(c_643,plain,(
    ! [A_102,C_103,D_104,E_105] : k2_xboole_0(k1_tarski(A_102),k1_enumset1(C_103,D_104,E_105)) = k2_enumset1(A_102,C_103,D_104,E_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_263])).

tff(c_652,plain,(
    ! [A_102,A_95] : k2_xboole_0(k1_tarski(A_102),k1_tarski(A_95)) = k2_enumset1(A_102,A_95,A_95,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_643])).

tff(c_727,plain,(
    ! [A_108,A_109] : k2_enumset1(A_108,A_109,A_109,A_109) = k2_tarski(A_108,A_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_652])).

tff(c_441,plain,(
    ! [A_24,B_25,D_27] : k2_enumset1(A_24,B_25,D_27,D_27) = k2_enumset1(A_24,A_24,B_25,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_423])).

tff(c_450,plain,(
    ! [A_24,B_25,D_27] : k2_enumset1(A_24,B_25,D_27,D_27) = k1_enumset1(A_24,B_25,D_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_441])).

tff(c_793,plain,(
    ! [A_110,A_111] : k1_enumset1(A_110,A_111,A_111) = k2_tarski(A_110,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_450])).

tff(c_822,plain,(
    ! [A_110,A_111,D_14] : k2_xboole_0(k2_tarski(A_110,A_111),k1_tarski(D_14)) = k2_enumset1(A_110,A_111,A_111,D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_8])).

tff(c_1191,plain,(
    ! [A_124,A_123,D_125] : k1_enumset1(A_124,A_123,D_125) = k1_enumset1(A_123,A_124,D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_165,c_822])).

tff(c_7226,plain,(
    ! [A_257,A_258,D_259,D_260] : k2_xboole_0(k1_enumset1(A_257,A_258,D_259),k1_tarski(D_260)) = k2_enumset1(A_258,A_257,D_259,D_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_8])).

tff(c_7235,plain,(
    ! [A_258,A_257,D_259,D_260] : k2_enumset1(A_258,A_257,D_259,D_260) = k2_enumset1(A_257,A_258,D_259,D_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_7226,c_8])).

tff(c_266,plain,(
    ! [A_20,C_70,D_71,E_73] : k2_xboole_0(k1_tarski(A_20),k1_enumset1(C_70,D_71,E_73)) = k2_enumset1(A_20,C_70,D_71,E_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_263])).

tff(c_1410,plain,(
    ! [A_20,C_130,B_128,A_126] : k3_enumset1(A_20,A_20,C_130,B_128,A_126) = k2_xboole_0(k1_tarski(A_20),k1_enumset1(A_126,B_128,C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1356])).

tff(c_1418,plain,(
    ! [A_20,C_130,B_128,A_126] : k2_enumset1(A_20,C_130,B_128,A_126) = k2_enumset1(A_20,A_126,B_128,C_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_16,c_1410])).

tff(c_296,plain,(
    ! [C_78,B_79,A_80,D_81] : k2_xboole_0(k1_enumset1(C_78,B_79,A_80),k1_tarski(D_81)) = k2_enumset1(A_80,B_79,C_78,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_147])).

tff(c_302,plain,(
    ! [C_78,B_79,A_80,D_81] : k2_enumset1(C_78,B_79,A_80,D_81) = k2_enumset1(A_80,B_79,C_78,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_8])).

tff(c_22,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_327,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_22])).

tff(c_2213,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_327])).

tff(c_7311,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_2213])).

tff(c_16477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16474,c_7311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.06/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.06/3.09  
% 9.06/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.06/3.09  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.06/3.09  
% 9.06/3.09  %Foreground sorts:
% 9.06/3.09  
% 9.06/3.09  
% 9.06/3.09  %Background operators:
% 9.06/3.09  
% 9.06/3.09  
% 9.06/3.09  %Foreground operators:
% 9.06/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.06/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.06/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.06/3.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.06/3.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.06/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.06/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.06/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.06/3.09  tff('#skF_2', type, '#skF_2': $i).
% 9.06/3.09  tff('#skF_3', type, '#skF_3': $i).
% 9.06/3.09  tff('#skF_1', type, '#skF_1': $i).
% 9.06/3.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.06/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.06/3.09  tff('#skF_4', type, '#skF_4': $i).
% 9.06/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.06/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.06/3.09  
% 9.06/3.11  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 9.06/3.11  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.06/3.11  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 9.06/3.11  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 9.06/3.11  tff(f_45, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 9.06/3.11  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 9.06/3.11  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 9.06/3.11  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 9.06/3.11  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_enumset1)).
% 9.06/3.11  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_tarski(D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.06/3.11  tff(c_12, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.06/3.11  tff(c_397, plain, (![C_89, A_88, D_87, B_90, E_86]: (k2_xboole_0(k1_enumset1(A_88, B_90, C_89), k2_tarski(D_87, E_86))=k3_enumset1(A_88, B_90, C_89, D_87, E_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.06/3.11  tff(c_418, plain, (![A_88, B_90, C_89, A_20]: (k3_enumset1(A_88, B_90, C_89, A_20, A_20)=k2_xboole_0(k1_enumset1(A_88, B_90, C_89), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_397])).
% 9.06/3.11  tff(c_422, plain, (![A_88, B_90, C_89, A_20]: (k3_enumset1(A_88, B_90, C_89, A_20, A_20)=k2_enumset1(A_88, B_90, C_89, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_418])).
% 9.06/3.11  tff(c_92, plain, (![A_46, B_47, C_48, D_49]: (k3_enumset1(A_46, A_46, B_47, C_48, D_49)=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.06/3.11  tff(c_20, plain, (![A_33, B_34]: (k3_enumset1(A_33, A_33, A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.06/3.11  tff(c_108, plain, (![C_50, D_51]: (k2_enumset1(C_50, C_50, C_50, D_51)=k2_tarski(C_50, D_51))), inference(superposition, [status(thm), theory('equality')], [c_92, c_20])).
% 9.06/3.11  tff(c_14, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.06/3.11  tff(c_114, plain, (![C_50, D_51]: (k1_enumset1(C_50, C_50, D_51)=k2_tarski(C_50, D_51))), inference(superposition, [status(thm), theory('equality')], [c_108, c_14])).
% 9.06/3.11  tff(c_6, plain, (![C_10, B_9, A_8]: (k1_enumset1(C_10, B_9, A_8)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.06/3.11  tff(c_242, plain, (![C_70, A_74, E_73, B_72, D_71]: (k2_xboole_0(k2_tarski(A_74, B_72), k1_enumset1(C_70, D_71, E_73))=k3_enumset1(A_74, B_72, C_70, D_71, E_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.06/3.11  tff(c_1356, plain, (![C_130, A_126, B_127, A_129, B_128]: (k2_xboole_0(k2_tarski(A_129, B_127), k1_enumset1(A_126, B_128, C_130))=k3_enumset1(A_129, B_127, C_130, B_128, A_126))), inference(superposition, [status(thm), theory('equality')], [c_6, c_242])).
% 9.06/3.11  tff(c_1401, plain, (![A_129, B_127, D_51, C_50]: (k3_enumset1(A_129, B_127, D_51, C_50, C_50)=k2_xboole_0(k2_tarski(A_129, B_127), k2_tarski(C_50, D_51)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1356])).
% 9.06/3.11  tff(c_1415, plain, (![A_129, B_127, C_50, D_51]: (k2_xboole_0(k2_tarski(A_129, B_127), k2_tarski(C_50, D_51))=k2_enumset1(A_129, B_127, D_51, C_50))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_1401])).
% 9.06/3.11  tff(c_16, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.06/3.11  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k2_tarski(D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.06/3.11  tff(c_943, plain, (![B_115, D_116, E_117, A_114, C_118]: (k2_xboole_0(k1_enumset1(A_114, B_115, C_118), k2_tarski(D_116, E_117))=k3_enumset1(C_118, B_115, A_114, D_116, E_117))), inference(superposition, [status(thm), theory('equality')], [c_6, c_397])).
% 9.06/3.11  tff(c_3148, plain, (![C_171, A_170, B_172, D_169, E_168]: (k3_enumset1(C_171, B_172, A_170, D_169, E_168)=k3_enumset1(A_170, B_172, C_171, D_169, E_168))), inference(superposition, [status(thm), theory('equality')], [c_4, c_943])).
% 9.06/3.11  tff(c_3197, plain, (![B_25, A_24, C_26, D_27]: (k3_enumset1(B_25, A_24, A_24, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3148])).
% 9.06/3.11  tff(c_979, plain, (![D_51, C_50, D_116, E_117]: (k3_enumset1(D_51, C_50, C_50, D_116, E_117)=k2_xboole_0(k2_tarski(C_50, D_51), k2_tarski(D_116, E_117)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_943])).
% 9.06/3.11  tff(c_16474, plain, (![C_50, D_51, E_117, D_116]: (k2_enumset1(C_50, D_51, E_117, D_116)=k2_enumset1(C_50, D_51, D_116, E_117))), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_3197, c_979])).
% 9.06/3.11  tff(c_147, plain, (![A_54, B_55, C_56, D_57]: (k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k1_tarski(D_57))=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.06/3.11  tff(c_156, plain, (![C_50, D_51, D_57]: (k2_xboole_0(k2_tarski(C_50, D_51), k1_tarski(D_57))=k2_enumset1(C_50, C_50, D_51, D_57))), inference(superposition, [status(thm), theory('equality')], [c_114, c_147])).
% 9.06/3.11  tff(c_165, plain, (![C_50, D_51, D_57]: (k2_xboole_0(k2_tarski(C_50, D_51), k1_tarski(D_57))=k1_enumset1(C_50, D_51, D_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 9.06/3.11  tff(c_124, plain, (![C_52, D_53]: (k1_enumset1(C_52, C_52, D_53)=k2_tarski(C_52, D_53))), inference(superposition, [status(thm), theory('equality')], [c_108, c_14])).
% 9.06/3.11  tff(c_167, plain, (![C_58, B_59]: (k1_enumset1(C_58, B_59, B_59)=k2_tarski(B_59, C_58))), inference(superposition, [status(thm), theory('equality')], [c_6, c_124])).
% 9.06/3.11  tff(c_173, plain, (![B_59, C_58, D_14]: (k2_xboole_0(k2_tarski(B_59, C_58), k1_tarski(D_14))=k2_enumset1(C_58, B_59, B_59, D_14))), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 9.06/3.11  tff(c_267, plain, (![C_58, B_59, D_14]: (k2_enumset1(C_58, B_59, B_59, D_14)=k1_enumset1(B_59, C_58, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_173])).
% 9.06/3.11  tff(c_220, plain, (![C_65, D_66, D_67]: (k2_xboole_0(k2_tarski(C_65, D_66), k1_tarski(D_67))=k1_enumset1(C_65, D_66, D_67))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 9.06/3.11  tff(c_229, plain, (![A_20, D_67]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_67))=k1_enumset1(A_20, A_20, D_67))), inference(superposition, [status(thm), theory('equality')], [c_12, c_220])).
% 9.06/3.11  tff(c_232, plain, (![A_20, D_67]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_67))=k2_tarski(A_20, D_67))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_229])).
% 9.06/3.11  tff(c_423, plain, (![A_91, B_92, C_93, A_94]: (k3_enumset1(A_91, B_92, C_93, A_94, A_94)=k2_enumset1(A_91, B_92, C_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_418])).
% 9.06/3.11  tff(c_434, plain, (![A_94]: (k2_enumset1(A_94, A_94, A_94, A_94)=k2_tarski(A_94, A_94))), inference(superposition, [status(thm), theory('equality')], [c_423, c_20])).
% 9.06/3.11  tff(c_452, plain, (![A_95]: (k2_enumset1(A_95, A_95, A_95, A_95)=k1_tarski(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_434])).
% 9.06/3.11  tff(c_464, plain, (![A_95]: (k1_enumset1(A_95, A_95, A_95)=k1_tarski(A_95))), inference(superposition, [status(thm), theory('equality')], [c_452, c_14])).
% 9.06/3.11  tff(c_263, plain, (![A_20, C_70, D_71, E_73]: (k3_enumset1(A_20, A_20, C_70, D_71, E_73)=k2_xboole_0(k1_tarski(A_20), k1_enumset1(C_70, D_71, E_73)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_242])).
% 9.06/3.11  tff(c_643, plain, (![A_102, C_103, D_104, E_105]: (k2_xboole_0(k1_tarski(A_102), k1_enumset1(C_103, D_104, E_105))=k2_enumset1(A_102, C_103, D_104, E_105))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_263])).
% 9.06/3.11  tff(c_652, plain, (![A_102, A_95]: (k2_xboole_0(k1_tarski(A_102), k1_tarski(A_95))=k2_enumset1(A_102, A_95, A_95, A_95))), inference(superposition, [status(thm), theory('equality')], [c_464, c_643])).
% 9.06/3.11  tff(c_727, plain, (![A_108, A_109]: (k2_enumset1(A_108, A_109, A_109, A_109)=k2_tarski(A_108, A_109))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_652])).
% 9.06/3.11  tff(c_441, plain, (![A_24, B_25, D_27]: (k2_enumset1(A_24, B_25, D_27, D_27)=k2_enumset1(A_24, A_24, B_25, D_27))), inference(superposition, [status(thm), theory('equality')], [c_16, c_423])).
% 9.06/3.11  tff(c_450, plain, (![A_24, B_25, D_27]: (k2_enumset1(A_24, B_25, D_27, D_27)=k1_enumset1(A_24, B_25, D_27))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_441])).
% 9.06/3.11  tff(c_793, plain, (![A_110, A_111]: (k1_enumset1(A_110, A_111, A_111)=k2_tarski(A_110, A_111))), inference(superposition, [status(thm), theory('equality')], [c_727, c_450])).
% 9.06/3.11  tff(c_822, plain, (![A_110, A_111, D_14]: (k2_xboole_0(k2_tarski(A_110, A_111), k1_tarski(D_14))=k2_enumset1(A_110, A_111, A_111, D_14))), inference(superposition, [status(thm), theory('equality')], [c_793, c_8])).
% 9.06/3.11  tff(c_1191, plain, (![A_124, A_123, D_125]: (k1_enumset1(A_124, A_123, D_125)=k1_enumset1(A_123, A_124, D_125))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_165, c_822])).
% 9.06/3.11  tff(c_7226, plain, (![A_257, A_258, D_259, D_260]: (k2_xboole_0(k1_enumset1(A_257, A_258, D_259), k1_tarski(D_260))=k2_enumset1(A_258, A_257, D_259, D_260))), inference(superposition, [status(thm), theory('equality')], [c_1191, c_8])).
% 9.06/3.11  tff(c_7235, plain, (![A_258, A_257, D_259, D_260]: (k2_enumset1(A_258, A_257, D_259, D_260)=k2_enumset1(A_257, A_258, D_259, D_260))), inference(superposition, [status(thm), theory('equality')], [c_7226, c_8])).
% 9.06/3.11  tff(c_266, plain, (![A_20, C_70, D_71, E_73]: (k2_xboole_0(k1_tarski(A_20), k1_enumset1(C_70, D_71, E_73))=k2_enumset1(A_20, C_70, D_71, E_73))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_263])).
% 9.06/3.11  tff(c_1410, plain, (![A_20, C_130, B_128, A_126]: (k3_enumset1(A_20, A_20, C_130, B_128, A_126)=k2_xboole_0(k1_tarski(A_20), k1_enumset1(A_126, B_128, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1356])).
% 9.06/3.11  tff(c_1418, plain, (![A_20, C_130, B_128, A_126]: (k2_enumset1(A_20, C_130, B_128, A_126)=k2_enumset1(A_20, A_126, B_128, C_130))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_16, c_1410])).
% 9.06/3.11  tff(c_296, plain, (![C_78, B_79, A_80, D_81]: (k2_xboole_0(k1_enumset1(C_78, B_79, A_80), k1_tarski(D_81))=k2_enumset1(A_80, B_79, C_78, D_81))), inference(superposition, [status(thm), theory('equality')], [c_6, c_147])).
% 9.06/3.11  tff(c_302, plain, (![C_78, B_79, A_80, D_81]: (k2_enumset1(C_78, B_79, A_80, D_81)=k2_enumset1(A_80, B_79, C_78, D_81))), inference(superposition, [status(thm), theory('equality')], [c_296, c_8])).
% 9.06/3.11  tff(c_22, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.06/3.11  tff(c_327, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_22])).
% 9.06/3.11  tff(c_2213, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1418, c_327])).
% 9.06/3.11  tff(c_7311, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7235, c_2213])).
% 9.06/3.11  tff(c_16477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16474, c_7311])).
% 9.06/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.06/3.11  
% 9.06/3.11  Inference rules
% 9.06/3.11  ----------------------
% 9.06/3.11  #Ref     : 0
% 9.06/3.11  #Sup     : 3718
% 9.06/3.11  #Fact    : 0
% 9.06/3.11  #Define  : 0
% 9.06/3.11  #Split   : 0
% 9.06/3.11  #Chain   : 0
% 9.06/3.11  #Close   : 0
% 9.06/3.11  
% 9.06/3.11  Ordering : KBO
% 9.06/3.11  
% 9.06/3.11  Simplification rules
% 9.06/3.11  ----------------------
% 9.06/3.11  #Subsume      : 563
% 9.06/3.11  #Demod        : 4278
% 9.06/3.11  #Tautology    : 2775
% 9.06/3.11  #SimpNegUnit  : 0
% 9.06/3.11  #BackRed      : 4
% 9.06/3.11  
% 9.06/3.11  #Partial instantiations: 0
% 9.06/3.11  #Strategies tried      : 1
% 9.06/3.11  
% 9.06/3.11  Timing (in seconds)
% 9.06/3.11  ----------------------
% 9.31/3.11  Preprocessing        : 0.29
% 9.31/3.11  Parsing              : 0.15
% 9.31/3.11  CNF conversion       : 0.02
% 9.31/3.11  Main loop            : 2.05
% 9.31/3.11  Inferencing          : 0.60
% 9.31/3.11  Reduction            : 1.08
% 9.31/3.11  Demodulation         : 0.96
% 9.31/3.11  BG Simplification    : 0.05
% 9.31/3.11  Subsumption          : 0.23
% 9.31/3.11  Abstraction          : 0.10
% 9.31/3.11  MUC search           : 0.00
% 9.31/3.11  Cooper               : 0.00
% 9.31/3.11  Total                : 2.38
% 9.31/3.11  Index Insertion      : 0.00
% 9.31/3.11  Index Deletion       : 0.00
% 9.31/3.11  Index Matching       : 0.00
% 9.31/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

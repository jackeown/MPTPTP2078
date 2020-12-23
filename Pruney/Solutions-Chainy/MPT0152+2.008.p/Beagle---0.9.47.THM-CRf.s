%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:02 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   40 (  70 expanded)
%              Number of equality atoms :   39 (  69 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_18,plain,(
    ! [H_41,D_37,A_34,F_39,B_35,G_40,C_36,E_38] : k2_xboole_0(k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39),k2_tarski(G_40,H_41)) = k6_enumset1(A_34,B_35,C_36,D_37,E_38,F_39,G_40,H_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [F_84,A_81,C_83,B_85,E_86,D_82] : k2_xboole_0(k1_enumset1(A_81,B_85,C_83),k1_enumset1(D_82,E_86,F_84)) = k4_enumset1(A_81,B_85,C_83,D_82,E_86,F_84) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_213,plain,(
    ! [F_84,C_3,A_81,C_83,B_85,E_86,D_82] : k2_xboole_0(k1_enumset1(A_81,B_85,C_83),k2_xboole_0(k1_enumset1(D_82,E_86,F_84),C_3)) = k2_xboole_0(k4_enumset1(A_81,B_85,C_83,D_82,E_86,F_84),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_2])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k2_xboole_0(A_50,B_51),C_52) = k2_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_9,B_10,C_11,C_52] : k2_xboole_0(k2_tarski(A_9,B_10),k2_xboole_0(k1_tarski(C_11),C_52)) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_48])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [A_69,B_70,C_71,C_72] : k2_xboole_0(k1_tarski(A_69),k2_xboole_0(k2_tarski(B_70,C_71),C_72)) = k2_xboole_0(k1_enumset1(A_69,B_70,C_71),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_155,plain,(
    ! [D_15,C_14,A_12,B_13,A_69] : k2_xboole_0(k1_enumset1(A_69,A_12,B_13),k2_tarski(C_14,D_15)) = k2_xboole_0(k1_tarski(A_69),k2_enumset1(A_12,B_13,C_14,D_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k1_tarski(E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_53,B_54,C_55,D_56] : k2_xboole_0(k2_tarski(A_53,B_54),k2_tarski(C_55,D_56)) = k2_enumset1(A_53,B_54,C_55,D_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_219,plain,(
    ! [A_88,D_89,C_90,B_91,C_87] : k2_xboole_0(k2_tarski(A_88,B_91),k2_xboole_0(k2_tarski(C_87,D_89),C_90)) = k2_xboole_0(k2_enumset1(A_88,B_91,C_87,D_89),C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_246,plain,(
    ! [C_11,A_88,B_10,B_91,A_9] : k2_xboole_0(k2_enumset1(A_88,B_91,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k2_tarski(A_88,B_91),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_250,plain,(
    ! [C_11,A_88,B_10,B_91,A_9] : k2_xboole_0(k2_tarski(A_88,B_91),k1_enumset1(A_9,B_10,C_11)) = k3_enumset1(A_88,B_91,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_246])).

tff(c_175,plain,(
    ! [A_77,B_78,C_79,C_80] : k2_xboole_0(k2_tarski(A_77,B_78),k2_xboole_0(k1_tarski(C_79),C_80)) = k2_xboole_0(k1_enumset1(A_77,B_78,C_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_48])).

tff(c_199,plain,(
    ! [B_7,C_8,B_78,A_77,A_6] : k2_xboole_0(k1_enumset1(A_77,B_78,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k2_tarski(A_77,B_78),k1_enumset1(A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_296,plain,(
    ! [B_7,C_8,B_78,A_77,A_6] : k2_xboole_0(k1_tarski(A_77),k2_enumset1(B_78,A_6,B_7,C_8)) = k3_enumset1(A_77,B_78,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_250,c_199])).

tff(c_328,plain,(
    ! [A_124,C_126,B_122,A_123,D_125] : k2_xboole_0(k1_enumset1(A_124,A_123,B_122),k2_tarski(C_126,D_125)) = k3_enumset1(A_124,A_123,B_122,C_126,D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_155])).

tff(c_604,plain,(
    ! [C_190,B_189,A_187,A_188,D_191,C_192] : k2_xboole_0(k1_enumset1(A_187,A_188,B_189),k2_xboole_0(k2_tarski(C_190,D_191),C_192)) = k2_xboole_0(k3_enumset1(A_187,A_188,B_189,C_190,D_191),C_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_2])).

tff(c_637,plain,(
    ! [C_11,B_189,B_10,A_187,C_52,A_188,A_9] : k2_xboole_0(k3_enumset1(A_187,A_188,B_189,A_9,B_10),k2_xboole_0(k1_tarski(C_11),C_52)) = k2_xboole_0(k1_enumset1(A_187,A_188,B_189),k2_xboole_0(k1_enumset1(A_9,B_10,C_11),C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_604])).

tff(c_957,plain,(
    ! [A_268,A_271,B_267,B_266,A_272,C_270,C_269] : k2_xboole_0(k3_enumset1(A_268,A_271,B_266,A_272,B_267),k2_xboole_0(k1_tarski(C_270),C_269)) = k2_xboole_0(k4_enumset1(A_268,A_271,B_266,A_272,B_267,C_270),C_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_637])).

tff(c_999,plain,(
    ! [A_268,B_7,C_8,A_271,B_267,B_266,A_272,A_6] : k2_xboole_0(k4_enumset1(A_268,A_271,B_266,A_272,B_267,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k3_enumset1(A_268,A_271,B_266,A_272,B_267),k1_enumset1(A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_957])).

tff(c_1008,plain,(
    ! [A_268,B_7,C_8,A_271,B_267,B_266,A_272,A_6] : k2_xboole_0(k3_enumset1(A_268,A_271,B_266,A_272,B_267),k1_enumset1(A_6,B_7,C_8)) = k6_enumset1(A_268,A_271,B_266,A_272,B_267,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_999])).

tff(c_270,plain,(
    ! [F_97,E_100,D_99,G_102,B_101,A_103,C_98] : k2_xboole_0(k3_enumset1(A_103,B_101,C_98,D_99,E_100),k2_tarski(F_97,G_102)) = k5_enumset1(A_103,B_101,C_98,D_99,E_100,F_97,G_102) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_766,plain,(
    ! [D_227,C_226,F_225,G_221,B_222,A_223,E_224,C_220] : k2_xboole_0(k3_enumset1(A_223,B_222,C_220,D_227,E_224),k2_xboole_0(k2_tarski(F_225,G_221),C_226)) = k2_xboole_0(k5_enumset1(A_223,B_222,C_220,D_227,E_224,F_225,G_221),C_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_2])).

tff(c_802,plain,(
    ! [D_227,B_222,C_11,B_10,A_223,E_224,C_220,A_9] : k2_xboole_0(k5_enumset1(A_223,B_222,C_220,D_227,E_224,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k3_enumset1(A_223,B_222,C_220,D_227,E_224),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_766])).

tff(c_1154,plain,(
    ! [D_227,B_222,C_11,B_10,A_223,E_224,C_220,A_9] : k2_xboole_0(k5_enumset1(A_223,B_222,C_220,D_227,E_224,A_9,B_10),k1_tarski(C_11)) = k6_enumset1(A_223,B_222,C_220,D_227,E_224,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_802])).

tff(c_20,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.59  
% 3.53/1.60  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 3.53/1.60  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.53/1.60  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 3.53/1.60  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.53/1.60  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.53/1.60  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 3.53/1.60  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.53/1.60  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 3.53/1.60  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 3.53/1.60  tff(c_18, plain, (![H_41, D_37, A_34, F_39, B_35, G_40, C_36, E_38]: (k2_xboole_0(k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39), k2_tarski(G_40, H_41))=k6_enumset1(A_34, B_35, C_36, D_37, E_38, F_39, G_40, H_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.60  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.60  tff(c_207, plain, (![F_84, A_81, C_83, B_85, E_86, D_82]: (k2_xboole_0(k1_enumset1(A_81, B_85, C_83), k1_enumset1(D_82, E_86, F_84))=k4_enumset1(A_81, B_85, C_83, D_82, E_86, F_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.60  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.60  tff(c_213, plain, (![F_84, C_3, A_81, C_83, B_85, E_86, D_82]: (k2_xboole_0(k1_enumset1(A_81, B_85, C_83), k2_xboole_0(k1_enumset1(D_82, E_86, F_84), C_3))=k2_xboole_0(k4_enumset1(A_81, B_85, C_83, D_82, E_86, F_84), C_3))), inference(superposition, [status(thm), theory('equality')], [c_207, c_2])).
% 3.53/1.60  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.60  tff(c_48, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k2_xboole_0(A_50, B_51), C_52)=k2_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.60  tff(c_66, plain, (![A_9, B_10, C_11, C_52]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_xboole_0(k1_tarski(C_11), C_52))=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), C_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_48])).
% 3.53/1.60  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.60  tff(c_140, plain, (![A_69, B_70, C_71, C_72]: (k2_xboole_0(k1_tarski(A_69), k2_xboole_0(k2_tarski(B_70, C_71), C_72))=k2_xboole_0(k1_enumset1(A_69, B_70, C_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_6, c_48])).
% 3.53/1.60  tff(c_155, plain, (![D_15, C_14, A_12, B_13, A_69]: (k2_xboole_0(k1_enumset1(A_69, A_12, B_13), k2_tarski(C_14, D_15))=k2_xboole_0(k1_tarski(A_69), k2_enumset1(A_12, B_13, C_14, D_15)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 3.53/1.60  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k1_tarski(E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.60  tff(c_74, plain, (![A_53, B_54, C_55, D_56]: (k2_xboole_0(k2_tarski(A_53, B_54), k2_tarski(C_55, D_56))=k2_enumset1(A_53, B_54, C_55, D_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.60  tff(c_219, plain, (![A_88, D_89, C_90, B_91, C_87]: (k2_xboole_0(k2_tarski(A_88, B_91), k2_xboole_0(k2_tarski(C_87, D_89), C_90))=k2_xboole_0(k2_enumset1(A_88, B_91, C_87, D_89), C_90))), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 3.53/1.60  tff(c_246, plain, (![C_11, A_88, B_10, B_91, A_9]: (k2_xboole_0(k2_enumset1(A_88, B_91, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k2_tarski(A_88, B_91), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_219])).
% 3.53/1.60  tff(c_250, plain, (![C_11, A_88, B_10, B_91, A_9]: (k2_xboole_0(k2_tarski(A_88, B_91), k1_enumset1(A_9, B_10, C_11))=k3_enumset1(A_88, B_91, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_246])).
% 3.53/1.60  tff(c_175, plain, (![A_77, B_78, C_79, C_80]: (k2_xboole_0(k2_tarski(A_77, B_78), k2_xboole_0(k1_tarski(C_79), C_80))=k2_xboole_0(k1_enumset1(A_77, B_78, C_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_8, c_48])).
% 3.53/1.60  tff(c_199, plain, (![B_7, C_8, B_78, A_77, A_6]: (k2_xboole_0(k1_enumset1(A_77, B_78, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k2_tarski(A_77, B_78), k1_enumset1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_175])).
% 3.53/1.60  tff(c_296, plain, (![B_7, C_8, B_78, A_77, A_6]: (k2_xboole_0(k1_tarski(A_77), k2_enumset1(B_78, A_6, B_7, C_8))=k3_enumset1(A_77, B_78, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_250, c_199])).
% 3.53/1.61  tff(c_328, plain, (![A_124, C_126, B_122, A_123, D_125]: (k2_xboole_0(k1_enumset1(A_124, A_123, B_122), k2_tarski(C_126, D_125))=k3_enumset1(A_124, A_123, B_122, C_126, D_125))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_155])).
% 3.53/1.61  tff(c_604, plain, (![C_190, B_189, A_187, A_188, D_191, C_192]: (k2_xboole_0(k1_enumset1(A_187, A_188, B_189), k2_xboole_0(k2_tarski(C_190, D_191), C_192))=k2_xboole_0(k3_enumset1(A_187, A_188, B_189, C_190, D_191), C_192))), inference(superposition, [status(thm), theory('equality')], [c_328, c_2])).
% 3.53/1.61  tff(c_637, plain, (![C_11, B_189, B_10, A_187, C_52, A_188, A_9]: (k2_xboole_0(k3_enumset1(A_187, A_188, B_189, A_9, B_10), k2_xboole_0(k1_tarski(C_11), C_52))=k2_xboole_0(k1_enumset1(A_187, A_188, B_189), k2_xboole_0(k1_enumset1(A_9, B_10, C_11), C_52)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_604])).
% 3.53/1.61  tff(c_957, plain, (![A_268, A_271, B_267, B_266, A_272, C_270, C_269]: (k2_xboole_0(k3_enumset1(A_268, A_271, B_266, A_272, B_267), k2_xboole_0(k1_tarski(C_270), C_269))=k2_xboole_0(k4_enumset1(A_268, A_271, B_266, A_272, B_267, C_270), C_269))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_637])).
% 3.53/1.61  tff(c_999, plain, (![A_268, B_7, C_8, A_271, B_267, B_266, A_272, A_6]: (k2_xboole_0(k4_enumset1(A_268, A_271, B_266, A_272, B_267, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k3_enumset1(A_268, A_271, B_266, A_272, B_267), k1_enumset1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_957])).
% 3.53/1.61  tff(c_1008, plain, (![A_268, B_7, C_8, A_271, B_267, B_266, A_272, A_6]: (k2_xboole_0(k3_enumset1(A_268, A_271, B_266, A_272, B_267), k1_enumset1(A_6, B_7, C_8))=k6_enumset1(A_268, A_271, B_266, A_272, B_267, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_999])).
% 3.53/1.61  tff(c_270, plain, (![F_97, E_100, D_99, G_102, B_101, A_103, C_98]: (k2_xboole_0(k3_enumset1(A_103, B_101, C_98, D_99, E_100), k2_tarski(F_97, G_102))=k5_enumset1(A_103, B_101, C_98, D_99, E_100, F_97, G_102))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.53/1.61  tff(c_766, plain, (![D_227, C_226, F_225, G_221, B_222, A_223, E_224, C_220]: (k2_xboole_0(k3_enumset1(A_223, B_222, C_220, D_227, E_224), k2_xboole_0(k2_tarski(F_225, G_221), C_226))=k2_xboole_0(k5_enumset1(A_223, B_222, C_220, D_227, E_224, F_225, G_221), C_226))), inference(superposition, [status(thm), theory('equality')], [c_270, c_2])).
% 3.53/1.61  tff(c_802, plain, (![D_227, B_222, C_11, B_10, A_223, E_224, C_220, A_9]: (k2_xboole_0(k5_enumset1(A_223, B_222, C_220, D_227, E_224, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k3_enumset1(A_223, B_222, C_220, D_227, E_224), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_766])).
% 3.53/1.61  tff(c_1154, plain, (![D_227, B_222, C_11, B_10, A_223, E_224, C_220, A_9]: (k2_xboole_0(k5_enumset1(A_223, B_222, C_220, D_227, E_224, A_9, B_10), k1_tarski(C_11))=k6_enumset1(A_223, B_222, C_220, D_227, E_224, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_802])).
% 3.53/1.61  tff(c_20, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.53/1.61  tff(c_1157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1154, c_20])).
% 3.53/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  Inference rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Ref     : 0
% 3.53/1.61  #Sup     : 303
% 3.53/1.61  #Fact    : 0
% 3.53/1.61  #Define  : 0
% 3.53/1.61  #Split   : 0
% 3.53/1.61  #Chain   : 0
% 3.53/1.61  #Close   : 0
% 3.53/1.61  
% 3.53/1.61  Ordering : KBO
% 3.53/1.61  
% 3.53/1.61  Simplification rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Subsume      : 0
% 3.53/1.61  #Demod        : 157
% 3.53/1.61  #Tautology    : 147
% 3.53/1.61  #SimpNegUnit  : 0
% 3.53/1.61  #BackRed      : 2
% 3.53/1.61  
% 3.53/1.61  #Partial instantiations: 0
% 3.53/1.61  #Strategies tried      : 1
% 3.53/1.61  
% 3.53/1.61  Timing (in seconds)
% 3.53/1.61  ----------------------
% 3.53/1.61  Preprocessing        : 0.29
% 3.53/1.61  Parsing              : 0.17
% 3.53/1.61  CNF conversion       : 0.02
% 3.53/1.61  Main loop            : 0.54
% 3.53/1.61  Inferencing          : 0.25
% 3.53/1.61  Reduction            : 0.18
% 3.53/1.61  Demodulation         : 0.15
% 3.53/1.61  BG Simplification    : 0.04
% 3.53/1.61  Subsumption          : 0.05
% 3.53/1.61  Abstraction          : 0.05
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.86
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

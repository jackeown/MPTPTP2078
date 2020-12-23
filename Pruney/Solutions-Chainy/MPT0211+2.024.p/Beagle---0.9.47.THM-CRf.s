%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 253 expanded)
%              Number of leaves         :   28 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 ( 237 expanded)
%              Number of equality atoms :   48 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_426,plain,(
    ! [D_81,B_82,C_83,A_84] : k2_enumset1(D_81,B_82,C_83,A_84) = k2_enumset1(A_84,B_82,C_83,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_537,plain,(
    ! [D_85,B_86,C_87] : k2_enumset1(D_85,B_86,C_87,B_86) = k1_enumset1(B_86,C_87,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_24])).

tff(c_14,plain,(
    ! [D_22,C_21,B_20,A_19] : k2_enumset1(D_22,C_21,B_20,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_560,plain,(
    ! [B_86,C_87,D_85] : k2_enumset1(B_86,C_87,B_86,D_85) = k1_enumset1(B_86,C_87,D_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_14])).

tff(c_8,plain,(
    ! [A_7,D_10,C_9,B_8] : k2_enumset1(A_7,D_10,C_9,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1563,plain,(
    ! [F_124,E_125,A_126,D_129,C_127,B_128] : k2_xboole_0(k2_enumset1(A_126,B_128,C_127,D_129),k2_tarski(E_125,F_124)) = k4_enumset1(A_126,B_128,C_127,D_129,E_125,F_124) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1620,plain,(
    ! [C_39,B_38,F_124,A_37,E_125] : k4_enumset1(A_37,A_37,B_38,C_39,E_125,F_124) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k2_tarski(E_125,F_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1563])).

tff(c_8825,plain,(
    ! [B_222,C_225,A_221,E_224,F_223] : k2_xboole_0(k1_enumset1(A_221,B_222,C_225),k2_tarski(E_224,F_223)) = k3_enumset1(A_221,B_222,C_225,E_224,F_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1620])).

tff(c_8849,plain,(
    ! [A_35,B_36,E_224,F_223] : k3_enumset1(A_35,A_35,B_36,E_224,F_223) = k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(E_224,F_223)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8825])).

tff(c_8855,plain,(
    ! [A_35,B_36,E_224,F_223] : k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(E_224,F_223)) = k2_enumset1(A_35,B_36,E_224,F_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8849])).

tff(c_143,plain,(
    ! [D_63,C_64,B_65,A_66] : k2_enumset1(D_63,C_64,B_65,A_66) = k2_enumset1(A_66,B_65,C_64,D_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [D_63,C_64,B_65] : k2_enumset1(D_63,C_64,B_65,B_65) = k1_enumset1(B_65,C_64,D_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_1499,plain,(
    ! [D_122,B_121,A_123,C_119,E_120] : k2_xboole_0(k2_enumset1(A_123,B_121,C_119,D_122),k1_tarski(E_120)) = k3_enumset1(A_123,B_121,C_119,D_122,E_120) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1556,plain,(
    ! [A_37,B_38,C_39,E_120] : k3_enumset1(A_37,A_37,B_38,C_39,E_120) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1499])).

tff(c_1559,plain,(
    ! [A_37,B_38,C_39,E_120] : k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_120)) = k2_enumset1(A_37,B_38,C_39,E_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1556])).

tff(c_20,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8852,plain,(
    ! [A_221,B_222,C_225,A_34] : k3_enumset1(A_221,B_222,C_225,A_34,A_34) = k2_xboole_0(k1_enumset1(A_221,B_222,C_225),k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8825])).

tff(c_9781,plain,(
    ! [A_261,B_262,C_263,A_264] : k3_enumset1(A_261,B_262,C_263,A_264,A_264) = k2_enumset1(A_261,B_262,C_263,A_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_8852])).

tff(c_9788,plain,(
    ! [B_262,C_263,A_264] : k2_enumset1(B_262,C_263,A_264,A_264) = k2_enumset1(B_262,B_262,C_263,A_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_9781,c_26])).

tff(c_9800,plain,(
    ! [B_265,C_266,A_267] : k1_enumset1(B_265,C_266,A_267) = k1_enumset1(A_267,C_266,B_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_24,c_9788])).

tff(c_190,plain,(
    ! [D_67,C_68,B_69] : k2_enumset1(D_67,C_68,B_69,B_69) = k1_enumset1(B_69,C_68,D_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_203,plain,(
    ! [C_68,B_69] : k1_enumset1(C_68,B_69,B_69) = k1_enumset1(B_69,C_68,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_24])).

tff(c_9840,plain,(
    ! [B_265,A_267] : k1_enumset1(B_265,B_265,A_267) = k1_enumset1(B_265,A_267,A_267) ),
    inference(superposition,[status(thm),theory(equality)],[c_9800,c_203])).

tff(c_9907,plain,(
    ! [B_265,A_267] : k1_enumset1(B_265,A_267,A_267) = k2_tarski(B_265,A_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9840])).

tff(c_9919,plain,(
    ! [C_68,B_69] : k2_tarski(C_68,B_69) = k2_tarski(B_69,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9907,c_9907,c_203])).

tff(c_610,plain,(
    ! [B_88,D_89,C_90,A_91] : k2_enumset1(B_88,D_89,C_90,A_91) = k2_enumset1(A_91,B_88,C_90,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1018,plain,(
    ! [B_102,D_103,C_104] : k2_enumset1(B_102,D_103,B_102,C_104) = k1_enumset1(B_102,C_104,D_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_610])).

tff(c_1028,plain,(
    ! [B_102,D_103,C_104] : k1_enumset1(B_102,D_103,C_104) = k1_enumset1(B_102,C_104,D_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_560])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1145,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_30])).

tff(c_9970,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9919,c_9919,c_1145])).

tff(c_22014,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8855,c_9970])).

tff(c_22017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_8,c_22014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.93/4.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/4.69  
% 11.93/4.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/4.70  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.93/4.70  
% 11.93/4.70  %Foreground sorts:
% 11.93/4.70  
% 11.93/4.70  
% 11.93/4.70  %Background operators:
% 11.93/4.70  
% 11.93/4.70  
% 11.93/4.70  %Foreground operators:
% 11.93/4.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.93/4.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.93/4.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.93/4.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.93/4.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.93/4.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.93/4.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.93/4.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.93/4.70  tff('#skF_2', type, '#skF_2': $i).
% 11.93/4.70  tff('#skF_3', type, '#skF_3': $i).
% 11.93/4.70  tff('#skF_1', type, '#skF_1': $i).
% 11.93/4.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.93/4.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.93/4.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.93/4.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.93/4.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.93/4.70  
% 11.93/4.71  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 11.93/4.71  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 11.93/4.71  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 11.93/4.71  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 11.93/4.71  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 11.93/4.71  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.93/4.71  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 11.93/4.71  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 11.93/4.71  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 11.93/4.71  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.93/4.71  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 11.93/4.71  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 11.93/4.71  tff(c_426, plain, (![D_81, B_82, C_83, A_84]: (k2_enumset1(D_81, B_82, C_83, A_84)=k2_enumset1(A_84, B_82, C_83, D_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.93/4.71  tff(c_24, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.93/4.71  tff(c_537, plain, (![D_85, B_86, C_87]: (k2_enumset1(D_85, B_86, C_87, B_86)=k1_enumset1(B_86, C_87, D_85))), inference(superposition, [status(thm), theory('equality')], [c_426, c_24])).
% 11.93/4.71  tff(c_14, plain, (![D_22, C_21, B_20, A_19]: (k2_enumset1(D_22, C_21, B_20, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.93/4.71  tff(c_560, plain, (![B_86, C_87, D_85]: (k2_enumset1(B_86, C_87, B_86, D_85)=k1_enumset1(B_86, C_87, D_85))), inference(superposition, [status(thm), theory('equality')], [c_537, c_14])).
% 11.93/4.71  tff(c_8, plain, (![A_7, D_10, C_9, B_8]: (k2_enumset1(A_7, D_10, C_9, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.93/4.71  tff(c_26, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.93/4.71  tff(c_22, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.93/4.71  tff(c_28, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.93/4.71  tff(c_1563, plain, (![F_124, E_125, A_126, D_129, C_127, B_128]: (k2_xboole_0(k2_enumset1(A_126, B_128, C_127, D_129), k2_tarski(E_125, F_124))=k4_enumset1(A_126, B_128, C_127, D_129, E_125, F_124))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.93/4.71  tff(c_1620, plain, (![C_39, B_38, F_124, A_37, E_125]: (k4_enumset1(A_37, A_37, B_38, C_39, E_125, F_124)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k2_tarski(E_125, F_124)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1563])).
% 11.93/4.71  tff(c_8825, plain, (![B_222, C_225, A_221, E_224, F_223]: (k2_xboole_0(k1_enumset1(A_221, B_222, C_225), k2_tarski(E_224, F_223))=k3_enumset1(A_221, B_222, C_225, E_224, F_223))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1620])).
% 11.93/4.71  tff(c_8849, plain, (![A_35, B_36, E_224, F_223]: (k3_enumset1(A_35, A_35, B_36, E_224, F_223)=k2_xboole_0(k2_tarski(A_35, B_36), k2_tarski(E_224, F_223)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8825])).
% 11.93/4.71  tff(c_8855, plain, (![A_35, B_36, E_224, F_223]: (k2_xboole_0(k2_tarski(A_35, B_36), k2_tarski(E_224, F_223))=k2_enumset1(A_35, B_36, E_224, F_223))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8849])).
% 11.93/4.71  tff(c_143, plain, (![D_63, C_64, B_65, A_66]: (k2_enumset1(D_63, C_64, B_65, A_66)=k2_enumset1(A_66, B_65, C_64, D_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.93/4.71  tff(c_159, plain, (![D_63, C_64, B_65]: (k2_enumset1(D_63, C_64, B_65, B_65)=k1_enumset1(B_65, C_64, D_63))), inference(superposition, [status(thm), theory('equality')], [c_143, c_24])).
% 11.93/4.71  tff(c_1499, plain, (![D_122, B_121, A_123, C_119, E_120]: (k2_xboole_0(k2_enumset1(A_123, B_121, C_119, D_122), k1_tarski(E_120))=k3_enumset1(A_123, B_121, C_119, D_122, E_120))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.93/4.71  tff(c_1556, plain, (![A_37, B_38, C_39, E_120]: (k3_enumset1(A_37, A_37, B_38, C_39, E_120)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_120)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1499])).
% 11.93/4.71  tff(c_1559, plain, (![A_37, B_38, C_39, E_120]: (k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_120))=k2_enumset1(A_37, B_38, C_39, E_120))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1556])).
% 11.93/4.71  tff(c_20, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.93/4.71  tff(c_8852, plain, (![A_221, B_222, C_225, A_34]: (k3_enumset1(A_221, B_222, C_225, A_34, A_34)=k2_xboole_0(k1_enumset1(A_221, B_222, C_225), k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_8825])).
% 11.93/4.71  tff(c_9781, plain, (![A_261, B_262, C_263, A_264]: (k3_enumset1(A_261, B_262, C_263, A_264, A_264)=k2_enumset1(A_261, B_262, C_263, A_264))), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_8852])).
% 11.93/4.71  tff(c_9788, plain, (![B_262, C_263, A_264]: (k2_enumset1(B_262, C_263, A_264, A_264)=k2_enumset1(B_262, B_262, C_263, A_264))), inference(superposition, [status(thm), theory('equality')], [c_9781, c_26])).
% 11.93/4.71  tff(c_9800, plain, (![B_265, C_266, A_267]: (k1_enumset1(B_265, C_266, A_267)=k1_enumset1(A_267, C_266, B_265))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_24, c_9788])).
% 11.93/4.71  tff(c_190, plain, (![D_67, C_68, B_69]: (k2_enumset1(D_67, C_68, B_69, B_69)=k1_enumset1(B_69, C_68, D_67))), inference(superposition, [status(thm), theory('equality')], [c_143, c_24])).
% 11.93/4.71  tff(c_203, plain, (![C_68, B_69]: (k1_enumset1(C_68, B_69, B_69)=k1_enumset1(B_69, C_68, C_68))), inference(superposition, [status(thm), theory('equality')], [c_190, c_24])).
% 11.93/4.71  tff(c_9840, plain, (![B_265, A_267]: (k1_enumset1(B_265, B_265, A_267)=k1_enumset1(B_265, A_267, A_267))), inference(superposition, [status(thm), theory('equality')], [c_9800, c_203])).
% 11.93/4.71  tff(c_9907, plain, (![B_265, A_267]: (k1_enumset1(B_265, A_267, A_267)=k2_tarski(B_265, A_267))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_9840])).
% 11.93/4.71  tff(c_9919, plain, (![C_68, B_69]: (k2_tarski(C_68, B_69)=k2_tarski(B_69, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_9907, c_9907, c_203])).
% 11.93/4.71  tff(c_610, plain, (![B_88, D_89, C_90, A_91]: (k2_enumset1(B_88, D_89, C_90, A_91)=k2_enumset1(A_91, B_88, C_90, D_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.93/4.71  tff(c_1018, plain, (![B_102, D_103, C_104]: (k2_enumset1(B_102, D_103, B_102, C_104)=k1_enumset1(B_102, C_104, D_103))), inference(superposition, [status(thm), theory('equality')], [c_159, c_610])).
% 11.93/4.71  tff(c_1028, plain, (![B_102, D_103, C_104]: (k1_enumset1(B_102, D_103, C_104)=k1_enumset1(B_102, C_104, D_103))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_560])).
% 11.93/4.71  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.93/4.71  tff(c_1145, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_30])).
% 11.93/4.71  tff(c_9970, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9919, c_9919, c_1145])).
% 11.93/4.71  tff(c_22014, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8855, c_9970])).
% 11.93/4.71  tff(c_22017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_8, c_22014])).
% 11.93/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.93/4.71  
% 11.93/4.71  Inference rules
% 11.93/4.71  ----------------------
% 11.93/4.71  #Ref     : 0
% 11.93/4.71  #Sup     : 5433
% 11.93/4.71  #Fact    : 0
% 11.93/4.71  #Define  : 0
% 11.93/4.71  #Split   : 0
% 11.93/4.71  #Chain   : 0
% 11.93/4.71  #Close   : 0
% 11.93/4.71  
% 11.93/4.71  Ordering : KBO
% 11.93/4.71  
% 11.93/4.71  Simplification rules
% 11.93/4.71  ----------------------
% 11.93/4.71  #Subsume      : 1966
% 11.93/4.71  #Demod        : 4345
% 11.93/4.71  #Tautology    : 2586
% 11.93/4.71  #SimpNegUnit  : 0
% 11.93/4.71  #BackRed      : 4
% 11.93/4.71  
% 11.93/4.71  #Partial instantiations: 0
% 11.93/4.71  #Strategies tried      : 1
% 11.93/4.71  
% 11.93/4.71  Timing (in seconds)
% 11.93/4.71  ----------------------
% 11.93/4.71  Preprocessing        : 0.29
% 11.93/4.71  Parsing              : 0.15
% 11.93/4.71  CNF conversion       : 0.02
% 11.93/4.71  Main loop            : 3.64
% 11.93/4.71  Inferencing          : 0.73
% 11.93/4.71  Reduction            : 2.37
% 11.93/4.71  Demodulation         : 2.24
% 11.93/4.71  BG Simplification    : 0.07
% 11.93/4.71  Subsumption          : 0.36
% 11.93/4.71  Abstraction          : 0.14
% 11.93/4.71  MUC search           : 0.00
% 11.93/4.71  Cooper               : 0.00
% 11.93/4.71  Total                : 3.96
% 11.93/4.72  Index Insertion      : 0.00
% 11.93/4.72  Index Deletion       : 0.00
% 11.93/4.72  Index Matching       : 0.00
% 11.93/4.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 8.96s
% Output     : CNFRefutation 8.96s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 235 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :   45 ( 218 expanded)
%              Number of equality atoms :   44 ( 217 expanded)
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

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_14,plain,(
    ! [D_22,C_21,B_20,A_19] : k2_enumset1(D_22,C_21,B_20,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [B_79,D_80,C_81,A_82] : k2_enumset1(B_79,D_80,C_81,A_82) = k2_enumset1(A_82,B_79,C_81,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_535,plain,(
    ! [B_90,D_91,C_92] : k2_enumset1(B_90,D_91,C_92,B_90) = k1_enumset1(B_90,C_92,D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_26])).

tff(c_919,plain,(
    ! [D_106,C_107,B_108] : k2_enumset1(D_106,C_107,B_108,D_106) = k1_enumset1(D_106,C_107,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_535])).

tff(c_298,plain,(
    ! [B_79,D_80,C_81] : k2_enumset1(B_79,D_80,C_81,B_79) = k1_enumset1(B_79,C_81,D_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_26])).

tff(c_935,plain,(
    ! [D_106,C_107,B_108] : k1_enumset1(D_106,C_107,B_108) = k1_enumset1(D_106,B_108,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_298])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8,D_10] : k2_enumset1(A_7,C_9,B_8,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,D_54,E_55) = k3_enumset1(A_51,B_52,C_53,D_54,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1691,plain,(
    ! [B_137,A_138,C_134,E_136,D_135,F_133] : k2_xboole_0(k2_enumset1(A_138,B_137,C_134,D_135),k2_tarski(E_136,F_133)) = k4_enumset1(A_138,B_137,C_134,D_135,E_136,F_133) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1751,plain,(
    ! [C_46,A_44,E_136,B_45,F_133] : k4_enumset1(A_44,A_44,B_45,C_46,E_136,F_133) = k2_xboole_0(k1_enumset1(A_44,B_45,C_46),k2_tarski(E_136,F_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1691])).

tff(c_5574,plain,(
    ! [F_190,A_194,C_191,B_193,E_192] : k2_xboole_0(k1_enumset1(A_194,B_193,C_191),k2_tarski(E_192,F_190)) = k3_enumset1(A_194,B_193,C_191,E_192,F_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1751])).

tff(c_5598,plain,(
    ! [A_42,B_43,E_192,F_190] : k3_enumset1(A_42,A_42,B_43,E_192,F_190) = k2_xboole_0(k2_tarski(A_42,B_43),k2_tarski(E_192,F_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5574])).

tff(c_5604,plain,(
    ! [A_42,B_43,E_192,F_190] : k2_xboole_0(k2_tarski(A_42,B_43),k2_tarski(E_192,F_190)) = k2_enumset1(A_42,B_43,E_192,F_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5598])).

tff(c_145,plain,(
    ! [D_70,C_71,B_72,A_73] : k2_enumset1(D_70,C_71,B_72,A_73) = k2_enumset1(A_73,B_72,C_71,D_70) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    ! [D_70,C_71,B_72] : k2_enumset1(D_70,C_71,B_72,B_72) = k1_enumset1(B_72,C_71,D_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(D_26)) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5601,plain,(
    ! [A_194,B_193,C_191,A_41] : k3_enumset1(A_194,B_193,C_191,A_41,A_41) = k2_xboole_0(k1_enumset1(A_194,B_193,C_191),k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5574])).

tff(c_8975,plain,(
    ! [A_260,B_261,C_262,A_263] : k3_enumset1(A_260,B_261,C_262,A_263,A_263) = k2_enumset1(A_260,B_261,C_262,A_263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5601])).

tff(c_8985,plain,(
    ! [B_261,C_262,A_263] : k2_enumset1(B_261,C_262,A_263,A_263) = k2_enumset1(B_261,B_261,C_262,A_263) ),
    inference(superposition,[status(thm),theory(equality)],[c_8975,c_28])).

tff(c_8998,plain,(
    ! [B_264,C_265,A_266] : k1_enumset1(B_264,C_265,A_266) = k1_enumset1(A_266,C_265,B_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_26,c_8985])).

tff(c_192,plain,(
    ! [D_74,C_75,B_76] : k2_enumset1(D_74,C_75,B_76,B_76) = k1_enumset1(B_76,C_75,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_205,plain,(
    ! [C_75,B_76] : k1_enumset1(C_75,B_76,B_76) = k1_enumset1(B_76,C_75,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_26])).

tff(c_9038,plain,(
    ! [B_264,A_266] : k1_enumset1(B_264,B_264,A_266) = k1_enumset1(B_264,A_266,A_266) ),
    inference(superposition,[status(thm),theory(equality)],[c_8998,c_205])).

tff(c_9105,plain,(
    ! [B_264,A_266] : k1_enumset1(B_264,A_266,A_266) = k2_tarski(B_264,A_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9038])).

tff(c_9117,plain,(
    ! [C_75,B_76] : k2_tarski(C_75,B_76) = k2_tarski(B_76,C_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9105,c_9105,c_205])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1038,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_32])).

tff(c_9168,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9117,c_1038])).

tff(c_11331,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5604,c_9168])).

tff(c_11334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_26,c_8,c_11331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.96/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.09  
% 8.96/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.09  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 8.96/3.09  
% 8.96/3.09  %Foreground sorts:
% 8.96/3.09  
% 8.96/3.09  
% 8.96/3.09  %Background operators:
% 8.96/3.09  
% 8.96/3.09  
% 8.96/3.09  %Foreground operators:
% 8.96/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.96/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.96/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.96/3.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.96/3.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.96/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.96/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.96/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.96/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.96/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.96/3.09  tff('#skF_1', type, '#skF_1': $i).
% 8.96/3.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.96/3.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.96/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.96/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.96/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.96/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.96/3.09  
% 8.96/3.11  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 8.96/3.11  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 8.96/3.11  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 8.96/3.11  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 8.96/3.11  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 8.96/3.11  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.96/3.11  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 8.96/3.11  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 8.96/3.11  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 8.96/3.11  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.96/3.11  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 8.96/3.11  tff(c_14, plain, (![D_22, C_21, B_20, A_19]: (k2_enumset1(D_22, C_21, B_20, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.96/3.11  tff(c_262, plain, (![B_79, D_80, C_81, A_82]: (k2_enumset1(B_79, D_80, C_81, A_82)=k2_enumset1(A_82, B_79, C_81, D_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.96/3.11  tff(c_26, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.96/3.11  tff(c_535, plain, (![B_90, D_91, C_92]: (k2_enumset1(B_90, D_91, C_92, B_90)=k1_enumset1(B_90, C_92, D_91))), inference(superposition, [status(thm), theory('equality')], [c_262, c_26])).
% 8.96/3.11  tff(c_919, plain, (![D_106, C_107, B_108]: (k2_enumset1(D_106, C_107, B_108, D_106)=k1_enumset1(D_106, C_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_14, c_535])).
% 8.96/3.11  tff(c_298, plain, (![B_79, D_80, C_81]: (k2_enumset1(B_79, D_80, C_81, B_79)=k1_enumset1(B_79, C_81, D_80))), inference(superposition, [status(thm), theory('equality')], [c_262, c_26])).
% 8.96/3.11  tff(c_935, plain, (![D_106, C_107, B_108]: (k1_enumset1(D_106, C_107, B_108)=k1_enumset1(D_106, B_108, C_107))), inference(superposition, [status(thm), theory('equality')], [c_919, c_298])).
% 8.96/3.11  tff(c_8, plain, (![A_7, C_9, B_8, D_10]: (k2_enumset1(A_7, C_9, B_8, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.96/3.11  tff(c_28, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.96/3.11  tff(c_24, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.96/3.11  tff(c_30, plain, (![B_52, E_55, C_53, D_54, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, D_54, E_55)=k3_enumset1(A_51, B_52, C_53, D_54, E_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.96/3.11  tff(c_1691, plain, (![B_137, A_138, C_134, E_136, D_135, F_133]: (k2_xboole_0(k2_enumset1(A_138, B_137, C_134, D_135), k2_tarski(E_136, F_133))=k4_enumset1(A_138, B_137, C_134, D_135, E_136, F_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.96/3.11  tff(c_1751, plain, (![C_46, A_44, E_136, B_45, F_133]: (k4_enumset1(A_44, A_44, B_45, C_46, E_136, F_133)=k2_xboole_0(k1_enumset1(A_44, B_45, C_46), k2_tarski(E_136, F_133)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1691])).
% 8.96/3.11  tff(c_5574, plain, (![F_190, A_194, C_191, B_193, E_192]: (k2_xboole_0(k1_enumset1(A_194, B_193, C_191), k2_tarski(E_192, F_190))=k3_enumset1(A_194, B_193, C_191, E_192, F_190))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1751])).
% 8.96/3.11  tff(c_5598, plain, (![A_42, B_43, E_192, F_190]: (k3_enumset1(A_42, A_42, B_43, E_192, F_190)=k2_xboole_0(k2_tarski(A_42, B_43), k2_tarski(E_192, F_190)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5574])).
% 8.96/3.11  tff(c_5604, plain, (![A_42, B_43, E_192, F_190]: (k2_xboole_0(k2_tarski(A_42, B_43), k2_tarski(E_192, F_190))=k2_enumset1(A_42, B_43, E_192, F_190))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5598])).
% 8.96/3.11  tff(c_145, plain, (![D_70, C_71, B_72, A_73]: (k2_enumset1(D_70, C_71, B_72, A_73)=k2_enumset1(A_73, B_72, C_71, D_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.96/3.11  tff(c_161, plain, (![D_70, C_71, B_72]: (k2_enumset1(D_70, C_71, B_72, B_72)=k1_enumset1(B_72, C_71, D_70))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 8.96/3.11  tff(c_16, plain, (![A_23, B_24, C_25, D_26]: (k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(D_26))=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.96/3.11  tff(c_22, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.96/3.11  tff(c_5601, plain, (![A_194, B_193, C_191, A_41]: (k3_enumset1(A_194, B_193, C_191, A_41, A_41)=k2_xboole_0(k1_enumset1(A_194, B_193, C_191), k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5574])).
% 8.96/3.11  tff(c_8975, plain, (![A_260, B_261, C_262, A_263]: (k3_enumset1(A_260, B_261, C_262, A_263, A_263)=k2_enumset1(A_260, B_261, C_262, A_263))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5601])).
% 8.96/3.11  tff(c_8985, plain, (![B_261, C_262, A_263]: (k2_enumset1(B_261, C_262, A_263, A_263)=k2_enumset1(B_261, B_261, C_262, A_263))), inference(superposition, [status(thm), theory('equality')], [c_8975, c_28])).
% 8.96/3.11  tff(c_8998, plain, (![B_264, C_265, A_266]: (k1_enumset1(B_264, C_265, A_266)=k1_enumset1(A_266, C_265, B_264))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_26, c_8985])).
% 8.96/3.11  tff(c_192, plain, (![D_74, C_75, B_76]: (k2_enumset1(D_74, C_75, B_76, B_76)=k1_enumset1(B_76, C_75, D_74))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 8.96/3.11  tff(c_205, plain, (![C_75, B_76]: (k1_enumset1(C_75, B_76, B_76)=k1_enumset1(B_76, C_75, C_75))), inference(superposition, [status(thm), theory('equality')], [c_192, c_26])).
% 8.96/3.11  tff(c_9038, plain, (![B_264, A_266]: (k1_enumset1(B_264, B_264, A_266)=k1_enumset1(B_264, A_266, A_266))), inference(superposition, [status(thm), theory('equality')], [c_8998, c_205])).
% 8.96/3.11  tff(c_9105, plain, (![B_264, A_266]: (k1_enumset1(B_264, A_266, A_266)=k2_tarski(B_264, A_266))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_9038])).
% 8.96/3.11  tff(c_9117, plain, (![C_75, B_76]: (k2_tarski(C_75, B_76)=k2_tarski(B_76, C_75))), inference(demodulation, [status(thm), theory('equality')], [c_9105, c_9105, c_205])).
% 8.96/3.11  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.96/3.11  tff(c_1038, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_935, c_32])).
% 8.96/3.11  tff(c_9168, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9117, c_1038])).
% 8.96/3.11  tff(c_11331, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5604, c_9168])).
% 8.96/3.11  tff(c_11334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_935, c_26, c_8, c_11331])).
% 8.96/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.11  
% 8.96/3.11  Inference rules
% 8.96/3.11  ----------------------
% 8.96/3.11  #Ref     : 0
% 8.96/3.11  #Sup     : 3000
% 8.96/3.11  #Fact    : 0
% 8.96/3.11  #Define  : 0
% 8.96/3.11  #Split   : 0
% 8.96/3.11  #Chain   : 0
% 8.96/3.11  #Close   : 0
% 8.96/3.11  
% 8.96/3.11  Ordering : KBO
% 8.96/3.11  
% 8.96/3.11  Simplification rules
% 8.96/3.11  ----------------------
% 8.96/3.11  #Subsume      : 996
% 8.96/3.11  #Demod        : 1413
% 8.96/3.11  #Tautology    : 1335
% 8.96/3.11  #SimpNegUnit  : 0
% 8.96/3.11  #BackRed      : 4
% 8.96/3.11  
% 8.96/3.11  #Partial instantiations: 0
% 8.96/3.11  #Strategies tried      : 1
% 8.96/3.11  
% 8.96/3.11  Timing (in seconds)
% 8.96/3.11  ----------------------
% 8.96/3.11  Preprocessing        : 0.30
% 8.96/3.11  Parsing              : 0.16
% 8.96/3.11  CNF conversion       : 0.02
% 8.96/3.11  Main loop            : 2.04
% 8.96/3.11  Inferencing          : 0.49
% 8.96/3.11  Reduction            : 1.21
% 8.96/3.11  Demodulation         : 1.12
% 8.96/3.11  BG Simplification    : 0.06
% 8.96/3.11  Subsumption          : 0.21
% 8.96/3.11  Abstraction          : 0.09
% 8.96/3.11  MUC search           : 0.00
% 8.96/3.11  Cooper               : 0.00
% 8.96/3.11  Total                : 2.37
% 8.96/3.11  Index Insertion      : 0.00
% 8.96/3.11  Index Deletion       : 0.00
% 8.96/3.11  Index Matching       : 0.00
% 8.96/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

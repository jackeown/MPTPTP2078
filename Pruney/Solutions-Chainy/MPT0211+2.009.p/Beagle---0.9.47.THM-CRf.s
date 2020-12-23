%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 163 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 150 expanded)
%              Number of equality atoms :   52 ( 149 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_xboole_0(k2_tarski(A_39,B_40),k2_tarski(C_41,D_42)) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_202,plain,(
    ! [A_15,C_41,D_42] : k2_xboole_0(k1_tarski(A_15),k2_tarski(C_41,D_42)) = k2_enumset1(A_15,A_15,C_41,D_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_178])).

tff(c_752,plain,(
    ! [A_64,C_65,D_66] : k2_xboole_0(k1_tarski(A_64),k2_tarski(C_65,D_66)) = k1_enumset1(A_64,C_65,D_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_202])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k2_tarski(A_34,B_35),k1_tarski(C_36)) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144,plain,(
    ! [C_36,A_34,B_35] : k2_xboole_0(k1_tarski(C_36),k2_tarski(A_34,B_35)) = k1_enumset1(A_34,B_35,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_804,plain,(
    ! [C_67,D_68,A_69] : k1_enumset1(C_67,D_68,A_69) = k1_enumset1(A_69,C_67,D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_144])).

tff(c_14,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_828,plain,(
    ! [C_67,D_68] : k1_enumset1(C_67,D_68,C_67) = k2_tarski(C_67,D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_14])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k2_tarski(A_8,B_9),k2_tarski(C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_15,C_36] : k2_xboole_0(k1_tarski(A_15),k1_tarski(C_36)) = k1_enumset1(A_15,A_15,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_153,plain,(
    ! [A_15,C_36] : k2_xboole_0(k1_tarski(A_15),k1_tarski(C_36)) = k2_tarski(A_15,C_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2043,plain,(
    ! [A_101,B_102,C_103,C_104] : k2_xboole_0(k2_tarski(A_101,B_102),k2_xboole_0(k1_tarski(C_103),C_104)) = k2_xboole_0(k1_enumset1(A_101,B_102,C_103),C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_4])).

tff(c_2166,plain,(
    ! [A_101,B_102,A_15,C_36] : k2_xboole_0(k1_enumset1(A_101,B_102,A_15),k1_tarski(C_36)) = k2_xboole_0(k2_tarski(A_101,B_102),k2_tarski(A_15,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2043])).

tff(c_6901,plain,(
    ! [A_165,B_166,A_167,C_168] : k2_xboole_0(k1_enumset1(A_165,B_166,A_167),k1_tarski(C_168)) = k2_enumset1(A_165,B_166,A_167,C_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2166])).

tff(c_6982,plain,(
    ! [C_67,D_68,C_168] : k2_xboole_0(k2_tarski(C_67,D_68),k1_tarski(C_168)) = k2_enumset1(C_67,D_68,C_67,C_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_6901])).

tff(c_7010,plain,(
    ! [C_67,D_68,C_168] : k2_enumset1(C_67,D_68,C_67,C_168) = k1_enumset1(C_67,D_68,C_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6982])).

tff(c_89,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k2_xboole_0(A_31,B_32),C_33) = k2_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_337,plain,(
    ! [B_52,A_53,C_54] : k2_xboole_0(k2_xboole_0(B_52,A_53),C_54) = k2_xboole_0(A_53,k2_xboole_0(B_52,C_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_352,plain,(
    ! [C_54,B_52,A_53] : k2_xboole_0(C_54,k2_xboole_0(B_52,A_53)) = k2_xboole_0(A_53,k2_xboole_0(B_52,C_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_2])).

tff(c_402,plain,(
    ! [A_57,A_55,B_56] : k2_xboole_0(A_57,k2_xboole_0(A_55,B_56)) = k2_xboole_0(A_55,k2_xboole_0(B_56,A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_3762,plain,(
    ! [A_128,C_129,A_130] : k2_xboole_0(k1_tarski(A_128),k2_xboole_0(k1_tarski(C_129),A_130)) = k2_xboole_0(A_130,k2_tarski(A_128,C_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_402])).

tff(c_3887,plain,(
    ! [A_53,C_129,A_128] : k2_xboole_0(A_53,k2_xboole_0(k1_tarski(C_129),k1_tarski(A_128))) = k2_xboole_0(A_53,k2_tarski(A_128,C_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_3762])).

tff(c_3964,plain,(
    ! [A_53,C_129,A_128] : k2_xboole_0(A_53,k2_tarski(C_129,A_128)) = k2_xboole_0(A_53,k2_tarski(A_128,C_129)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_3887])).

tff(c_370,plain,(
    ! [C_36,A_15,C_54] : k2_xboole_0(k1_tarski(C_36),k2_xboole_0(k1_tarski(A_15),C_54)) = k2_xboole_0(k2_tarski(A_15,C_36),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_337])).

tff(c_154,plain,(
    ! [A_37,C_38] : k2_xboole_0(k1_tarski(A_37),k1_tarski(C_38)) = k2_tarski(A_37,C_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_4284,plain,(
    ! [A_134,C_135,C_136] : k2_xboole_0(k1_tarski(A_134),k2_xboole_0(k1_tarski(C_135),C_136)) = k2_xboole_0(k2_tarski(A_134,C_135),C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_4997,plain,(
    ! [C_143,A_144,C_145] : k2_xboole_0(k2_tarski(C_143,A_144),C_145) = k2_xboole_0(k2_tarski(A_144,C_143),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_4284])).

tff(c_5297,plain,(
    ! [C_143,A_144,C_129,A_128] : k2_xboole_0(k2_tarski(C_143,A_144),k2_tarski(C_129,A_128)) = k2_xboole_0(k2_tarski(A_144,C_143),k2_tarski(A_128,C_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3964,c_4997])).

tff(c_5451,plain,(
    ! [C_143,A_144,C_129,A_128] : k2_enumset1(C_143,A_144,C_129,A_128) = k2_enumset1(A_144,C_143,A_128,C_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_5297])).

tff(c_3108,plain,(
    ! [C_116,A_117,C_118] : k2_xboole_0(k1_tarski(C_116),k2_xboole_0(k1_tarski(A_117),C_118)) = k2_xboole_0(k2_tarski(A_117,C_116),C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_337])).

tff(c_3265,plain,(
    ! [A_15,C_116,C_36] : k2_xboole_0(k2_tarski(A_15,C_116),k1_tarski(C_36)) = k2_xboole_0(k1_tarski(C_116),k2_tarski(A_15,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_3108])).

tff(c_3301,plain,(
    ! [A_15,C_36,C_116] : k1_enumset1(A_15,C_36,C_116) = k1_enumset1(A_15,C_116,C_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_10,c_3265])).

tff(c_1020,plain,(
    ! [C_76,D_77,A_78,B_79] : k2_xboole_0(k2_tarski(C_76,D_77),k2_tarski(A_78,B_79)) = k2_enumset1(A_78,B_79,C_76,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_1065,plain,(
    ! [C_10,D_11,A_8,B_9] : k2_enumset1(C_10,D_11,A_8,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1020])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_1875,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_19])).

tff(c_3302,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_1875])).

tff(c_6714,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_3302])).

tff(c_7197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7010,c_6714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.78/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.90  
% 7.96/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.90  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.96/2.90  
% 7.96/2.90  %Foreground sorts:
% 7.96/2.90  
% 7.96/2.90  
% 7.96/2.90  %Background operators:
% 7.96/2.90  
% 7.96/2.90  
% 7.96/2.90  %Foreground operators:
% 7.96/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.96/2.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.96/2.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.96/2.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.96/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.96/2.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.96/2.90  tff('#skF_2', type, '#skF_2': $i).
% 7.96/2.90  tff('#skF_3', type, '#skF_3': $i).
% 7.96/2.90  tff('#skF_1', type, '#skF_1': $i).
% 7.96/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.96/2.90  
% 7.96/2.92  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 7.96/2.92  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.96/2.92  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.96/2.92  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 7.96/2.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.96/2.92  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.96/2.92  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.96/2.92  tff(f_44, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 7.96/2.92  tff(c_10, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_12, B_13), k1_tarski(C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.96/2.92  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.96/2.92  tff(c_12, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.96/2.92  tff(c_178, plain, (![A_39, B_40, C_41, D_42]: (k2_xboole_0(k2_tarski(A_39, B_40), k2_tarski(C_41, D_42))=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.96/2.92  tff(c_202, plain, (![A_15, C_41, D_42]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(C_41, D_42))=k2_enumset1(A_15, A_15, C_41, D_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_178])).
% 7.96/2.92  tff(c_752, plain, (![A_64, C_65, D_66]: (k2_xboole_0(k1_tarski(A_64), k2_tarski(C_65, D_66))=k1_enumset1(A_64, C_65, D_66))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_202])).
% 7.96/2.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/2.92  tff(c_126, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k2_tarski(A_34, B_35), k1_tarski(C_36))=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.96/2.92  tff(c_144, plain, (![C_36, A_34, B_35]: (k2_xboole_0(k1_tarski(C_36), k2_tarski(A_34, B_35))=k1_enumset1(A_34, B_35, C_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 7.96/2.92  tff(c_804, plain, (![C_67, D_68, A_69]: (k1_enumset1(C_67, D_68, A_69)=k1_enumset1(A_69, C_67, D_68))), inference(superposition, [status(thm), theory('equality')], [c_752, c_144])).
% 7.96/2.92  tff(c_14, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.96/2.92  tff(c_828, plain, (![C_67, D_68]: (k1_enumset1(C_67, D_68, C_67)=k2_tarski(C_67, D_68))), inference(superposition, [status(thm), theory('equality')], [c_804, c_14])).
% 7.96/2.92  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k2_tarski(A_8, B_9), k2_tarski(C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.96/2.92  tff(c_150, plain, (![A_15, C_36]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(C_36))=k1_enumset1(A_15, A_15, C_36))), inference(superposition, [status(thm), theory('equality')], [c_12, c_126])).
% 7.96/2.92  tff(c_153, plain, (![A_15, C_36]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(C_36))=k2_tarski(A_15, C_36))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 7.96/2.92  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.96/2.92  tff(c_2043, plain, (![A_101, B_102, C_103, C_104]: (k2_xboole_0(k2_tarski(A_101, B_102), k2_xboole_0(k1_tarski(C_103), C_104))=k2_xboole_0(k1_enumset1(A_101, B_102, C_103), C_104))), inference(superposition, [status(thm), theory('equality')], [c_126, c_4])).
% 7.96/2.92  tff(c_2166, plain, (![A_101, B_102, A_15, C_36]: (k2_xboole_0(k1_enumset1(A_101, B_102, A_15), k1_tarski(C_36))=k2_xboole_0(k2_tarski(A_101, B_102), k2_tarski(A_15, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_2043])).
% 7.96/2.92  tff(c_6901, plain, (![A_165, B_166, A_167, C_168]: (k2_xboole_0(k1_enumset1(A_165, B_166, A_167), k1_tarski(C_168))=k2_enumset1(A_165, B_166, A_167, C_168))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2166])).
% 7.96/2.92  tff(c_6982, plain, (![C_67, D_68, C_168]: (k2_xboole_0(k2_tarski(C_67, D_68), k1_tarski(C_168))=k2_enumset1(C_67, D_68, C_67, C_168))), inference(superposition, [status(thm), theory('equality')], [c_828, c_6901])).
% 7.96/2.92  tff(c_7010, plain, (![C_67, D_68, C_168]: (k2_enumset1(C_67, D_68, C_67, C_168)=k1_enumset1(C_67, D_68, C_168))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6982])).
% 7.96/2.92  tff(c_89, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k2_xboole_0(A_31, B_32), C_33)=k2_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.96/2.92  tff(c_337, plain, (![B_52, A_53, C_54]: (k2_xboole_0(k2_xboole_0(B_52, A_53), C_54)=k2_xboole_0(A_53, k2_xboole_0(B_52, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 7.96/2.92  tff(c_352, plain, (![C_54, B_52, A_53]: (k2_xboole_0(C_54, k2_xboole_0(B_52, A_53))=k2_xboole_0(A_53, k2_xboole_0(B_52, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_2])).
% 7.96/2.92  tff(c_402, plain, (![A_57, A_55, B_56]: (k2_xboole_0(A_57, k2_xboole_0(A_55, B_56))=k2_xboole_0(A_55, k2_xboole_0(B_56, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 7.96/2.92  tff(c_3762, plain, (![A_128, C_129, A_130]: (k2_xboole_0(k1_tarski(A_128), k2_xboole_0(k1_tarski(C_129), A_130))=k2_xboole_0(A_130, k2_tarski(A_128, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_402])).
% 7.96/2.92  tff(c_3887, plain, (![A_53, C_129, A_128]: (k2_xboole_0(A_53, k2_xboole_0(k1_tarski(C_129), k1_tarski(A_128)))=k2_xboole_0(A_53, k2_tarski(A_128, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_352, c_3762])).
% 7.96/2.92  tff(c_3964, plain, (![A_53, C_129, A_128]: (k2_xboole_0(A_53, k2_tarski(C_129, A_128))=k2_xboole_0(A_53, k2_tarski(A_128, C_129)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_3887])).
% 7.96/2.92  tff(c_370, plain, (![C_36, A_15, C_54]: (k2_xboole_0(k1_tarski(C_36), k2_xboole_0(k1_tarski(A_15), C_54))=k2_xboole_0(k2_tarski(A_15, C_36), C_54))), inference(superposition, [status(thm), theory('equality')], [c_153, c_337])).
% 7.96/2.92  tff(c_154, plain, (![A_37, C_38]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(C_38))=k2_tarski(A_37, C_38))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 7.96/2.92  tff(c_4284, plain, (![A_134, C_135, C_136]: (k2_xboole_0(k1_tarski(A_134), k2_xboole_0(k1_tarski(C_135), C_136))=k2_xboole_0(k2_tarski(A_134, C_135), C_136))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 7.96/2.92  tff(c_4997, plain, (![C_143, A_144, C_145]: (k2_xboole_0(k2_tarski(C_143, A_144), C_145)=k2_xboole_0(k2_tarski(A_144, C_143), C_145))), inference(superposition, [status(thm), theory('equality')], [c_370, c_4284])).
% 7.96/2.92  tff(c_5297, plain, (![C_143, A_144, C_129, A_128]: (k2_xboole_0(k2_tarski(C_143, A_144), k2_tarski(C_129, A_128))=k2_xboole_0(k2_tarski(A_144, C_143), k2_tarski(A_128, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_3964, c_4997])).
% 7.96/2.92  tff(c_5451, plain, (![C_143, A_144, C_129, A_128]: (k2_enumset1(C_143, A_144, C_129, A_128)=k2_enumset1(A_144, C_143, A_128, C_129))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_5297])).
% 7.96/2.92  tff(c_3108, plain, (![C_116, A_117, C_118]: (k2_xboole_0(k1_tarski(C_116), k2_xboole_0(k1_tarski(A_117), C_118))=k2_xboole_0(k2_tarski(A_117, C_116), C_118))), inference(superposition, [status(thm), theory('equality')], [c_153, c_337])).
% 7.96/2.92  tff(c_3265, plain, (![A_15, C_116, C_36]: (k2_xboole_0(k2_tarski(A_15, C_116), k1_tarski(C_36))=k2_xboole_0(k1_tarski(C_116), k2_tarski(A_15, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_3108])).
% 7.96/2.92  tff(c_3301, plain, (![A_15, C_36, C_116]: (k1_enumset1(A_15, C_36, C_116)=k1_enumset1(A_15, C_116, C_36))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_10, c_3265])).
% 7.96/2.92  tff(c_1020, plain, (![C_76, D_77, A_78, B_79]: (k2_xboole_0(k2_tarski(C_76, D_77), k2_tarski(A_78, B_79))=k2_enumset1(A_78, B_79, C_76, D_77))), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 7.96/2.92  tff(c_1065, plain, (![C_10, D_11, A_8, B_9]: (k2_enumset1(C_10, D_11, A_8, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1020])).
% 7.96/2.92  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.96/2.92  tff(c_19, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 7.96/2.92  tff(c_1875, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_19])).
% 7.96/2.92  tff(c_3302, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_1875])).
% 7.96/2.92  tff(c_6714, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_3302])).
% 7.96/2.92  tff(c_7197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7010, c_6714])).
% 7.96/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.92  
% 7.96/2.92  Inference rules
% 7.96/2.92  ----------------------
% 7.96/2.92  #Ref     : 0
% 7.96/2.92  #Sup     : 1902
% 7.96/2.92  #Fact    : 0
% 7.96/2.92  #Define  : 0
% 7.96/2.92  #Split   : 0
% 7.96/2.92  #Chain   : 0
% 7.96/2.92  #Close   : 0
% 7.96/2.92  
% 7.96/2.92  Ordering : KBO
% 7.96/2.92  
% 7.96/2.92  Simplification rules
% 7.96/2.92  ----------------------
% 7.96/2.92  #Subsume      : 304
% 7.96/2.92  #Demod        : 950
% 7.96/2.92  #Tautology    : 465
% 7.96/2.92  #SimpNegUnit  : 0
% 7.96/2.92  #BackRed      : 4
% 7.96/2.92  
% 7.96/2.92  #Partial instantiations: 0
% 7.96/2.92  #Strategies tried      : 1
% 7.96/2.92  
% 7.96/2.92  Timing (in seconds)
% 7.96/2.92  ----------------------
% 7.96/2.92  Preprocessing        : 0.27
% 7.96/2.92  Parsing              : 0.14
% 7.96/2.92  CNF conversion       : 0.01
% 7.96/2.92  Main loop            : 1.87
% 7.96/2.92  Inferencing          : 0.45
% 7.96/2.92  Reduction            : 1.11
% 7.96/2.92  Demodulation         : 1.02
% 7.96/2.92  BG Simplification    : 0.07
% 7.96/2.92  Subsumption          : 0.18
% 7.96/2.92  Abstraction          : 0.10
% 7.96/2.92  MUC search           : 0.00
% 7.96/2.92  Cooper               : 0.00
% 7.96/2.92  Total                : 2.18
% 7.96/2.92  Index Insertion      : 0.00
% 7.96/2.92  Index Deletion       : 0.00
% 7.96/2.92  Index Matching       : 0.00
% 7.96/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------

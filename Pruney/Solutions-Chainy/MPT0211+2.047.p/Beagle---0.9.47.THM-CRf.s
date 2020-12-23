%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 150 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 133 expanded)
%              Number of equality atoms :   50 ( 132 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_30,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_652,plain,(
    ! [C_99,B_100,D_101,A_102] : k2_enumset1(C_99,B_100,D_101,A_102) = k2_enumset1(A_102,B_100,C_99,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1032,plain,(
    ! [C_117,A_118,B_119] : k2_enumset1(C_117,A_118,A_118,B_119) = k1_enumset1(A_118,B_119,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_652])).

tff(c_16,plain,(
    ! [B_22,D_24,C_23,A_21] : k2_enumset1(B_22,D_24,C_23,A_21) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1065,plain,(
    ! [A_118,B_119,C_117] : k2_enumset1(A_118,B_119,A_118,C_117) = k1_enumset1(A_118,B_119,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_16])).

tff(c_32,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_enumset1(A_52,A_52,B_53,C_54,D_55) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1771,plain,(
    ! [E_143,D_144,A_142,C_145,B_141] : k2_xboole_0(k1_enumset1(A_142,B_141,C_145),k2_tarski(D_144,E_143)) = k3_enumset1(A_142,B_141,C_145,D_144,E_143) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1795,plain,(
    ! [A_47,B_48,D_144,E_143] : k3_enumset1(A_47,A_47,B_48,D_144,E_143) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_144,E_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1771])).

tff(c_1801,plain,(
    ! [A_47,B_48,D_144,E_143] : k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_144,E_143)) = k2_enumset1(A_47,B_48,D_144,E_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1795])).

tff(c_26,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1156,plain,(
    ! [A_120,B_121,C_122,D_123] : k2_xboole_0(k1_enumset1(A_120,B_121,C_122),k1_tarski(D_123)) = k2_enumset1(A_120,B_121,C_122,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1180,plain,(
    ! [A_47,B_48,D_123] : k2_xboole_0(k2_tarski(A_47,B_48),k1_tarski(D_123)) = k2_enumset1(A_47,A_47,B_48,D_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1156])).

tff(c_5273,plain,(
    ! [A_195,B_196,D_197] : k2_xboole_0(k2_tarski(A_195,B_196),k1_tarski(D_197)) = k1_enumset1(A_195,B_196,D_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1180])).

tff(c_5294,plain,(
    ! [A_46,D_197] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_197)) = k1_enumset1(A_46,A_46,D_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5273])).

tff(c_5298,plain,(
    ! [A_198,D_199] : k2_xboole_0(k1_tarski(A_198),k1_tarski(D_199)) = k2_tarski(A_198,D_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5294])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_261,plain,(
    ! [A_83,B_84] : k5_xboole_0(k5_xboole_0(A_83,B_84),k3_xboole_0(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3322,plain,(
    ! [B_173,A_174] : k5_xboole_0(k5_xboole_0(B_173,A_174),k3_xboole_0(A_174,B_173)) = k2_xboole_0(A_174,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_261])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3341,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,k5_xboole_0(A_174,k3_xboole_0(A_174,B_173))) = k2_xboole_0(A_174,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_3322,c_6])).

tff(c_3388,plain,(
    ! [B_173,A_174] : k2_xboole_0(B_173,A_174) = k2_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_3341])).

tff(c_5319,plain,(
    ! [D_200,A_201] : k2_xboole_0(k1_tarski(D_200),k1_tarski(A_201)) = k2_tarski(A_201,D_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_5298,c_3388])).

tff(c_5297,plain,(
    ! [A_46,D_197] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_197)) = k2_tarski(A_46,D_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5294])).

tff(c_5325,plain,(
    ! [D_200,A_201] : k2_tarski(D_200,A_201) = k2_tarski(A_201,D_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_5319,c_5297])).

tff(c_873,plain,(
    ! [B_111,A_112,C_113] : k2_enumset1(B_111,A_112,C_113,A_112) = k1_enumset1(A_112,B_111,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_652])).

tff(c_313,plain,(
    ! [B_85,D_86,C_87,A_88] : k2_enumset1(B_85,D_86,C_87,A_88) = k2_enumset1(A_88,B_85,C_87,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_88,D_86,C_87] : k2_enumset1(A_88,D_86,C_87,D_86) = k1_enumset1(D_86,C_87,A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_30])).

tff(c_889,plain,(
    ! [A_112,C_113,B_111] : k1_enumset1(A_112,C_113,B_111) = k1_enumset1(A_112,B_111,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_353])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_962,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_36])).

tff(c_3394,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3388,c_962])).

tff(c_5461,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5325,c_5325,c_3394])).

tff(c_8931,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_5461])).

tff(c_8934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_8931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:01:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/2.65  
% 7.62/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/2.65  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.62/2.65  
% 7.62/2.65  %Foreground sorts:
% 7.62/2.65  
% 7.62/2.65  
% 7.62/2.65  %Background operators:
% 7.62/2.65  
% 7.62/2.65  
% 7.62/2.65  %Foreground operators:
% 7.62/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.62/2.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/2.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/2.65  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/2.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/2.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/2.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/2.65  tff('#skF_2', type, '#skF_2': $i).
% 7.62/2.65  tff('#skF_3', type, '#skF_3': $i).
% 7.62/2.65  tff('#skF_1', type, '#skF_1': $i).
% 7.62/2.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/2.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.62/2.65  
% 7.62/2.67  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.62/2.67  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 7.62/2.67  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 7.62/2.67  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.62/2.67  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.62/2.67  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 7.62/2.67  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.62/2.67  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 7.62/2.67  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.62/2.67  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.62/2.67  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.62/2.67  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.62/2.67  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.62/2.67  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 7.62/2.67  tff(c_30, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.62/2.67  tff(c_652, plain, (![C_99, B_100, D_101, A_102]: (k2_enumset1(C_99, B_100, D_101, A_102)=k2_enumset1(A_102, B_100, C_99, D_101))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.62/2.67  tff(c_1032, plain, (![C_117, A_118, B_119]: (k2_enumset1(C_117, A_118, A_118, B_119)=k1_enumset1(A_118, B_119, C_117))), inference(superposition, [status(thm), theory('equality')], [c_30, c_652])).
% 7.62/2.67  tff(c_16, plain, (![B_22, D_24, C_23, A_21]: (k2_enumset1(B_22, D_24, C_23, A_21)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.62/2.67  tff(c_1065, plain, (![A_118, B_119, C_117]: (k2_enumset1(A_118, B_119, A_118, C_117)=k1_enumset1(A_118, B_119, C_117))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_16])).
% 7.62/2.67  tff(c_32, plain, (![A_52, B_53, C_54, D_55]: (k3_enumset1(A_52, A_52, B_53, C_54, D_55)=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.62/2.67  tff(c_28, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.62/2.67  tff(c_1771, plain, (![E_143, D_144, A_142, C_145, B_141]: (k2_xboole_0(k1_enumset1(A_142, B_141, C_145), k2_tarski(D_144, E_143))=k3_enumset1(A_142, B_141, C_145, D_144, E_143))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.62/2.67  tff(c_1795, plain, (![A_47, B_48, D_144, E_143]: (k3_enumset1(A_47, A_47, B_48, D_144, E_143)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_144, E_143)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1771])).
% 7.62/2.67  tff(c_1801, plain, (![A_47, B_48, D_144, E_143]: (k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_144, E_143))=k2_enumset1(A_47, B_48, D_144, E_143))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1795])).
% 7.62/2.67  tff(c_26, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.62/2.67  tff(c_1156, plain, (![A_120, B_121, C_122, D_123]: (k2_xboole_0(k1_enumset1(A_120, B_121, C_122), k1_tarski(D_123))=k2_enumset1(A_120, B_121, C_122, D_123))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.62/2.67  tff(c_1180, plain, (![A_47, B_48, D_123]: (k2_xboole_0(k2_tarski(A_47, B_48), k1_tarski(D_123))=k2_enumset1(A_47, A_47, B_48, D_123))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1156])).
% 7.62/2.67  tff(c_5273, plain, (![A_195, B_196, D_197]: (k2_xboole_0(k2_tarski(A_195, B_196), k1_tarski(D_197))=k1_enumset1(A_195, B_196, D_197))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1180])).
% 7.62/2.67  tff(c_5294, plain, (![A_46, D_197]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_197))=k1_enumset1(A_46, A_46, D_197))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5273])).
% 7.62/2.67  tff(c_5298, plain, (![A_198, D_199]: (k2_xboole_0(k1_tarski(A_198), k1_tarski(D_199))=k2_tarski(A_198, D_199))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5294])).
% 7.62/2.67  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.62/2.67  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.62/2.67  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.62/2.67  tff(c_261, plain, (![A_83, B_84]: (k5_xboole_0(k5_xboole_0(A_83, B_84), k3_xboole_0(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.62/2.67  tff(c_3322, plain, (![B_173, A_174]: (k5_xboole_0(k5_xboole_0(B_173, A_174), k3_xboole_0(A_174, B_173))=k2_xboole_0(A_174, B_173))), inference(superposition, [status(thm), theory('equality')], [c_2, c_261])).
% 7.62/2.67  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.62/2.67  tff(c_3341, plain, (![B_173, A_174]: (k5_xboole_0(B_173, k5_xboole_0(A_174, k3_xboole_0(A_174, B_173)))=k2_xboole_0(A_174, B_173))), inference(superposition, [status(thm), theory('equality')], [c_3322, c_6])).
% 7.62/2.67  tff(c_3388, plain, (![B_173, A_174]: (k2_xboole_0(B_173, A_174)=k2_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_3341])).
% 7.62/2.67  tff(c_5319, plain, (![D_200, A_201]: (k2_xboole_0(k1_tarski(D_200), k1_tarski(A_201))=k2_tarski(A_201, D_200))), inference(superposition, [status(thm), theory('equality')], [c_5298, c_3388])).
% 7.62/2.67  tff(c_5297, plain, (![A_46, D_197]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_197))=k2_tarski(A_46, D_197))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5294])).
% 7.62/2.67  tff(c_5325, plain, (![D_200, A_201]: (k2_tarski(D_200, A_201)=k2_tarski(A_201, D_200))), inference(superposition, [status(thm), theory('equality')], [c_5319, c_5297])).
% 7.62/2.67  tff(c_873, plain, (![B_111, A_112, C_113]: (k2_enumset1(B_111, A_112, C_113, A_112)=k1_enumset1(A_112, B_111, C_113))), inference(superposition, [status(thm), theory('equality')], [c_30, c_652])).
% 7.62/2.67  tff(c_313, plain, (![B_85, D_86, C_87, A_88]: (k2_enumset1(B_85, D_86, C_87, A_88)=k2_enumset1(A_88, B_85, C_87, D_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.62/2.67  tff(c_353, plain, (![A_88, D_86, C_87]: (k2_enumset1(A_88, D_86, C_87, D_86)=k1_enumset1(D_86, C_87, A_88))), inference(superposition, [status(thm), theory('equality')], [c_313, c_30])).
% 7.62/2.67  tff(c_889, plain, (![A_112, C_113, B_111]: (k1_enumset1(A_112, C_113, B_111)=k1_enumset1(A_112, B_111, C_113))), inference(superposition, [status(thm), theory('equality')], [c_873, c_353])).
% 7.62/2.67  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.62/2.67  tff(c_962, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_36])).
% 7.62/2.67  tff(c_3394, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3388, c_962])).
% 7.62/2.67  tff(c_5461, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5325, c_5325, c_3394])).
% 7.62/2.67  tff(c_8931, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_5461])).
% 7.62/2.67  tff(c_8934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1065, c_8931])).
% 7.62/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/2.67  
% 7.62/2.67  Inference rules
% 7.62/2.67  ----------------------
% 7.62/2.67  #Ref     : 0
% 7.62/2.67  #Sup     : 2348
% 7.62/2.67  #Fact    : 0
% 7.62/2.67  #Define  : 0
% 7.62/2.67  #Split   : 0
% 7.62/2.67  #Chain   : 0
% 7.62/2.67  #Close   : 0
% 7.62/2.67  
% 7.62/2.67  Ordering : KBO
% 7.62/2.67  
% 7.62/2.67  Simplification rules
% 7.62/2.67  ----------------------
% 7.62/2.67  #Subsume      : 722
% 7.62/2.67  #Demod        : 1118
% 7.62/2.67  #Tautology    : 1109
% 7.62/2.67  #SimpNegUnit  : 0
% 7.62/2.67  #BackRed      : 5
% 7.62/2.67  
% 7.62/2.67  #Partial instantiations: 0
% 7.62/2.67  #Strategies tried      : 1
% 7.62/2.67  
% 7.62/2.67  Timing (in seconds)
% 7.62/2.67  ----------------------
% 7.62/2.67  Preprocessing        : 0.34
% 7.62/2.67  Parsing              : 0.18
% 7.62/2.67  CNF conversion       : 0.02
% 7.62/2.67  Main loop            : 1.54
% 7.62/2.67  Inferencing          : 0.42
% 7.62/2.67  Reduction            : 0.86
% 7.62/2.67  Demodulation         : 0.78
% 7.62/2.67  BG Simplification    : 0.05
% 7.62/2.67  Subsumption          : 0.16
% 7.62/2.67  Abstraction          : 0.08
% 7.62/2.67  MUC search           : 0.00
% 7.62/2.67  Cooper               : 0.00
% 7.62/2.67  Total                : 1.91
% 7.62/2.67  Index Insertion      : 0.00
% 7.62/2.67  Index Deletion       : 0.00
% 7.62/2.67  Index Matching       : 0.00
% 7.62/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

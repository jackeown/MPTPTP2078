%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 162 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 144 expanded)
%              Number of equality atoms :   50 ( 143 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_517,plain,(
    ! [D_100,C_101,B_102,A_103] : k2_enumset1(D_100,C_101,B_102,A_103) = k2_enumset1(A_103,B_102,C_101,D_100) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_864,plain,(
    ! [A_113,B_114,C_115] : k2_enumset1(A_113,B_114,C_115,C_115) = k1_enumset1(C_115,B_114,A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_30])).

tff(c_398,plain,(
    ! [C_96,D_97,B_98,A_99] : k2_enumset1(C_96,D_97,B_98,A_99) = k2_enumset1(A_99,B_98,C_96,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_454,plain,(
    ! [C_96,D_97,B_98] : k2_enumset1(C_96,D_97,B_98,B_98) = k1_enumset1(B_98,C_96,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_30])).

tff(c_870,plain,(
    ! [C_115,B_114,A_113] : k1_enumset1(C_115,B_114,A_113) = k1_enumset1(C_115,A_113,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_454])).

tff(c_16,plain,(
    ! [B_22,D_24,C_23,A_21] : k2_enumset1(B_22,D_24,C_23,A_21) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_940,plain,(
    ! [A_21,B_22,D_24] : k2_enumset1(A_21,B_22,A_21,D_24) = k1_enumset1(A_21,D_24,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_864])).

tff(c_32,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_enumset1(A_52,A_52,B_53,C_54,D_55) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1949,plain,(
    ! [B_150,C_154,E_152,D_153,A_151] : k2_xboole_0(k1_enumset1(A_151,B_150,C_154),k2_tarski(D_153,E_152)) = k3_enumset1(A_151,B_150,C_154,D_153,E_152) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1973,plain,(
    ! [A_47,B_48,D_153,E_152] : k3_enumset1(A_47,A_47,B_48,D_153,E_152) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_153,E_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1949])).

tff(c_1979,plain,(
    ! [A_47,B_48,D_153,E_152] : k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(D_153,E_152)) = k2_enumset1(A_47,B_48,D_153,E_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1973])).

tff(c_26,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1174,plain,(
    ! [A_126,B_127,C_128,D_129] : k2_xboole_0(k1_enumset1(A_126,B_127,C_128),k1_tarski(D_129)) = k2_enumset1(A_126,B_127,C_128,D_129) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1198,plain,(
    ! [A_47,B_48,D_129] : k2_xboole_0(k2_tarski(A_47,B_48),k1_tarski(D_129)) = k2_enumset1(A_47,A_47,B_48,D_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1174])).

tff(c_7567,plain,(
    ! [A_226,B_227,D_228] : k2_xboole_0(k2_tarski(A_226,B_227),k1_tarski(D_228)) = k1_enumset1(A_226,B_227,D_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1198])).

tff(c_7588,plain,(
    ! [A_46,D_228] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_228)) = k1_enumset1(A_46,A_46,D_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7567])).

tff(c_7592,plain,(
    ! [A_229,D_230] : k2_xboole_0(k1_tarski(A_229),k1_tarski(D_230)) = k2_tarski(A_229,D_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7588])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_812,plain,(
    ! [A_111,B_112] : k5_xboole_0(k5_xboole_0(A_111,B_112),k3_xboole_0(A_111,B_112)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6115,plain,(
    ! [A_211,B_212] : k5_xboole_0(k5_xboole_0(A_211,B_212),k3_xboole_0(B_212,A_211)) = k2_xboole_0(B_212,A_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_812])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6137,plain,(
    ! [A_211,B_212] : k5_xboole_0(A_211,k5_xboole_0(B_212,k3_xboole_0(B_212,A_211))) = k2_xboole_0(B_212,A_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_6115,c_6])).

tff(c_6187,plain,(
    ! [B_212,A_211] : k2_xboole_0(B_212,A_211) = k2_xboole_0(A_211,B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_6137])).

tff(c_7613,plain,(
    ! [D_231,A_232] : k2_xboole_0(k1_tarski(D_231),k1_tarski(A_232)) = k2_tarski(A_232,D_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_7592,c_6187])).

tff(c_7591,plain,(
    ! [A_46,D_228] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_228)) = k2_tarski(A_46,D_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7588])).

tff(c_7619,plain,(
    ! [D_231,A_232] : k2_tarski(D_231,A_232) = k2_tarski(A_232,D_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_7613,c_7591])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_969,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_38])).

tff(c_6193,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6187,c_969])).

tff(c_7644,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7619,c_7619,c_6193])).

tff(c_8194,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_7644])).

tff(c_8197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_940,c_8194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.51  
% 7.05/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.51  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.05/2.51  
% 7.05/2.51  %Foreground sorts:
% 7.05/2.51  
% 7.05/2.51  
% 7.05/2.51  %Background operators:
% 7.05/2.51  
% 7.05/2.51  
% 7.05/2.51  %Foreground operators:
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.05/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.05/2.51  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.05/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.05/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.05/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.05/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.05/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.05/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.05/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.51  
% 7.41/2.53  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 7.41/2.53  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.41/2.53  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_enumset1)).
% 7.41/2.53  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 7.41/2.53  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.41/2.53  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.41/2.53  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 7.41/2.53  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.41/2.53  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 7.41/2.53  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.41/2.53  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.41/2.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.41/2.53  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.41/2.53  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.41/2.53  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 7.41/2.53  tff(c_517, plain, (![D_100, C_101, B_102, A_103]: (k2_enumset1(D_100, C_101, B_102, A_103)=k2_enumset1(A_103, B_102, C_101, D_100))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.53  tff(c_30, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.41/2.53  tff(c_864, plain, (![A_113, B_114, C_115]: (k2_enumset1(A_113, B_114, C_115, C_115)=k1_enumset1(C_115, B_114, A_113))), inference(superposition, [status(thm), theory('equality')], [c_517, c_30])).
% 7.41/2.53  tff(c_398, plain, (![C_96, D_97, B_98, A_99]: (k2_enumset1(C_96, D_97, B_98, A_99)=k2_enumset1(A_99, B_98, C_96, D_97))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.41/2.53  tff(c_454, plain, (![C_96, D_97, B_98]: (k2_enumset1(C_96, D_97, B_98, B_98)=k1_enumset1(B_98, C_96, D_97))), inference(superposition, [status(thm), theory('equality')], [c_398, c_30])).
% 7.41/2.53  tff(c_870, plain, (![C_115, B_114, A_113]: (k1_enumset1(C_115, B_114, A_113)=k1_enumset1(C_115, A_113, B_114))), inference(superposition, [status(thm), theory('equality')], [c_864, c_454])).
% 7.41/2.53  tff(c_16, plain, (![B_22, D_24, C_23, A_21]: (k2_enumset1(B_22, D_24, C_23, A_21)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.41/2.53  tff(c_940, plain, (![A_21, B_22, D_24]: (k2_enumset1(A_21, B_22, A_21, D_24)=k1_enumset1(A_21, D_24, B_22))), inference(superposition, [status(thm), theory('equality')], [c_16, c_864])).
% 7.41/2.53  tff(c_32, plain, (![A_52, B_53, C_54, D_55]: (k3_enumset1(A_52, A_52, B_53, C_54, D_55)=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.41/2.53  tff(c_28, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.41/2.53  tff(c_1949, plain, (![B_150, C_154, E_152, D_153, A_151]: (k2_xboole_0(k1_enumset1(A_151, B_150, C_154), k2_tarski(D_153, E_152))=k3_enumset1(A_151, B_150, C_154, D_153, E_152))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.41/2.53  tff(c_1973, plain, (![A_47, B_48, D_153, E_152]: (k3_enumset1(A_47, A_47, B_48, D_153, E_152)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_153, E_152)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1949])).
% 7.41/2.53  tff(c_1979, plain, (![A_47, B_48, D_153, E_152]: (k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(D_153, E_152))=k2_enumset1(A_47, B_48, D_153, E_152))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1973])).
% 7.41/2.53  tff(c_26, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.41/2.53  tff(c_1174, plain, (![A_126, B_127, C_128, D_129]: (k2_xboole_0(k1_enumset1(A_126, B_127, C_128), k1_tarski(D_129))=k2_enumset1(A_126, B_127, C_128, D_129))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.41/2.53  tff(c_1198, plain, (![A_47, B_48, D_129]: (k2_xboole_0(k2_tarski(A_47, B_48), k1_tarski(D_129))=k2_enumset1(A_47, A_47, B_48, D_129))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1174])).
% 7.41/2.53  tff(c_7567, plain, (![A_226, B_227, D_228]: (k2_xboole_0(k2_tarski(A_226, B_227), k1_tarski(D_228))=k1_enumset1(A_226, B_227, D_228))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1198])).
% 7.41/2.53  tff(c_7588, plain, (![A_46, D_228]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_228))=k1_enumset1(A_46, A_46, D_228))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7567])).
% 7.41/2.53  tff(c_7592, plain, (![A_229, D_230]: (k2_xboole_0(k1_tarski(A_229), k1_tarski(D_230))=k2_tarski(A_229, D_230))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7588])).
% 7.41/2.53  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.41/2.53  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.41/2.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.53  tff(c_812, plain, (![A_111, B_112]: (k5_xboole_0(k5_xboole_0(A_111, B_112), k3_xboole_0(A_111, B_112))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.41/2.53  tff(c_6115, plain, (![A_211, B_212]: (k5_xboole_0(k5_xboole_0(A_211, B_212), k3_xboole_0(B_212, A_211))=k2_xboole_0(B_212, A_211))), inference(superposition, [status(thm), theory('equality')], [c_2, c_812])).
% 7.41/2.53  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.53  tff(c_6137, plain, (![A_211, B_212]: (k5_xboole_0(A_211, k5_xboole_0(B_212, k3_xboole_0(B_212, A_211)))=k2_xboole_0(B_212, A_211))), inference(superposition, [status(thm), theory('equality')], [c_6115, c_6])).
% 7.41/2.53  tff(c_6187, plain, (![B_212, A_211]: (k2_xboole_0(B_212, A_211)=k2_xboole_0(A_211, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_6137])).
% 7.41/2.53  tff(c_7613, plain, (![D_231, A_232]: (k2_xboole_0(k1_tarski(D_231), k1_tarski(A_232))=k2_tarski(A_232, D_231))), inference(superposition, [status(thm), theory('equality')], [c_7592, c_6187])).
% 7.41/2.53  tff(c_7591, plain, (![A_46, D_228]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_228))=k2_tarski(A_46, D_228))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7588])).
% 7.41/2.53  tff(c_7619, plain, (![D_231, A_232]: (k2_tarski(D_231, A_232)=k2_tarski(A_232, D_231))), inference(superposition, [status(thm), theory('equality')], [c_7613, c_7591])).
% 7.41/2.53  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.41/2.53  tff(c_969, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_38])).
% 7.41/2.53  tff(c_6193, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6187, c_969])).
% 7.41/2.53  tff(c_7644, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7619, c_7619, c_6193])).
% 7.41/2.53  tff(c_8194, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_7644])).
% 7.41/2.53  tff(c_8197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_870, c_940, c_8194])).
% 7.41/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.53  
% 7.41/2.53  Inference rules
% 7.41/2.53  ----------------------
% 7.41/2.53  #Ref     : 0
% 7.41/2.53  #Sup     : 2165
% 7.41/2.53  #Fact    : 0
% 7.41/2.53  #Define  : 0
% 7.41/2.53  #Split   : 0
% 7.41/2.53  #Chain   : 0
% 7.41/2.53  #Close   : 0
% 7.41/2.53  
% 7.41/2.53  Ordering : KBO
% 7.41/2.53  
% 7.41/2.53  Simplification rules
% 7.41/2.53  ----------------------
% 7.41/2.53  #Subsume      : 680
% 7.41/2.53  #Demod        : 996
% 7.41/2.53  #Tautology    : 1025
% 7.41/2.53  #SimpNegUnit  : 0
% 7.41/2.53  #BackRed      : 5
% 7.41/2.53  
% 7.41/2.53  #Partial instantiations: 0
% 7.41/2.53  #Strategies tried      : 1
% 7.41/2.53  
% 7.41/2.53  Timing (in seconds)
% 7.41/2.53  ----------------------
% 7.41/2.53  Preprocessing        : 0.31
% 7.41/2.53  Parsing              : 0.16
% 7.41/2.53  CNF conversion       : 0.02
% 7.41/2.53  Main loop            : 1.46
% 7.41/2.53  Inferencing          : 0.39
% 7.41/2.53  Reduction            : 0.81
% 7.41/2.53  Demodulation         : 0.74
% 7.41/2.53  BG Simplification    : 0.04
% 7.41/2.53  Subsumption          : 0.16
% 7.41/2.53  Abstraction          : 0.07
% 7.41/2.53  MUC search           : 0.00
% 7.41/2.53  Cooper               : 0.00
% 7.41/2.53  Total                : 1.80
% 7.41/2.53  Index Insertion      : 0.00
% 7.41/2.53  Index Deletion       : 0.00
% 7.41/2.53  Index Matching       : 0.00
% 7.41/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

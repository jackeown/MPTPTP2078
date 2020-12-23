%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 10.86s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 162 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 145 expanded)
%              Number of equality atoms :   55 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_311,plain,(
    ! [B_81,D_82,C_83,A_84] : k2_enumset1(B_81,D_82,C_83,A_84) = k2_enumset1(A_84,B_81,C_83,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_505,plain,(
    ! [A_89,D_90,C_91] : k2_enumset1(A_89,D_90,C_91,D_90) = k1_enumset1(D_90,C_91,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_28])).

tff(c_16,plain,(
    ! [D_23,C_22,B_21,A_20] : k2_enumset1(D_23,C_22,B_21,A_20) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_514,plain,(
    ! [D_90,C_91,A_89] : k2_enumset1(D_90,C_91,D_90,A_89) = k1_enumset1(D_90,C_91,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_16])).

tff(c_30,plain,(
    ! [A_48,B_49,C_50,D_51] : k3_enumset1(A_48,A_48,B_49,C_50,D_51) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [D_55,B_53,A_52,E_56,C_54] : k4_enumset1(A_52,A_52,B_53,C_54,D_55,E_56) = k3_enumset1(A_52,B_53,C_54,D_55,E_56) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1128,plain,(
    ! [F_124,E_125,A_126,D_129,C_127,B_128] : k2_xboole_0(k2_enumset1(A_126,B_128,C_127,D_129),k2_tarski(E_125,F_124)) = k4_enumset1(A_126,B_128,C_127,D_129,E_125,F_124) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1173,plain,(
    ! [F_124,C_47,A_45,E_125,B_46] : k4_enumset1(A_45,A_45,B_46,C_47,E_125,F_124) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),k2_tarski(E_125,F_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1128])).

tff(c_8581,plain,(
    ! [F_236,C_238,E_239,A_237,B_235] : k2_xboole_0(k1_enumset1(A_237,B_235,C_238),k2_tarski(E_239,F_236)) = k3_enumset1(A_237,B_235,C_238,E_239,F_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1173])).

tff(c_8623,plain,(
    ! [A_43,B_44,E_239,F_236] : k3_enumset1(A_43,A_43,B_44,E_239,F_236) = k2_xboole_0(k2_tarski(A_43,B_44),k2_tarski(E_239,F_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8581])).

tff(c_8629,plain,(
    ! [A_43,B_44,E_239,F_236] : k2_xboole_0(k2_tarski(A_43,B_44),k2_tarski(E_239,F_236)) = k2_enumset1(A_43,B_44,E_239,F_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8623])).

tff(c_24,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_713,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_xboole_0(k1_enumset1(A_103,B_104,C_105),k1_tarski(D_106)) = k2_enumset1(A_103,B_104,C_105,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_731,plain,(
    ! [A_43,B_44,D_106] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(D_106)) = k2_enumset1(A_43,A_43,B_44,D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_713])).

tff(c_3515,plain,(
    ! [A_175,B_176,D_177] : k2_xboole_0(k2_tarski(A_175,B_176),k1_tarski(D_177)) = k1_enumset1(A_175,B_176,D_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_731])).

tff(c_3536,plain,(
    ! [A_42,D_177] : k2_xboole_0(k1_tarski(A_42),k1_tarski(D_177)) = k1_enumset1(A_42,A_42,D_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3515])).

tff(c_3540,plain,(
    ! [A_178,D_179] : k2_xboole_0(k1_tarski(A_178),k1_tarski(D_179)) = k2_tarski(A_178,D_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3536])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_69,B_70] : k5_xboole_0(k5_xboole_0(A_69,B_70),k3_xboole_0(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2293,plain,(
    ! [B_159,A_160] : k5_xboole_0(k5_xboole_0(B_159,A_160),k3_xboole_0(A_160,B_159)) = k2_xboole_0(A_160,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2308,plain,(
    ! [B_159,A_160] : k5_xboole_0(B_159,k5_xboole_0(A_160,k3_xboole_0(A_160,B_159))) = k2_xboole_0(A_160,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2293,c_6])).

tff(c_2364,plain,(
    ! [B_159,A_160] : k2_xboole_0(B_159,A_160) = k2_xboole_0(A_160,B_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_2308])).

tff(c_3759,plain,(
    ! [D_183,A_184] : k2_xboole_0(k1_tarski(D_183),k1_tarski(A_184)) = k2_tarski(A_184,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_2364])).

tff(c_3539,plain,(
    ! [A_42,D_177] : k2_xboole_0(k1_tarski(A_42),k1_tarski(D_177)) = k2_tarski(A_42,D_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3536])).

tff(c_3765,plain,(
    ! [D_183,A_184] : k2_tarski(D_183,A_184) = k2_tarski(A_184,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_3759,c_3539])).

tff(c_14,plain,(
    ! [B_17,D_19,C_18,A_16] : k2_enumset1(B_17,D_19,C_18,A_16) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_396,plain,(
    ! [D_85,C_86,B_87,A_88] : k2_enumset1(D_85,C_86,B_87,A_88) = k2_enumset1(A_88,B_87,C_86,D_85) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_567,plain,(
    ! [C_92,B_93,A_94] : k2_enumset1(C_92,B_93,A_94,A_94) = k1_enumset1(A_94,B_93,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_396])).

tff(c_840,plain,(
    ! [A_115,B_116,D_117] : k2_enumset1(A_115,B_116,A_115,D_117) = k1_enumset1(A_115,D_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_567])).

tff(c_846,plain,(
    ! [A_115,D_117,B_116] : k1_enumset1(A_115,D_117,B_116) = k1_enumset1(A_115,B_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_514])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_941,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_34])).

tff(c_2371,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_941])).

tff(c_3790,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_3765,c_2371])).

tff(c_16996,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8629,c_3790])).

tff(c_16999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_16996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:35:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.86/4.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/4.37  
% 10.86/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/4.37  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 10.86/4.37  
% 10.86/4.37  %Foreground sorts:
% 10.86/4.37  
% 10.86/4.37  
% 10.86/4.37  %Background operators:
% 10.86/4.37  
% 10.86/4.37  
% 10.86/4.37  %Foreground operators:
% 10.86/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.86/4.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.86/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.86/4.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.86/4.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.86/4.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.86/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.86/4.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.86/4.37  tff('#skF_2', type, '#skF_2': $i).
% 10.86/4.37  tff('#skF_3', type, '#skF_3': $i).
% 10.86/4.37  tff('#skF_1', type, '#skF_1': $i).
% 10.86/4.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.86/4.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.86/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.86/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.86/4.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.86/4.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.86/4.37  
% 10.86/4.39  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 10.86/4.39  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 10.86/4.39  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 10.86/4.39  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 10.86/4.39  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.86/4.39  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 10.86/4.39  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 10.86/4.39  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.86/4.39  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 10.86/4.39  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.86/4.39  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.86/4.39  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.86/4.39  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 10.86/4.39  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.86/4.39  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 10.86/4.39  tff(c_311, plain, (![B_81, D_82, C_83, A_84]: (k2_enumset1(B_81, D_82, C_83, A_84)=k2_enumset1(A_84, B_81, C_83, D_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.86/4.39  tff(c_28, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.86/4.39  tff(c_505, plain, (![A_89, D_90, C_91]: (k2_enumset1(A_89, D_90, C_91, D_90)=k1_enumset1(D_90, C_91, A_89))), inference(superposition, [status(thm), theory('equality')], [c_311, c_28])).
% 10.86/4.39  tff(c_16, plain, (![D_23, C_22, B_21, A_20]: (k2_enumset1(D_23, C_22, B_21, A_20)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/4.39  tff(c_514, plain, (![D_90, C_91, A_89]: (k2_enumset1(D_90, C_91, D_90, A_89)=k1_enumset1(D_90, C_91, A_89))), inference(superposition, [status(thm), theory('equality')], [c_505, c_16])).
% 10.86/4.39  tff(c_30, plain, (![A_48, B_49, C_50, D_51]: (k3_enumset1(A_48, A_48, B_49, C_50, D_51)=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.86/4.39  tff(c_26, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.86/4.39  tff(c_32, plain, (![D_55, B_53, A_52, E_56, C_54]: (k4_enumset1(A_52, A_52, B_53, C_54, D_55, E_56)=k3_enumset1(A_52, B_53, C_54, D_55, E_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.86/4.39  tff(c_1128, plain, (![F_124, E_125, A_126, D_129, C_127, B_128]: (k2_xboole_0(k2_enumset1(A_126, B_128, C_127, D_129), k2_tarski(E_125, F_124))=k4_enumset1(A_126, B_128, C_127, D_129, E_125, F_124))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.86/4.39  tff(c_1173, plain, (![F_124, C_47, A_45, E_125, B_46]: (k4_enumset1(A_45, A_45, B_46, C_47, E_125, F_124)=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), k2_tarski(E_125, F_124)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1128])).
% 10.86/4.39  tff(c_8581, plain, (![F_236, C_238, E_239, A_237, B_235]: (k2_xboole_0(k1_enumset1(A_237, B_235, C_238), k2_tarski(E_239, F_236))=k3_enumset1(A_237, B_235, C_238, E_239, F_236))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1173])).
% 10.86/4.39  tff(c_8623, plain, (![A_43, B_44, E_239, F_236]: (k3_enumset1(A_43, A_43, B_44, E_239, F_236)=k2_xboole_0(k2_tarski(A_43, B_44), k2_tarski(E_239, F_236)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8581])).
% 10.86/4.39  tff(c_8629, plain, (![A_43, B_44, E_239, F_236]: (k2_xboole_0(k2_tarski(A_43, B_44), k2_tarski(E_239, F_236))=k2_enumset1(A_43, B_44, E_239, F_236))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8623])).
% 10.86/4.39  tff(c_24, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.86/4.39  tff(c_713, plain, (![A_103, B_104, C_105, D_106]: (k2_xboole_0(k1_enumset1(A_103, B_104, C_105), k1_tarski(D_106))=k2_enumset1(A_103, B_104, C_105, D_106))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.86/4.39  tff(c_731, plain, (![A_43, B_44, D_106]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(D_106))=k2_enumset1(A_43, A_43, B_44, D_106))), inference(superposition, [status(thm), theory('equality')], [c_26, c_713])).
% 10.86/4.39  tff(c_3515, plain, (![A_175, B_176, D_177]: (k2_xboole_0(k2_tarski(A_175, B_176), k1_tarski(D_177))=k1_enumset1(A_175, B_176, D_177))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_731])).
% 10.86/4.39  tff(c_3536, plain, (![A_42, D_177]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(D_177))=k1_enumset1(A_42, A_42, D_177))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3515])).
% 10.86/4.39  tff(c_3540, plain, (![A_178, D_179]: (k2_xboole_0(k1_tarski(A_178), k1_tarski(D_179))=k2_tarski(A_178, D_179))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3536])).
% 10.86/4.39  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.86/4.39  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.86/4.39  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.86/4.39  tff(c_113, plain, (![A_69, B_70]: (k5_xboole_0(k5_xboole_0(A_69, B_70), k3_xboole_0(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.86/4.39  tff(c_2293, plain, (![B_159, A_160]: (k5_xboole_0(k5_xboole_0(B_159, A_160), k3_xboole_0(A_160, B_159))=k2_xboole_0(A_160, B_159))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 10.86/4.39  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.86/4.39  tff(c_2308, plain, (![B_159, A_160]: (k5_xboole_0(B_159, k5_xboole_0(A_160, k3_xboole_0(A_160, B_159)))=k2_xboole_0(A_160, B_159))), inference(superposition, [status(thm), theory('equality')], [c_2293, c_6])).
% 10.86/4.39  tff(c_2364, plain, (![B_159, A_160]: (k2_xboole_0(B_159, A_160)=k2_xboole_0(A_160, B_159))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_2308])).
% 10.86/4.39  tff(c_3759, plain, (![D_183, A_184]: (k2_xboole_0(k1_tarski(D_183), k1_tarski(A_184))=k2_tarski(A_184, D_183))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_2364])).
% 10.86/4.39  tff(c_3539, plain, (![A_42, D_177]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(D_177))=k2_tarski(A_42, D_177))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3536])).
% 10.86/4.39  tff(c_3765, plain, (![D_183, A_184]: (k2_tarski(D_183, A_184)=k2_tarski(A_184, D_183))), inference(superposition, [status(thm), theory('equality')], [c_3759, c_3539])).
% 10.86/4.39  tff(c_14, plain, (![B_17, D_19, C_18, A_16]: (k2_enumset1(B_17, D_19, C_18, A_16)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.86/4.39  tff(c_396, plain, (![D_85, C_86, B_87, A_88]: (k2_enumset1(D_85, C_86, B_87, A_88)=k2_enumset1(A_88, B_87, C_86, D_85))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/4.39  tff(c_567, plain, (![C_92, B_93, A_94]: (k2_enumset1(C_92, B_93, A_94, A_94)=k1_enumset1(A_94, B_93, C_92))), inference(superposition, [status(thm), theory('equality')], [c_28, c_396])).
% 10.86/4.39  tff(c_840, plain, (![A_115, B_116, D_117]: (k2_enumset1(A_115, B_116, A_115, D_117)=k1_enumset1(A_115, D_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_14, c_567])).
% 10.86/4.39  tff(c_846, plain, (![A_115, D_117, B_116]: (k1_enumset1(A_115, D_117, B_116)=k1_enumset1(A_115, B_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_840, c_514])).
% 10.86/4.39  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.86/4.39  tff(c_941, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_34])).
% 10.86/4.39  tff(c_2371, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_941])).
% 10.86/4.39  tff(c_3790, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_3765, c_2371])).
% 10.86/4.39  tff(c_16996, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8629, c_3790])).
% 10.86/4.39  tff(c_16999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_16996])).
% 10.86/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/4.39  
% 10.86/4.39  Inference rules
% 10.86/4.39  ----------------------
% 10.86/4.39  #Ref     : 0
% 10.86/4.39  #Sup     : 4575
% 10.86/4.39  #Fact    : 0
% 10.86/4.39  #Define  : 0
% 10.86/4.39  #Split   : 0
% 10.86/4.39  #Chain   : 0
% 10.86/4.39  #Close   : 0
% 10.86/4.39  
% 10.86/4.39  Ordering : KBO
% 10.86/4.39  
% 10.86/4.39  Simplification rules
% 10.86/4.39  ----------------------
% 10.86/4.39  #Subsume      : 1129
% 10.86/4.39  #Demod        : 2399
% 10.86/4.39  #Tautology    : 1420
% 10.86/4.39  #SimpNegUnit  : 0
% 10.86/4.39  #BackRed      : 5
% 10.86/4.39  
% 10.86/4.39  #Partial instantiations: 0
% 10.86/4.39  #Strategies tried      : 1
% 10.86/4.39  
% 10.86/4.39  Timing (in seconds)
% 10.86/4.39  ----------------------
% 10.86/4.39  Preprocessing        : 0.30
% 10.86/4.39  Parsing              : 0.16
% 10.86/4.39  CNF conversion       : 0.02
% 10.86/4.39  Main loop            : 3.33
% 10.86/4.39  Inferencing          : 0.70
% 10.86/4.39  Reduction            : 2.10
% 10.86/4.39  Demodulation         : 1.96
% 10.86/4.39  BG Simplification    : 0.10
% 10.86/4.39  Subsumption          : 0.32
% 10.86/4.39  Abstraction          : 0.16
% 10.86/4.39  MUC search           : 0.00
% 10.86/4.39  Cooper               : 0.00
% 10.86/4.39  Total                : 3.66
% 10.86/4.39  Index Insertion      : 0.00
% 10.86/4.39  Index Deletion       : 0.00
% 10.86/4.39  Index Matching       : 0.00
% 10.86/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

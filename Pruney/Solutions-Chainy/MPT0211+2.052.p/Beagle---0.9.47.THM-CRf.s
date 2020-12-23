%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 11.77s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 177 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 161 expanded)
%              Number of equality atoms :   53 ( 160 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_224,plain,(
    ! [B_70,D_71,C_72,A_73] : k2_enumset1(B_70,D_71,C_72,A_73) = k2_enumset1(A_73,B_70,C_72,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_240,plain,(
    ! [B_70,D_71,C_72] : k2_enumset1(B_70,D_71,C_72,B_70) = k1_enumset1(B_70,C_72,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_28])).

tff(c_352,plain,(
    ! [A_80,C_81,D_82,B_83] : k2_enumset1(A_80,C_81,D_82,B_83) = k2_enumset1(A_80,B_83,C_81,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_447,plain,(
    ! [B_84,C_85,D_86] : k2_enumset1(B_84,C_85,D_86,B_84) = k1_enumset1(B_84,C_85,D_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_28])).

tff(c_491,plain,(
    ! [B_70,D_71,C_72] : k1_enumset1(B_70,D_71,C_72) = k1_enumset1(B_70,C_72,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_447])).

tff(c_12,plain,(
    ! [A_12,C_14,D_15,B_13] : k2_enumset1(A_12,C_14,D_15,B_13) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [B_49,A_48,D_51,E_52,C_50] : k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52) = k3_enumset1(A_48,B_49,C_50,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1792,plain,(
    ! [D_138,F_135,C_136,E_133,A_137,B_134] : k2_xboole_0(k2_enumset1(A_137,B_134,C_136,D_138),k2_tarski(E_133,F_135)) = k4_enumset1(A_137,B_134,C_136,D_138,E_133,F_135) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1852,plain,(
    ! [F_135,E_133,C_43,A_41,B_42] : k4_enumset1(A_41,A_41,B_42,C_43,E_133,F_135) = k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k2_tarski(E_133,F_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1792])).

tff(c_9384,plain,(
    ! [C_230,F_232,A_229,B_233,E_231] : k2_xboole_0(k1_enumset1(A_229,B_233,C_230),k2_tarski(E_231,F_232)) = k3_enumset1(A_229,B_233,C_230,E_231,F_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1852])).

tff(c_9426,plain,(
    ! [A_39,B_40,E_231,F_232] : k3_enumset1(A_39,A_39,B_40,E_231,F_232) = k2_xboole_0(k2_tarski(A_39,B_40),k2_tarski(E_231,F_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9384])).

tff(c_9432,plain,(
    ! [A_39,B_40,E_231,F_232] : k2_xboole_0(k2_tarski(A_39,B_40),k2_tarski(E_231,F_232)) = k2_enumset1(A_39,B_40,E_231,F_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9426])).

tff(c_24,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1436,plain,(
    ! [A_118,B_119,C_120,D_121] : k2_xboole_0(k1_enumset1(A_118,B_119,C_120),k1_tarski(D_121)) = k2_enumset1(A_118,B_119,C_120,D_121) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1460,plain,(
    ! [A_39,B_40,D_121] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(D_121)) = k2_enumset1(A_39,A_39,B_40,D_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1436])).

tff(c_5019,plain,(
    ! [A_178,B_179,D_180] : k2_xboole_0(k2_tarski(A_178,B_179),k1_tarski(D_180)) = k1_enumset1(A_178,B_179,D_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1460])).

tff(c_5040,plain,(
    ! [A_38,D_180] : k2_xboole_0(k1_tarski(A_38),k1_tarski(D_180)) = k1_enumset1(A_38,A_38,D_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5019])).

tff(c_5044,plain,(
    ! [A_181,D_182] : k2_xboole_0(k1_tarski(A_181),k1_tarski(D_182)) = k2_tarski(A_181,D_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5040])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_67,B_68,C_69] : k5_xboole_0(k5_xboole_0(A_67,B_68),C_69) = k5_xboole_0(A_67,k5_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2990,plain,(
    ! [C_155,A_156,B_157] : k5_xboole_0(C_155,k5_xboole_0(A_156,B_157)) = k5_xboole_0(A_156,k5_xboole_0(B_157,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_113,plain,(
    ! [A_65,B_66] : k5_xboole_0(k5_xboole_0(A_65,B_66),k3_xboole_0(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_65,B_66] : k5_xboole_0(k3_xboole_0(A_65,B_66),k5_xboole_0(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_3021,plain,(
    ! [C_155,B_157] : k5_xboole_0(C_155,k5_xboole_0(k3_xboole_0(B_157,C_155),B_157)) = k2_xboole_0(B_157,C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_122])).

tff(c_3161,plain,(
    ! [C_155,B_157] : k2_xboole_0(C_155,B_157) = k2_xboole_0(B_157,C_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_2,c_3021])).

tff(c_5065,plain,(
    ! [D_183,A_184] : k2_xboole_0(k1_tarski(D_183),k1_tarski(A_184)) = k2_tarski(A_184,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_5044,c_3161])).

tff(c_5043,plain,(
    ! [A_38,D_180] : k2_xboole_0(k1_tarski(A_38),k1_tarski(D_180)) = k2_tarski(A_38,D_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5040])).

tff(c_5071,plain,(
    ! [D_183,A_184] : k2_tarski(D_183,A_184) = k2_tarski(A_184,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_5065,c_5043])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_665,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_34])).

tff(c_3176,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_665])).

tff(c_5096,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5071,c_5071,c_3176])).

tff(c_20150,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9432,c_5096])).

tff(c_20153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_28,c_12,c_20150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.77/4.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.77/4.91  
% 11.77/4.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.77/4.91  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.77/4.91  
% 11.77/4.91  %Foreground sorts:
% 11.77/4.91  
% 11.77/4.91  
% 11.77/4.91  %Background operators:
% 11.77/4.91  
% 11.77/4.91  
% 11.77/4.91  %Foreground operators:
% 11.77/4.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.77/4.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.77/4.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.77/4.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.77/4.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.77/4.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.77/4.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.77/4.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.77/4.91  tff('#skF_2', type, '#skF_2': $i).
% 11.77/4.91  tff('#skF_3', type, '#skF_3': $i).
% 11.77/4.91  tff('#skF_1', type, '#skF_1': $i).
% 11.77/4.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.77/4.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.77/4.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.77/4.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.77/4.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.77/4.91  
% 11.91/4.93  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 11.91/4.93  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.91/4.93  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 11.91/4.93  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.91/4.93  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.91/4.93  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 11.91/4.93  tff(f_47, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 11.91/4.93  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.91/4.93  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 11.91/4.93  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.91/4.93  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.91/4.93  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.91/4.93  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.91/4.93  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.91/4.93  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 11.91/4.93  tff(c_224, plain, (![B_70, D_71, C_72, A_73]: (k2_enumset1(B_70, D_71, C_72, A_73)=k2_enumset1(A_73, B_70, C_72, D_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.93  tff(c_28, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.91/4.93  tff(c_240, plain, (![B_70, D_71, C_72]: (k2_enumset1(B_70, D_71, C_72, B_70)=k1_enumset1(B_70, C_72, D_71))), inference(superposition, [status(thm), theory('equality')], [c_224, c_28])).
% 11.91/4.93  tff(c_352, plain, (![A_80, C_81, D_82, B_83]: (k2_enumset1(A_80, C_81, D_82, B_83)=k2_enumset1(A_80, B_83, C_81, D_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.91/4.93  tff(c_447, plain, (![B_84, C_85, D_86]: (k2_enumset1(B_84, C_85, D_86, B_84)=k1_enumset1(B_84, C_85, D_86))), inference(superposition, [status(thm), theory('equality')], [c_352, c_28])).
% 11.91/4.93  tff(c_491, plain, (![B_70, D_71, C_72]: (k1_enumset1(B_70, D_71, C_72)=k1_enumset1(B_70, C_72, D_71))), inference(superposition, [status(thm), theory('equality')], [c_240, c_447])).
% 11.91/4.93  tff(c_12, plain, (![A_12, C_14, D_15, B_13]: (k2_enumset1(A_12, C_14, D_15, B_13)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.91/4.93  tff(c_30, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.91/4.93  tff(c_26, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.91/4.93  tff(c_32, plain, (![B_49, A_48, D_51, E_52, C_50]: (k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52)=k3_enumset1(A_48, B_49, C_50, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.91/4.93  tff(c_1792, plain, (![D_138, F_135, C_136, E_133, A_137, B_134]: (k2_xboole_0(k2_enumset1(A_137, B_134, C_136, D_138), k2_tarski(E_133, F_135))=k4_enumset1(A_137, B_134, C_136, D_138, E_133, F_135))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.91/4.93  tff(c_1852, plain, (![F_135, E_133, C_43, A_41, B_42]: (k4_enumset1(A_41, A_41, B_42, C_43, E_133, F_135)=k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k2_tarski(E_133, F_135)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1792])).
% 11.91/4.93  tff(c_9384, plain, (![C_230, F_232, A_229, B_233, E_231]: (k2_xboole_0(k1_enumset1(A_229, B_233, C_230), k2_tarski(E_231, F_232))=k3_enumset1(A_229, B_233, C_230, E_231, F_232))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1852])).
% 11.91/4.93  tff(c_9426, plain, (![A_39, B_40, E_231, F_232]: (k3_enumset1(A_39, A_39, B_40, E_231, F_232)=k2_xboole_0(k2_tarski(A_39, B_40), k2_tarski(E_231, F_232)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9384])).
% 11.91/4.93  tff(c_9432, plain, (![A_39, B_40, E_231, F_232]: (k2_xboole_0(k2_tarski(A_39, B_40), k2_tarski(E_231, F_232))=k2_enumset1(A_39, B_40, E_231, F_232))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9426])).
% 11.91/4.93  tff(c_24, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.91/4.93  tff(c_1436, plain, (![A_118, B_119, C_120, D_121]: (k2_xboole_0(k1_enumset1(A_118, B_119, C_120), k1_tarski(D_121))=k2_enumset1(A_118, B_119, C_120, D_121))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.93  tff(c_1460, plain, (![A_39, B_40, D_121]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(D_121))=k2_enumset1(A_39, A_39, B_40, D_121))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1436])).
% 11.91/4.93  tff(c_5019, plain, (![A_178, B_179, D_180]: (k2_xboole_0(k2_tarski(A_178, B_179), k1_tarski(D_180))=k1_enumset1(A_178, B_179, D_180))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1460])).
% 11.91/4.93  tff(c_5040, plain, (![A_38, D_180]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(D_180))=k1_enumset1(A_38, A_38, D_180))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5019])).
% 11.91/4.93  tff(c_5044, plain, (![A_181, D_182]: (k2_xboole_0(k1_tarski(A_181), k1_tarski(D_182))=k2_tarski(A_181, D_182))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5040])).
% 11.91/4.93  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.91/4.93  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.91/4.93  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.91/4.93  tff(c_152, plain, (![A_67, B_68, C_69]: (k5_xboole_0(k5_xboole_0(A_67, B_68), C_69)=k5_xboole_0(A_67, k5_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.91/4.93  tff(c_2990, plain, (![C_155, A_156, B_157]: (k5_xboole_0(C_155, k5_xboole_0(A_156, B_157))=k5_xboole_0(A_156, k5_xboole_0(B_157, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 11.91/4.93  tff(c_113, plain, (![A_65, B_66]: (k5_xboole_0(k5_xboole_0(A_65, B_66), k3_xboole_0(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.91/4.93  tff(c_122, plain, (![A_65, B_66]: (k5_xboole_0(k3_xboole_0(A_65, B_66), k5_xboole_0(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 11.91/4.93  tff(c_3021, plain, (![C_155, B_157]: (k5_xboole_0(C_155, k5_xboole_0(k3_xboole_0(B_157, C_155), B_157))=k2_xboole_0(B_157, C_155))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_122])).
% 11.91/4.93  tff(c_3161, plain, (![C_155, B_157]: (k2_xboole_0(C_155, B_157)=k2_xboole_0(B_157, C_155))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_2, c_3021])).
% 11.91/4.93  tff(c_5065, plain, (![D_183, A_184]: (k2_xboole_0(k1_tarski(D_183), k1_tarski(A_184))=k2_tarski(A_184, D_183))), inference(superposition, [status(thm), theory('equality')], [c_5044, c_3161])).
% 11.91/4.93  tff(c_5043, plain, (![A_38, D_180]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(D_180))=k2_tarski(A_38, D_180))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5040])).
% 11.91/4.93  tff(c_5071, plain, (![D_183, A_184]: (k2_tarski(D_183, A_184)=k2_tarski(A_184, D_183))), inference(superposition, [status(thm), theory('equality')], [c_5065, c_5043])).
% 11.91/4.93  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.91/4.93  tff(c_665, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_34])).
% 11.91/4.93  tff(c_3176, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_665])).
% 11.91/4.93  tff(c_5096, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5071, c_5071, c_3176])).
% 11.91/4.93  tff(c_20150, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9432, c_5096])).
% 11.91/4.93  tff(c_20153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_28, c_12, c_20150])).
% 11.91/4.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.93  
% 11.91/4.93  Inference rules
% 11.91/4.93  ----------------------
% 11.91/4.93  #Ref     : 0
% 11.91/4.93  #Sup     : 5332
% 11.91/4.93  #Fact    : 0
% 11.91/4.93  #Define  : 0
% 11.91/4.93  #Split   : 0
% 11.91/4.93  #Chain   : 0
% 11.91/4.93  #Close   : 0
% 11.91/4.93  
% 11.91/4.93  Ordering : KBO
% 11.91/4.93  
% 11.91/4.93  Simplification rules
% 11.91/4.93  ----------------------
% 11.91/4.93  #Subsume      : 1225
% 11.91/4.93  #Demod        : 3162
% 11.91/4.93  #Tautology    : 1857
% 11.91/4.93  #SimpNegUnit  : 0
% 11.91/4.93  #BackRed      : 5
% 11.91/4.93  
% 11.91/4.93  #Partial instantiations: 0
% 11.91/4.93  #Strategies tried      : 1
% 11.91/4.93  
% 11.91/4.93  Timing (in seconds)
% 11.91/4.93  ----------------------
% 11.91/4.93  Preprocessing        : 0.28
% 11.91/4.93  Parsing              : 0.15
% 11.91/4.93  CNF conversion       : 0.02
% 11.91/4.93  Main loop            : 3.79
% 11.91/4.93  Inferencing          : 0.74
% 11.91/4.93  Reduction            : 2.41
% 11.91/4.93  Demodulation         : 2.27
% 11.91/4.93  BG Simplification    : 0.11
% 11.91/4.93  Subsumption          : 0.38
% 11.91/4.93  Abstraction          : 0.17
% 11.91/4.93  MUC search           : 0.00
% 11.91/4.93  Cooper               : 0.00
% 11.91/4.93  Total                : 4.11
% 11.91/4.93  Index Insertion      : 0.00
% 11.91/4.93  Index Deletion       : 0.00
% 11.91/4.93  Index Matching       : 0.00
% 11.91/4.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------

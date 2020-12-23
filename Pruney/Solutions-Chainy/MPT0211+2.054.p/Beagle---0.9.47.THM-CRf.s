%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 160 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 142 expanded)
%              Number of equality atoms :   53 ( 141 expanded)
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

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_32,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,A_61,B_62,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,(
    ! [B_91,D_92,C_93,A_94] : k2_enumset1(B_91,D_92,C_93,A_94) = k2_enumset1(A_94,B_91,C_93,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [C_63,A_61,B_62] : k2_enumset1(C_63,A_61,B_62,A_61) = k1_enumset1(A_61,B_62,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_248,plain,(
    ! [D_101,C_102,B_103,A_104] : k2_enumset1(D_101,C_102,B_103,A_104) = k2_enumset1(A_104,B_103,C_102,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_311,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,B_62,A_61,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_248])).

tff(c_34,plain,(
    ! [A_64,B_65,C_66,D_67] : k3_enumset1(A_64,A_64,B_65,C_66,D_67) = k2_enumset1(A_64,B_65,C_66,D_67) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [E_72,C_70,B_69,D_71,A_68] : k4_enumset1(A_68,A_68,B_69,C_70,D_71,E_72) = k3_enumset1(A_68,B_69,C_70,D_71,E_72) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1873,plain,(
    ! [D_177,B_174,E_175,C_178,F_176,A_173] : k2_xboole_0(k2_enumset1(A_173,B_174,C_178,D_177),k2_tarski(E_175,F_176)) = k4_enumset1(A_173,B_174,C_178,D_177,E_175,F_176) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1933,plain,(
    ! [A_61,B_62,C_63,E_175,F_176] : k4_enumset1(A_61,A_61,B_62,C_63,E_175,F_176) = k2_xboole_0(k1_enumset1(A_61,B_62,C_63),k2_tarski(E_175,F_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1873])).

tff(c_8954,plain,(
    ! [E_285,C_282,F_281,A_284,B_283] : k2_xboole_0(k1_enumset1(A_284,B_283,C_282),k2_tarski(E_285,F_281)) = k3_enumset1(A_284,B_283,C_282,E_285,F_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1933])).

tff(c_8996,plain,(
    ! [A_59,B_60,E_285,F_281] : k3_enumset1(A_59,A_59,B_60,E_285,F_281) = k2_xboole_0(k2_tarski(A_59,B_60),k2_tarski(E_285,F_281)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8954])).

tff(c_9002,plain,(
    ! [A_59,B_60,E_285,F_281] : k2_xboole_0(k2_tarski(A_59,B_60),k2_tarski(E_285,F_281)) = k2_enumset1(A_59,B_60,E_285,F_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8996])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_347,plain,(
    ! [A_105,B_106] : k5_xboole_0(k5_xboole_0(A_105,B_106),k3_xboole_0(A_105,B_106)) = k2_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3464,plain,(
    ! [B_220,A_221] : k5_xboole_0(k5_xboole_0(B_220,A_221),k3_xboole_0(A_221,B_220)) = k2_xboole_0(A_221,B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_347])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3479,plain,(
    ! [B_220,A_221] : k5_xboole_0(B_220,k5_xboole_0(A_221,k3_xboole_0(A_221,B_220))) = k2_xboole_0(A_221,B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_3464,c_6])).

tff(c_3543,plain,(
    ! [B_222,A_223] : k2_xboole_0(B_222,A_223) = k2_xboole_0(A_223,B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_3479])).

tff(c_28,plain,(
    ! [A_58] : k2_tarski(A_58,A_58) = k1_tarski(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1356,plain,(
    ! [A_143,B_144,C_145,D_146] : k2_xboole_0(k1_enumset1(A_143,B_144,C_145),k1_tarski(D_146)) = k2_enumset1(A_143,B_144,C_145,D_146) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1380,plain,(
    ! [A_59,B_60,D_146] : k2_xboole_0(k2_tarski(A_59,B_60),k1_tarski(D_146)) = k2_enumset1(A_59,A_59,B_60,D_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1356])).

tff(c_3402,plain,(
    ! [A_213,B_214,D_215] : k2_xboole_0(k2_tarski(A_213,B_214),k1_tarski(D_215)) = k1_enumset1(A_213,B_214,D_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1380])).

tff(c_3411,plain,(
    ! [A_58,D_215] : k2_xboole_0(k1_tarski(A_58),k1_tarski(D_215)) = k1_enumset1(A_58,A_58,D_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3402])).

tff(c_3414,plain,(
    ! [A_58,D_215] : k2_xboole_0(k1_tarski(A_58),k1_tarski(D_215)) = k2_tarski(A_58,D_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3411])).

tff(c_3660,plain,(
    ! [D_224,A_225] : k2_xboole_0(k1_tarski(D_224),k1_tarski(A_225)) = k2_tarski(A_225,D_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_3543,c_3414])).

tff(c_3672,plain,(
    ! [D_224,A_225] : k2_tarski(D_224,A_225) = k2_tarski(A_225,D_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_3414])).

tff(c_3535,plain,(
    ! [B_220,A_221] : k2_xboole_0(B_220,A_221) = k2_xboole_0(A_221,B_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_3479])).

tff(c_135,plain,(
    ! [B_91,D_92,C_93] : k2_enumset1(B_91,D_92,C_93,B_91) = k1_enumset1(B_91,C_93,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_32])).

tff(c_807,plain,(
    ! [D_124,C_125,B_126] : k2_enumset1(D_124,C_125,B_126,D_124) = k1_enumset1(D_124,C_125,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_135])).

tff(c_837,plain,(
    ! [D_124,C_125,B_126] : k1_enumset1(D_124,C_125,B_126) = k1_enumset1(D_124,B_126,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_135])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_908,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_40])).

tff(c_3542,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3535,c_908])).

tff(c_4158,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_3542])).

tff(c_16812,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9002,c_4158])).

tff(c_16815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_16812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.99/4.42  
% 10.99/4.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.99/4.43  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 10.99/4.43  
% 10.99/4.43  %Foreground sorts:
% 10.99/4.43  
% 10.99/4.43  
% 10.99/4.43  %Background operators:
% 10.99/4.43  
% 10.99/4.43  
% 10.99/4.43  %Foreground operators:
% 10.99/4.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.99/4.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.99/4.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.99/4.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.99/4.43  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.99/4.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.99/4.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.99/4.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.99/4.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.99/4.43  tff('#skF_2', type, '#skF_2': $i).
% 10.99/4.43  tff('#skF_3', type, '#skF_3': $i).
% 10.99/4.43  tff('#skF_1', type, '#skF_1': $i).
% 10.99/4.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.99/4.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.99/4.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.99/4.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.99/4.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.99/4.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.99/4.43  
% 11.09/4.44  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 11.09/4.44  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 11.09/4.44  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 11.09/4.44  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 11.09/4.44  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.09/4.44  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 11.09/4.44  tff(f_51, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 11.09/4.44  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.09/4.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.09/4.44  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.09/4.44  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.09/4.44  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.09/4.44  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.09/4.44  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 11.09/4.44  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 11.09/4.44  tff(c_32, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, A_61, B_62, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.09/4.44  tff(c_119, plain, (![B_91, D_92, C_93, A_94]: (k2_enumset1(B_91, D_92, C_93, A_94)=k2_enumset1(A_94, B_91, C_93, D_92))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.09/4.44  tff(c_154, plain, (![C_63, A_61, B_62]: (k2_enumset1(C_63, A_61, B_62, A_61)=k1_enumset1(A_61, B_62, C_63))), inference(superposition, [status(thm), theory('equality')], [c_32, c_119])).
% 11.09/4.44  tff(c_248, plain, (![D_101, C_102, B_103, A_104]: (k2_enumset1(D_101, C_102, B_103, A_104)=k2_enumset1(A_104, B_103, C_102, D_101))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.09/4.44  tff(c_311, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, B_62, A_61, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(superposition, [status(thm), theory('equality')], [c_154, c_248])).
% 11.09/4.44  tff(c_34, plain, (![A_64, B_65, C_66, D_67]: (k3_enumset1(A_64, A_64, B_65, C_66, D_67)=k2_enumset1(A_64, B_65, C_66, D_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.09/4.44  tff(c_30, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.09/4.44  tff(c_36, plain, (![E_72, C_70, B_69, D_71, A_68]: (k4_enumset1(A_68, A_68, B_69, C_70, D_71, E_72)=k3_enumset1(A_68, B_69, C_70, D_71, E_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.09/4.44  tff(c_1873, plain, (![D_177, B_174, E_175, C_178, F_176, A_173]: (k2_xboole_0(k2_enumset1(A_173, B_174, C_178, D_177), k2_tarski(E_175, F_176))=k4_enumset1(A_173, B_174, C_178, D_177, E_175, F_176))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.09/4.44  tff(c_1933, plain, (![A_61, B_62, C_63, E_175, F_176]: (k4_enumset1(A_61, A_61, B_62, C_63, E_175, F_176)=k2_xboole_0(k1_enumset1(A_61, B_62, C_63), k2_tarski(E_175, F_176)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1873])).
% 11.09/4.44  tff(c_8954, plain, (![E_285, C_282, F_281, A_284, B_283]: (k2_xboole_0(k1_enumset1(A_284, B_283, C_282), k2_tarski(E_285, F_281))=k3_enumset1(A_284, B_283, C_282, E_285, F_281))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1933])).
% 11.09/4.44  tff(c_8996, plain, (![A_59, B_60, E_285, F_281]: (k3_enumset1(A_59, A_59, B_60, E_285, F_281)=k2_xboole_0(k2_tarski(A_59, B_60), k2_tarski(E_285, F_281)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8954])).
% 11.09/4.44  tff(c_9002, plain, (![A_59, B_60, E_285, F_281]: (k2_xboole_0(k2_tarski(A_59, B_60), k2_tarski(E_285, F_281))=k2_enumset1(A_59, B_60, E_285, F_281))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8996])).
% 11.09/4.44  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.09/4.44  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.09/4.44  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.09/4.44  tff(c_347, plain, (![A_105, B_106]: (k5_xboole_0(k5_xboole_0(A_105, B_106), k3_xboole_0(A_105, B_106))=k2_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.09/4.44  tff(c_3464, plain, (![B_220, A_221]: (k5_xboole_0(k5_xboole_0(B_220, A_221), k3_xboole_0(A_221, B_220))=k2_xboole_0(A_221, B_220))), inference(superposition, [status(thm), theory('equality')], [c_2, c_347])).
% 11.09/4.44  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.09/4.44  tff(c_3479, plain, (![B_220, A_221]: (k5_xboole_0(B_220, k5_xboole_0(A_221, k3_xboole_0(A_221, B_220)))=k2_xboole_0(A_221, B_220))), inference(superposition, [status(thm), theory('equality')], [c_3464, c_6])).
% 11.09/4.44  tff(c_3543, plain, (![B_222, A_223]: (k2_xboole_0(B_222, A_223)=k2_xboole_0(A_223, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_3479])).
% 11.09/4.44  tff(c_28, plain, (![A_58]: (k2_tarski(A_58, A_58)=k1_tarski(A_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.09/4.44  tff(c_1356, plain, (![A_143, B_144, C_145, D_146]: (k2_xboole_0(k1_enumset1(A_143, B_144, C_145), k1_tarski(D_146))=k2_enumset1(A_143, B_144, C_145, D_146))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.09/4.44  tff(c_1380, plain, (![A_59, B_60, D_146]: (k2_xboole_0(k2_tarski(A_59, B_60), k1_tarski(D_146))=k2_enumset1(A_59, A_59, B_60, D_146))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1356])).
% 11.09/4.44  tff(c_3402, plain, (![A_213, B_214, D_215]: (k2_xboole_0(k2_tarski(A_213, B_214), k1_tarski(D_215))=k1_enumset1(A_213, B_214, D_215))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1380])).
% 11.09/4.44  tff(c_3411, plain, (![A_58, D_215]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(D_215))=k1_enumset1(A_58, A_58, D_215))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3402])).
% 11.09/4.44  tff(c_3414, plain, (![A_58, D_215]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(D_215))=k2_tarski(A_58, D_215))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3411])).
% 11.09/4.44  tff(c_3660, plain, (![D_224, A_225]: (k2_xboole_0(k1_tarski(D_224), k1_tarski(A_225))=k2_tarski(A_225, D_224))), inference(superposition, [status(thm), theory('equality')], [c_3543, c_3414])).
% 11.09/4.44  tff(c_3672, plain, (![D_224, A_225]: (k2_tarski(D_224, A_225)=k2_tarski(A_225, D_224))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_3414])).
% 11.09/4.44  tff(c_3535, plain, (![B_220, A_221]: (k2_xboole_0(B_220, A_221)=k2_xboole_0(A_221, B_220))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_3479])).
% 11.09/4.44  tff(c_135, plain, (![B_91, D_92, C_93]: (k2_enumset1(B_91, D_92, C_93, B_91)=k1_enumset1(B_91, C_93, D_92))), inference(superposition, [status(thm), theory('equality')], [c_119, c_32])).
% 11.09/4.44  tff(c_807, plain, (![D_124, C_125, B_126]: (k2_enumset1(D_124, C_125, B_126, D_124)=k1_enumset1(D_124, C_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_248, c_135])).
% 11.09/4.44  tff(c_837, plain, (![D_124, C_125, B_126]: (k1_enumset1(D_124, C_125, B_126)=k1_enumset1(D_124, B_126, C_125))), inference(superposition, [status(thm), theory('equality')], [c_807, c_135])).
% 11.09/4.44  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.09/4.44  tff(c_908, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_837, c_40])).
% 11.09/4.44  tff(c_3542, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3535, c_908])).
% 11.09/4.44  tff(c_4158, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_3542])).
% 11.09/4.44  tff(c_16812, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9002, c_4158])).
% 11.09/4.44  tff(c_16815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_16812])).
% 11.09/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.44  
% 11.09/4.44  Inference rules
% 11.09/4.44  ----------------------
% 11.09/4.44  #Ref     : 0
% 11.09/4.44  #Sup     : 4557
% 11.09/4.44  #Fact    : 0
% 11.09/4.44  #Define  : 0
% 11.09/4.44  #Split   : 0
% 11.09/4.44  #Chain   : 0
% 11.09/4.44  #Close   : 0
% 11.09/4.44  
% 11.09/4.44  Ordering : KBO
% 11.09/4.44  
% 11.09/4.44  Simplification rules
% 11.09/4.44  ----------------------
% 11.09/4.44  #Subsume      : 1141
% 11.09/4.44  #Demod        : 2277
% 11.09/4.44  #Tautology    : 1415
% 11.09/4.44  #SimpNegUnit  : 0
% 11.09/4.44  #BackRed      : 4
% 11.09/4.44  
% 11.09/4.44  #Partial instantiations: 0
% 11.09/4.44  #Strategies tried      : 1
% 11.09/4.44  
% 11.09/4.44  Timing (in seconds)
% 11.09/4.44  ----------------------
% 11.09/4.44  Preprocessing        : 0.32
% 11.09/4.44  Parsing              : 0.17
% 11.09/4.44  CNF conversion       : 0.02
% 11.09/4.44  Main loop            : 3.28
% 11.09/4.44  Inferencing          : 0.71
% 11.09/4.44  Reduction            : 2.04
% 11.09/4.44  Demodulation         : 1.91
% 11.09/4.44  BG Simplification    : 0.11
% 11.09/4.44  Subsumption          : 0.31
% 11.09/4.44  Abstraction          : 0.15
% 11.09/4.45  MUC search           : 0.00
% 11.09/4.45  Cooper               : 0.00
% 11.09/4.45  Total                : 3.63
% 11.09/4.45  Index Insertion      : 0.00
% 11.09/4.45  Index Deletion       : 0.00
% 11.09/4.45  Index Matching       : 0.00
% 11.09/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

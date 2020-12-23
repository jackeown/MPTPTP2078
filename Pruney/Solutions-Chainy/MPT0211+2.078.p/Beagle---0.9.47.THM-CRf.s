%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 243 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :   45 ( 226 expanded)
%              Number of equality atoms :   44 ( 225 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_584,plain,(
    ! [B_97,D_98,C_99,A_100] : k2_enumset1(B_97,D_98,C_99,A_100) = k2_enumset1(A_100,B_97,C_99,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_358,plain,(
    ! [D_88,C_89,B_90,A_91] : k2_enumset1(D_88,C_89,B_90,A_91) = k2_enumset1(A_91,B_90,C_89,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_414,plain,(
    ! [D_88,C_89,B_90] : k2_enumset1(D_88,C_89,B_90,B_90) = k1_enumset1(B_90,C_89,D_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_28])).

tff(c_930,plain,(
    ! [B_114,D_115,A_116] : k2_enumset1(B_114,D_115,D_115,A_116) = k1_enumset1(D_115,B_114,A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_414])).

tff(c_482,plain,(
    ! [D_92,C_93,B_94] : k2_enumset1(D_92,C_93,B_94,B_94) = k1_enumset1(B_94,C_93,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_28])).

tff(c_10,plain,(
    ! [A_10,D_13,C_12,B_11] : k2_enumset1(A_10,D_13,C_12,B_11) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_511,plain,(
    ! [D_92,B_94,C_93] : k2_enumset1(D_92,B_94,B_94,C_93) = k1_enumset1(B_94,C_93,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_10])).

tff(c_936,plain,(
    ! [D_115,B_114,A_116] : k1_enumset1(D_115,B_114,A_116) = k1_enumset1(D_115,A_116,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_511])).

tff(c_604,plain,(
    ! [A_100,B_97,D_98] : k2_enumset1(A_100,B_97,A_100,D_98) = k1_enumset1(A_100,D_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_414])).

tff(c_30,plain,(
    ! [A_50,B_51,C_52,D_53] : k3_enumset1(A_50,A_50,B_51,C_52,D_53) = k2_enumset1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [C_56,E_58,D_57,B_55,A_54] : k4_enumset1(A_54,A_54,B_55,C_56,D_57,E_58) = k3_enumset1(A_54,B_55,C_56,D_57,E_58) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1537,plain,(
    ! [E_138,A_137,C_134,B_135,D_139,F_136] : k2_xboole_0(k2_enumset1(A_137,B_135,C_134,D_139),k2_tarski(E_138,F_136)) = k4_enumset1(A_137,B_135,C_134,D_139,E_138,F_136) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1594,plain,(
    ! [E_138,A_47,C_49,F_136,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,E_138,F_136) = k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k2_tarski(E_138,F_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1537])).

tff(c_8194,plain,(
    ! [C_230,E_228,F_227,A_226,B_229] : k2_xboole_0(k1_enumset1(A_226,B_229,C_230),k2_tarski(E_228,F_227)) = k3_enumset1(A_226,B_229,C_230,E_228,F_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1594])).

tff(c_8218,plain,(
    ! [A_45,B_46,E_228,F_227] : k3_enumset1(A_45,A_45,B_46,E_228,F_227) = k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(E_228,F_227)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8194])).

tff(c_8224,plain,(
    ! [A_45,B_46,E_228,F_227] : k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(E_228,F_227)) = k2_enumset1(A_45,B_46,E_228,F_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8218])).

tff(c_18,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k1_enumset1(A_26,B_27,C_28),k1_tarski(D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8401,plain,(
    ! [B_237,A_239,D_238,C_236,A_240] : k4_enumset1(A_240,B_237,C_236,D_238,A_239,A_239) = k2_xboole_0(k2_enumset1(A_240,B_237,C_236,D_238),k1_tarski(A_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1537])).

tff(c_8417,plain,(
    ! [B_237,C_236,D_238,A_239] : k3_enumset1(B_237,C_236,D_238,A_239,A_239) = k2_xboole_0(k2_enumset1(B_237,B_237,C_236,D_238),k1_tarski(A_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8401,c_32])).

tff(c_9849,plain,(
    ! [B_290,C_291,D_292,A_293] : k3_enumset1(B_290,C_291,D_292,A_293,A_293) = k2_enumset1(B_290,C_291,D_292,A_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28,c_8417])).

tff(c_9859,plain,(
    ! [C_291,D_292,A_293] : k2_enumset1(C_291,D_292,A_293,A_293) = k2_enumset1(C_291,C_291,D_292,A_293) ),
    inference(superposition,[status(thm),theory(equality)],[c_9849,c_30])).

tff(c_9872,plain,(
    ! [C_294,D_295,A_296] : k1_enumset1(C_294,D_295,A_296) = k1_enumset1(A_296,D_295,C_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_28,c_9859])).

tff(c_554,plain,(
    ! [C_49,A_47] : k1_enumset1(C_49,A_47,A_47) = k1_enumset1(A_47,C_49,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_482])).

tff(c_9912,plain,(
    ! [C_294,A_296] : k1_enumset1(C_294,C_294,A_296) = k1_enumset1(C_294,A_296,A_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_9872,c_554])).

tff(c_9979,plain,(
    ! [C_294,A_296] : k1_enumset1(C_294,A_296,A_296) = k2_tarski(C_294,A_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9912])).

tff(c_9991,plain,(
    ! [C_49,A_47] : k2_tarski(C_49,A_47) = k2_tarski(A_47,C_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9979,c_9979,c_554])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1049,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_34])).

tff(c_10042,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9991,c_9991,c_1049])).

tff(c_10799,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8224,c_10042])).

tff(c_10802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_604,c_10,c_10799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/3.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.32  
% 8.22/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.32  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 8.22/3.32  
% 8.22/3.32  %Foreground sorts:
% 8.22/3.32  
% 8.22/3.32  
% 8.22/3.32  %Background operators:
% 8.22/3.32  
% 8.22/3.32  
% 8.22/3.32  %Foreground operators:
% 8.22/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/3.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.22/3.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.22/3.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.22/3.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.22/3.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.22/3.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.22/3.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.22/3.32  tff('#skF_2', type, '#skF_2': $i).
% 8.22/3.32  tff('#skF_3', type, '#skF_3': $i).
% 8.22/3.32  tff('#skF_1', type, '#skF_1': $i).
% 8.22/3.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.22/3.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.22/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/3.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.22/3.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.22/3.32  
% 8.22/3.34  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 8.22/3.34  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 8.22/3.34  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.22/3.34  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 8.22/3.34  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.22/3.34  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.22/3.34  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 8.22/3.34  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 8.22/3.34  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 8.22/3.34  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.22/3.34  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 8.22/3.34  tff(c_584, plain, (![B_97, D_98, C_99, A_100]: (k2_enumset1(B_97, D_98, C_99, A_100)=k2_enumset1(A_100, B_97, C_99, D_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.22/3.34  tff(c_358, plain, (![D_88, C_89, B_90, A_91]: (k2_enumset1(D_88, C_89, B_90, A_91)=k2_enumset1(A_91, B_90, C_89, D_88))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/3.34  tff(c_28, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/3.34  tff(c_414, plain, (![D_88, C_89, B_90]: (k2_enumset1(D_88, C_89, B_90, B_90)=k1_enumset1(B_90, C_89, D_88))), inference(superposition, [status(thm), theory('equality')], [c_358, c_28])).
% 8.22/3.34  tff(c_930, plain, (![B_114, D_115, A_116]: (k2_enumset1(B_114, D_115, D_115, A_116)=k1_enumset1(D_115, B_114, A_116))), inference(superposition, [status(thm), theory('equality')], [c_584, c_414])).
% 8.22/3.34  tff(c_482, plain, (![D_92, C_93, B_94]: (k2_enumset1(D_92, C_93, B_94, B_94)=k1_enumset1(B_94, C_93, D_92))), inference(superposition, [status(thm), theory('equality')], [c_358, c_28])).
% 8.22/3.34  tff(c_10, plain, (![A_10, D_13, C_12, B_11]: (k2_enumset1(A_10, D_13, C_12, B_11)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.22/3.34  tff(c_511, plain, (![D_92, B_94, C_93]: (k2_enumset1(D_92, B_94, B_94, C_93)=k1_enumset1(B_94, C_93, D_92))), inference(superposition, [status(thm), theory('equality')], [c_482, c_10])).
% 8.22/3.34  tff(c_936, plain, (![D_115, B_114, A_116]: (k1_enumset1(D_115, B_114, A_116)=k1_enumset1(D_115, A_116, B_114))), inference(superposition, [status(thm), theory('equality')], [c_930, c_511])).
% 8.22/3.34  tff(c_604, plain, (![A_100, B_97, D_98]: (k2_enumset1(A_100, B_97, A_100, D_98)=k1_enumset1(A_100, D_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_584, c_414])).
% 8.22/3.34  tff(c_30, plain, (![A_50, B_51, C_52, D_53]: (k3_enumset1(A_50, A_50, B_51, C_52, D_53)=k2_enumset1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.22/3.34  tff(c_26, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.22/3.34  tff(c_32, plain, (![C_56, E_58, D_57, B_55, A_54]: (k4_enumset1(A_54, A_54, B_55, C_56, D_57, E_58)=k3_enumset1(A_54, B_55, C_56, D_57, E_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/3.34  tff(c_1537, plain, (![E_138, A_137, C_134, B_135, D_139, F_136]: (k2_xboole_0(k2_enumset1(A_137, B_135, C_134, D_139), k2_tarski(E_138, F_136))=k4_enumset1(A_137, B_135, C_134, D_139, E_138, F_136))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.22/3.34  tff(c_1594, plain, (![E_138, A_47, C_49, F_136, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, E_138, F_136)=k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k2_tarski(E_138, F_136)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1537])).
% 8.22/3.34  tff(c_8194, plain, (![C_230, E_228, F_227, A_226, B_229]: (k2_xboole_0(k1_enumset1(A_226, B_229, C_230), k2_tarski(E_228, F_227))=k3_enumset1(A_226, B_229, C_230, E_228, F_227))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1594])).
% 8.22/3.34  tff(c_8218, plain, (![A_45, B_46, E_228, F_227]: (k3_enumset1(A_45, A_45, B_46, E_228, F_227)=k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(E_228, F_227)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8194])).
% 8.22/3.34  tff(c_8224, plain, (![A_45, B_46, E_228, F_227]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(E_228, F_227))=k2_enumset1(A_45, B_46, E_228, F_227))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8218])).
% 8.22/3.34  tff(c_18, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k1_enumset1(A_26, B_27, C_28), k1_tarski(D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/3.34  tff(c_24, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.22/3.34  tff(c_8401, plain, (![B_237, A_239, D_238, C_236, A_240]: (k4_enumset1(A_240, B_237, C_236, D_238, A_239, A_239)=k2_xboole_0(k2_enumset1(A_240, B_237, C_236, D_238), k1_tarski(A_239)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1537])).
% 8.22/3.34  tff(c_8417, plain, (![B_237, C_236, D_238, A_239]: (k3_enumset1(B_237, C_236, D_238, A_239, A_239)=k2_xboole_0(k2_enumset1(B_237, B_237, C_236, D_238), k1_tarski(A_239)))), inference(superposition, [status(thm), theory('equality')], [c_8401, c_32])).
% 8.22/3.34  tff(c_9849, plain, (![B_290, C_291, D_292, A_293]: (k3_enumset1(B_290, C_291, D_292, A_293, A_293)=k2_enumset1(B_290, C_291, D_292, A_293))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28, c_8417])).
% 8.22/3.34  tff(c_9859, plain, (![C_291, D_292, A_293]: (k2_enumset1(C_291, D_292, A_293, A_293)=k2_enumset1(C_291, C_291, D_292, A_293))), inference(superposition, [status(thm), theory('equality')], [c_9849, c_30])).
% 8.22/3.34  tff(c_9872, plain, (![C_294, D_295, A_296]: (k1_enumset1(C_294, D_295, A_296)=k1_enumset1(A_296, D_295, C_294))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_28, c_9859])).
% 8.22/3.34  tff(c_554, plain, (![C_49, A_47]: (k1_enumset1(C_49, A_47, A_47)=k1_enumset1(A_47, C_49, C_49))), inference(superposition, [status(thm), theory('equality')], [c_28, c_482])).
% 8.22/3.34  tff(c_9912, plain, (![C_294, A_296]: (k1_enumset1(C_294, C_294, A_296)=k1_enumset1(C_294, A_296, A_296))), inference(superposition, [status(thm), theory('equality')], [c_9872, c_554])).
% 8.22/3.34  tff(c_9979, plain, (![C_294, A_296]: (k1_enumset1(C_294, A_296, A_296)=k2_tarski(C_294, A_296))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9912])).
% 8.22/3.34  tff(c_9991, plain, (![C_49, A_47]: (k2_tarski(C_49, A_47)=k2_tarski(A_47, C_49))), inference(demodulation, [status(thm), theory('equality')], [c_9979, c_9979, c_554])).
% 8.22/3.34  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.22/3.34  tff(c_1049, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_936, c_34])).
% 8.22/3.34  tff(c_10042, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9991, c_9991, c_1049])).
% 8.22/3.34  tff(c_10799, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8224, c_10042])).
% 8.22/3.34  tff(c_10802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_936, c_604, c_10, c_10799])).
% 8.22/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.34  
% 8.22/3.34  Inference rules
% 8.22/3.34  ----------------------
% 8.22/3.34  #Ref     : 0
% 8.22/3.34  #Sup     : 2893
% 8.22/3.34  #Fact    : 0
% 8.22/3.34  #Define  : 0
% 8.22/3.34  #Split   : 0
% 8.22/3.34  #Chain   : 0
% 8.22/3.34  #Close   : 0
% 8.22/3.34  
% 8.22/3.34  Ordering : KBO
% 8.22/3.34  
% 8.22/3.34  Simplification rules
% 8.22/3.34  ----------------------
% 8.22/3.34  #Subsume      : 1021
% 8.22/3.34  #Demod        : 1427
% 8.22/3.34  #Tautology    : 1227
% 8.22/3.34  #SimpNegUnit  : 0
% 8.22/3.34  #BackRed      : 4
% 8.22/3.34  
% 8.22/3.34  #Partial instantiations: 0
% 8.22/3.34  #Strategies tried      : 1
% 8.22/3.34  
% 8.22/3.34  Timing (in seconds)
% 8.22/3.34  ----------------------
% 8.22/3.34  Preprocessing        : 0.32
% 8.22/3.34  Parsing              : 0.17
% 8.22/3.34  CNF conversion       : 0.02
% 8.22/3.34  Main loop            : 2.21
% 8.22/3.34  Inferencing          : 0.54
% 8.22/3.34  Reduction            : 1.32
% 8.22/3.34  Demodulation         : 1.23
% 8.22/3.34  BG Simplification    : 0.06
% 8.22/3.34  Subsumption          : 0.21
% 8.22/3.34  Abstraction          : 0.12
% 8.22/3.34  MUC search           : 0.00
% 8.22/3.34  Cooper               : 0.00
% 8.22/3.34  Total                : 2.56
% 8.22/3.34  Index Insertion      : 0.00
% 8.22/3.34  Index Deletion       : 0.00
% 8.22/3.34  Index Matching       : 0.00
% 8.22/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

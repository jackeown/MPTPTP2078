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
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 31.22s
% Output     : CNFRefutation 31.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 520 expanded)
%              Number of leaves         :   21 ( 189 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 ( 506 expanded)
%              Number of equality atoms :   48 ( 505 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k2_xboole_0(k1_tarski(A_15),k2_enumset1(B_16,C_17,D_18,E_19)) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2214,plain,(
    ! [A_80,B_81,C_82] : k2_xboole_0(k1_tarski(A_80),k2_xboole_0(k1_tarski(B_81),C_82)) = k2_xboole_0(k2_tarski(A_80,B_81),C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_2349,plain,(
    ! [D_14,A_80,B_12,A_11,C_13] : k2_xboole_0(k2_tarski(A_80,A_11),k1_enumset1(B_12,C_13,D_14)) = k2_xboole_0(k1_tarski(A_80),k2_enumset1(A_11,B_12,C_13,D_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2214])).

tff(c_2404,plain,(
    ! [D_14,A_80,B_12,A_11,C_13] : k2_xboole_0(k2_tarski(A_80,A_11),k1_enumset1(B_12,C_13,D_14)) = k3_enumset1(A_80,A_11,B_12,C_13,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2349])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [B_34,A_35,B_36] : k2_xboole_0(B_34,k2_xboole_0(A_35,B_36)) = k2_xboole_0(A_35,k2_xboole_0(B_36,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_288,plain,(
    ! [A_8,B_9,C_10,B_34] : k2_xboole_0(k1_tarski(A_8),k2_xboole_0(k2_tarski(B_9,C_10),B_34)) = k2_xboole_0(B_34,k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_211])).

tff(c_181,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k1_tarski(A_31),k2_tarski(B_32,C_33)) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_362,plain,(
    ! [B_37,C_38,A_39] : k2_xboole_0(k2_tarski(B_37,C_38),k1_tarski(A_39)) = k1_enumset1(A_39,B_37,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_166,plain,(
    ! [B_2,A_28,B_29] : k2_xboole_0(B_2,k2_xboole_0(A_28,B_29)) = k2_xboole_0(A_28,k2_xboole_0(B_29,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_33118,plain,(
    ! [A_328,A_329,B_330,C_331] : k2_xboole_0(k1_tarski(A_328),k2_xboole_0(A_329,k2_tarski(B_330,C_331))) = k2_xboole_0(A_329,k1_enumset1(A_328,B_330,C_331)) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_166])).

tff(c_33386,plain,(
    ! [C_331,B_330,A_8,C_10,B_9] : k2_xboole_0(k2_tarski(B_9,C_10),k1_enumset1(A_8,B_330,C_331)) = k2_xboole_0(k2_tarski(B_330,C_331),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_33118])).

tff(c_33581,plain,(
    ! [C_331,B_330,A_8,C_10,B_9] : k3_enumset1(B_9,C_10,A_8,B_330,C_331) = k3_enumset1(B_330,C_331,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2404,c_2404,c_33386])).

tff(c_2368,plain,(
    ! [A_80,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_80,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k1_tarski(A_80),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2214])).

tff(c_2406,plain,(
    ! [A_80,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_80,A_8),k2_tarski(B_9,C_10)) = k2_enumset1(A_80,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2368])).

tff(c_28938,plain,(
    ! [A_312,B_313,C_314,B_315] : k2_xboole_0(k1_tarski(A_312),k2_xboole_0(k2_tarski(B_313,C_314),B_315)) = k2_xboole_0(B_315,k1_enumset1(A_312,B_313,C_314)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_211])).

tff(c_29335,plain,(
    ! [A_312,A_8,C_10,B_9,A_80] : k2_xboole_0(k2_tarski(B_9,C_10),k1_enumset1(A_312,A_80,A_8)) = k2_xboole_0(k1_tarski(A_312),k2_enumset1(A_80,A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_28938])).

tff(c_40835,plain,(
    ! [A_383,A_381,C_385,A_382,B_384] : k3_enumset1(B_384,C_385,A_382,A_381,A_383) = k3_enumset1(A_382,A_381,A_383,B_384,C_385) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2404,c_12,c_29335])).

tff(c_40913,plain,(
    ! [C_331,B_330,A_8,C_10,B_9] : k3_enumset1(B_9,C_10,B_330,C_331,A_8) = k3_enumset1(B_9,C_10,A_8,B_330,C_331) ),
    inference(superposition,[status(thm),theory(equality)],[c_33581,c_40835])).

tff(c_33408,plain,(
    ! [A_8,A_328,C_10,B_9,A_80] : k2_xboole_0(k2_tarski(A_80,A_8),k1_enumset1(A_328,B_9,C_10)) = k2_xboole_0(k1_tarski(A_328),k2_enumset1(A_80,A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_33118])).

tff(c_33586,plain,(
    ! [A_8,A_328,C_10,B_9,A_80] : k3_enumset1(A_80,A_8,A_328,B_9,C_10) = k3_enumset1(A_328,A_80,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2404,c_12,c_33408])).

tff(c_40904,plain,(
    ! [A_8,A_328,C_10,B_9,A_80] : k3_enumset1(A_328,B_9,C_10,A_80,A_8) = k3_enumset1(A_328,A_80,A_8,B_9,C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_33586,c_40835])).

tff(c_535,plain,(
    ! [B_49,E_50,D_48,C_47,A_51] : k2_xboole_0(k1_tarski(A_51),k2_enumset1(B_49,C_47,D_48,E_50)) = k3_enumset1(A_51,B_49,C_47,D_48,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_556,plain,(
    ! [B_49,E_50,D_48,C_47,A_51] : k2_xboole_0(k2_enumset1(B_49,C_47,D_48,E_50),k1_tarski(A_51)) = k3_enumset1(A_51,B_49,C_47,D_48,E_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_2])).

tff(c_499,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_xboole_0(k1_tarski(A_43),k1_enumset1(B_44,C_45,D_46)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_526,plain,(
    ! [B_44,C_45,D_46,A_43] : k2_xboole_0(k1_enumset1(B_44,C_45,D_46),k1_tarski(A_43)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_499])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4698,plain,(
    ! [C_121,C_125,D_122,A_123,B_124] : k2_xboole_0(k1_tarski(A_123),k2_xboole_0(k1_enumset1(B_124,C_121,D_122),C_125)) = k2_xboole_0(k2_enumset1(A_123,B_124,C_121,D_122),C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_4])).

tff(c_4877,plain,(
    ! [A_123,D_46,C_45,A_43,B_44] : k2_xboole_0(k2_enumset1(A_123,B_44,C_45,D_46),k1_tarski(A_43)) = k2_xboole_0(k1_tarski(A_123),k2_enumset1(A_43,B_44,C_45,D_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_4698])).

tff(c_4925,plain,(
    ! [A_123,D_46,C_45,A_43,B_44] : k3_enumset1(A_43,A_123,B_44,C_45,D_46) = k3_enumset1(A_123,A_43,B_44,C_45,D_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_12,c_4877])).

tff(c_40928,plain,(
    ! [A_123,D_46,C_45,A_43,B_44] : k3_enumset1(B_44,C_45,D_46,A_43,A_123) = k3_enumset1(A_123,A_43,B_44,C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_4925,c_40835])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_16,plain,(
    k3_enumset1('#skF_5','#skF_1','#skF_2','#skF_3','#skF_4') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_15])).

tff(c_8405,plain,(
    k3_enumset1('#skF_1','#skF_5','#skF_2','#skF_3','#skF_4') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4925,c_16])).

tff(c_36663,plain,(
    k3_enumset1('#skF_1','#skF_5','#skF_2','#skF_3','#skF_4') != k3_enumset1('#skF_4','#skF_5','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33581,c_8405])).

tff(c_40939,plain,(
    k3_enumset1('#skF_4','#skF_5','#skF_3','#skF_1','#skF_2') != k3_enumset1('#skF_4','#skF_3','#skF_1','#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40928,c_36663])).

tff(c_41811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40913,c_40904,c_40913,c_40904,c_40913,c_40939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.22/22.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.22/22.33  
% 31.22/22.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.22/22.34  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 31.22/22.34  
% 31.22/22.34  %Foreground sorts:
% 31.22/22.34  
% 31.22/22.34  
% 31.22/22.34  %Background operators:
% 31.22/22.34  
% 31.22/22.34  
% 31.22/22.34  %Foreground operators:
% 31.22/22.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.22/22.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.22/22.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 31.22/22.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 31.22/22.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 31.22/22.34  tff('#skF_5', type, '#skF_5': $i).
% 31.22/22.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 31.22/22.34  tff('#skF_2', type, '#skF_2': $i).
% 31.22/22.34  tff('#skF_3', type, '#skF_3': $i).
% 31.22/22.34  tff('#skF_1', type, '#skF_1': $i).
% 31.22/22.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.22/22.34  tff('#skF_4', type, '#skF_4': $i).
% 31.22/22.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.22/22.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.22/22.34  
% 31.22/22.35  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 31.22/22.35  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 31.22/22.35  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 31.22/22.35  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 31.22/22.35  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 31.22/22.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 31.22/22.35  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 31.22/22.35  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k2_xboole_0(k1_tarski(A_15), k2_enumset1(B_16, C_17, D_18, E_19))=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.22/22.35  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.22/22.35  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.22/22.35  tff(c_135, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.22/22.35  tff(c_2214, plain, (![A_80, B_81, C_82]: (k2_xboole_0(k1_tarski(A_80), k2_xboole_0(k1_tarski(B_81), C_82))=k2_xboole_0(k2_tarski(A_80, B_81), C_82))), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 31.22/22.35  tff(c_2349, plain, (![D_14, A_80, B_12, A_11, C_13]: (k2_xboole_0(k2_tarski(A_80, A_11), k1_enumset1(B_12, C_13, D_14))=k2_xboole_0(k1_tarski(A_80), k2_enumset1(A_11, B_12, C_13, D_14)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2214])).
% 31.22/22.35  tff(c_2404, plain, (![D_14, A_80, B_12, A_11, C_13]: (k2_xboole_0(k2_tarski(A_80, A_11), k1_enumset1(B_12, C_13, D_14))=k3_enumset1(A_80, A_11, B_12, C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2349])).
% 31.22/22.35  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.22/22.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 31.22/22.35  tff(c_211, plain, (![B_34, A_35, B_36]: (k2_xboole_0(B_34, k2_xboole_0(A_35, B_36))=k2_xboole_0(A_35, k2_xboole_0(B_36, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 31.22/22.35  tff(c_288, plain, (![A_8, B_9, C_10, B_34]: (k2_xboole_0(k1_tarski(A_8), k2_xboole_0(k2_tarski(B_9, C_10), B_34))=k2_xboole_0(B_34, k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_211])).
% 31.22/22.35  tff(c_181, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k1_tarski(A_31), k2_tarski(B_32, C_33))=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.22/22.35  tff(c_362, plain, (![B_37, C_38, A_39]: (k2_xboole_0(k2_tarski(B_37, C_38), k1_tarski(A_39))=k1_enumset1(A_39, B_37, C_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 31.22/22.35  tff(c_166, plain, (![B_2, A_28, B_29]: (k2_xboole_0(B_2, k2_xboole_0(A_28, B_29))=k2_xboole_0(A_28, k2_xboole_0(B_29, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 31.22/22.35  tff(c_33118, plain, (![A_328, A_329, B_330, C_331]: (k2_xboole_0(k1_tarski(A_328), k2_xboole_0(A_329, k2_tarski(B_330, C_331)))=k2_xboole_0(A_329, k1_enumset1(A_328, B_330, C_331)))), inference(superposition, [status(thm), theory('equality')], [c_362, c_166])).
% 31.22/22.35  tff(c_33386, plain, (![C_331, B_330, A_8, C_10, B_9]: (k2_xboole_0(k2_tarski(B_9, C_10), k1_enumset1(A_8, B_330, C_331))=k2_xboole_0(k2_tarski(B_330, C_331), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_33118])).
% 31.22/22.35  tff(c_33581, plain, (![C_331, B_330, A_8, C_10, B_9]: (k3_enumset1(B_9, C_10, A_8, B_330, C_331)=k3_enumset1(B_330, C_331, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_2404, c_2404, c_33386])).
% 31.22/22.35  tff(c_2368, plain, (![A_80, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_80, A_8), k2_tarski(B_9, C_10))=k2_xboole_0(k1_tarski(A_80), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2214])).
% 31.22/22.35  tff(c_2406, plain, (![A_80, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_80, A_8), k2_tarski(B_9, C_10))=k2_enumset1(A_80, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2368])).
% 31.22/22.35  tff(c_28938, plain, (![A_312, B_313, C_314, B_315]: (k2_xboole_0(k1_tarski(A_312), k2_xboole_0(k2_tarski(B_313, C_314), B_315))=k2_xboole_0(B_315, k1_enumset1(A_312, B_313, C_314)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_211])).
% 31.22/22.35  tff(c_29335, plain, (![A_312, A_8, C_10, B_9, A_80]: (k2_xboole_0(k2_tarski(B_9, C_10), k1_enumset1(A_312, A_80, A_8))=k2_xboole_0(k1_tarski(A_312), k2_enumset1(A_80, A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_2406, c_28938])).
% 31.22/22.35  tff(c_40835, plain, (![A_383, A_381, C_385, A_382, B_384]: (k3_enumset1(B_384, C_385, A_382, A_381, A_383)=k3_enumset1(A_382, A_381, A_383, B_384, C_385))), inference(demodulation, [status(thm), theory('equality')], [c_2404, c_12, c_29335])).
% 31.22/22.35  tff(c_40913, plain, (![C_331, B_330, A_8, C_10, B_9]: (k3_enumset1(B_9, C_10, B_330, C_331, A_8)=k3_enumset1(B_9, C_10, A_8, B_330, C_331))), inference(superposition, [status(thm), theory('equality')], [c_33581, c_40835])).
% 31.22/22.35  tff(c_33408, plain, (![A_8, A_328, C_10, B_9, A_80]: (k2_xboole_0(k2_tarski(A_80, A_8), k1_enumset1(A_328, B_9, C_10))=k2_xboole_0(k1_tarski(A_328), k2_enumset1(A_80, A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_2406, c_33118])).
% 31.22/22.35  tff(c_33586, plain, (![A_8, A_328, C_10, B_9, A_80]: (k3_enumset1(A_80, A_8, A_328, B_9, C_10)=k3_enumset1(A_328, A_80, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_2404, c_12, c_33408])).
% 31.22/22.35  tff(c_40904, plain, (![A_8, A_328, C_10, B_9, A_80]: (k3_enumset1(A_328, B_9, C_10, A_80, A_8)=k3_enumset1(A_328, A_80, A_8, B_9, C_10))), inference(superposition, [status(thm), theory('equality')], [c_33586, c_40835])).
% 31.22/22.35  tff(c_535, plain, (![B_49, E_50, D_48, C_47, A_51]: (k2_xboole_0(k1_tarski(A_51), k2_enumset1(B_49, C_47, D_48, E_50))=k3_enumset1(A_51, B_49, C_47, D_48, E_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.22/22.35  tff(c_556, plain, (![B_49, E_50, D_48, C_47, A_51]: (k2_xboole_0(k2_enumset1(B_49, C_47, D_48, E_50), k1_tarski(A_51))=k3_enumset1(A_51, B_49, C_47, D_48, E_50))), inference(superposition, [status(thm), theory('equality')], [c_535, c_2])).
% 31.22/22.35  tff(c_499, plain, (![A_43, B_44, C_45, D_46]: (k2_xboole_0(k1_tarski(A_43), k1_enumset1(B_44, C_45, D_46))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.22/22.35  tff(c_526, plain, (![B_44, C_45, D_46, A_43]: (k2_xboole_0(k1_enumset1(B_44, C_45, D_46), k1_tarski(A_43))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_499])).
% 31.22/22.35  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.22/22.35  tff(c_4698, plain, (![C_121, C_125, D_122, A_123, B_124]: (k2_xboole_0(k1_tarski(A_123), k2_xboole_0(k1_enumset1(B_124, C_121, D_122), C_125))=k2_xboole_0(k2_enumset1(A_123, B_124, C_121, D_122), C_125))), inference(superposition, [status(thm), theory('equality')], [c_499, c_4])).
% 31.22/22.35  tff(c_4877, plain, (![A_123, D_46, C_45, A_43, B_44]: (k2_xboole_0(k2_enumset1(A_123, B_44, C_45, D_46), k1_tarski(A_43))=k2_xboole_0(k1_tarski(A_123), k2_enumset1(A_43, B_44, C_45, D_46)))), inference(superposition, [status(thm), theory('equality')], [c_526, c_4698])).
% 31.22/22.35  tff(c_4925, plain, (![A_123, D_46, C_45, A_43, B_44]: (k3_enumset1(A_43, A_123, B_44, C_45, D_46)=k3_enumset1(A_123, A_43, B_44, C_45, D_46))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_12, c_4877])).
% 31.22/22.35  tff(c_40928, plain, (![A_123, D_46, C_45, A_43, B_44]: (k3_enumset1(B_44, C_45, D_46, A_43, A_123)=k3_enumset1(A_123, A_43, B_44, C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_4925, c_40835])).
% 31.22/22.35  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 31.22/22.35  tff(c_15, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 31.22/22.35  tff(c_16, plain, (k3_enumset1('#skF_5', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_15])).
% 31.22/22.35  tff(c_8405, plain, (k3_enumset1('#skF_1', '#skF_5', '#skF_2', '#skF_3', '#skF_4')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4925, c_16])).
% 31.22/22.35  tff(c_36663, plain, (k3_enumset1('#skF_1', '#skF_5', '#skF_2', '#skF_3', '#skF_4')!=k3_enumset1('#skF_4', '#skF_5', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33581, c_8405])).
% 31.22/22.35  tff(c_40939, plain, (k3_enumset1('#skF_4', '#skF_5', '#skF_3', '#skF_1', '#skF_2')!=k3_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40928, c_36663])).
% 31.22/22.35  tff(c_41811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40913, c_40904, c_40913, c_40904, c_40913, c_40939])).
% 31.22/22.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.22/22.35  
% 31.22/22.35  Inference rules
% 31.22/22.35  ----------------------
% 31.22/22.35  #Ref     : 0
% 31.22/22.35  #Sup     : 11261
% 31.22/22.35  #Fact    : 0
% 31.22/22.35  #Define  : 0
% 31.22/22.35  #Split   : 0
% 31.22/22.35  #Chain   : 0
% 31.22/22.35  #Close   : 0
% 31.22/22.35  
% 31.22/22.35  Ordering : KBO
% 31.22/22.35  
% 31.22/22.35  Simplification rules
% 31.22/22.35  ----------------------
% 31.22/22.35  #Subsume      : 2316
% 31.22/22.35  #Demod        : 8201
% 31.22/22.35  #Tautology    : 1067
% 31.22/22.35  #SimpNegUnit  : 0
% 31.22/22.35  #BackRed      : 3
% 31.22/22.35  
% 31.22/22.35  #Partial instantiations: 0
% 31.22/22.35  #Strategies tried      : 1
% 31.22/22.35  
% 31.22/22.35  Timing (in seconds)
% 31.22/22.35  ----------------------
% 31.22/22.36  Preprocessing        : 0.26
% 31.22/22.36  Parsing              : 0.14
% 31.22/22.36  CNF conversion       : 0.02
% 31.22/22.36  Main loop            : 21.32
% 31.22/22.36  Inferencing          : 1.70
% 31.22/22.36  Reduction            : 17.84
% 31.22/22.36  Demodulation         : 17.44
% 31.22/22.36  BG Simplification    : 0.35
% 31.22/22.36  Subsumption          : 1.10
% 31.22/22.36  Abstraction          : 0.56
% 31.22/22.36  MUC search           : 0.00
% 31.22/22.36  Cooper               : 0.00
% 31.22/22.36  Total                : 21.61
% 31.22/22.36  Index Insertion      : 0.00
% 31.22/22.36  Index Deletion       : 0.00
% 31.22/22.36  Index Matching       : 0.00
% 31.22/22.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------

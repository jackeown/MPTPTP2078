%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :   40 (  90 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_10,plain,(
    ! [G_17,F_16,D_14,E_15,H_18,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k2_enumset1(E_15,F_16,G_17,H_18)) = k6_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17,H_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k2_xboole_0(k1_tarski(A_28),k2_enumset1(B_29,C_30,D_31,E_32)) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k1_tarski(A_21),k2_tarski(B_22,C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k2_xboole_0(A_50,B_51),C_52) = k2_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_215,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k1_tarski(A_66),k2_xboole_0(k1_tarski(B_67),C_68)) = k2_xboole_0(k2_tarski(A_66,B_67),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_239,plain,(
    ! [A_66,A_19,B_20] : k2_xboole_0(k2_tarski(A_66,A_19),k1_tarski(B_20)) = k2_xboole_0(k1_tarski(A_66),k2_tarski(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_215])).

tff(c_244,plain,(
    ! [A_66,A_19,B_20] : k2_xboole_0(k2_tarski(A_66,A_19),k1_tarski(B_20)) = k1_enumset1(A_66,A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_239])).

tff(c_109,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k1_tarski(A_53),k2_tarski(B_54,C_55)) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_487,plain,(
    ! [A_103,B_104,C_105,C_106] : k2_xboole_0(k1_tarski(A_103),k2_xboole_0(k2_tarski(B_104,C_105),C_106)) = k2_xboole_0(k1_enumset1(A_103,B_104,C_105),C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_4])).

tff(c_505,plain,(
    ! [A_103,A_66,A_19,B_20] : k2_xboole_0(k1_enumset1(A_103,A_66,A_19),k1_tarski(B_20)) = k2_xboole_0(k1_tarski(A_103),k1_enumset1(A_66,A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_487])).

tff(c_510,plain,(
    ! [A_103,A_66,A_19,B_20] : k2_xboole_0(k1_enumset1(A_103,A_66,A_19),k1_tarski(B_20)) = k2_enumset1(A_103,A_66,A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_505])).

tff(c_121,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_xboole_0(k1_tarski(A_56),k1_enumset1(B_57,C_58,D_59)) = k2_enumset1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_573,plain,(
    ! [C_121,D_122,A_123,B_120,C_124] : k2_xboole_0(k1_tarski(A_123),k2_xboole_0(k1_enumset1(B_120,C_121,D_122),C_124)) = k2_xboole_0(k2_enumset1(A_123,B_120,C_121,D_122),C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_594,plain,(
    ! [A_19,A_66,A_123,B_20,A_103] : k2_xboole_0(k2_enumset1(A_123,A_103,A_66,A_19),k1_tarski(B_20)) = k2_xboole_0(k1_tarski(A_123),k2_enumset1(A_103,A_66,A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_573])).

tff(c_598,plain,(
    ! [A_19,A_66,A_123,B_20,A_103] : k2_xboole_0(k2_enumset1(A_123,A_103,A_66,A_19),k1_tarski(B_20)) = k3_enumset1(A_123,A_103,A_66,A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_594])).

tff(c_50,plain,(
    ! [A_47,B_48,C_49] : k5_xboole_0(k5_xboole_0(A_47,B_48),C_49) = k5_xboole_0(A_47,k5_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_284,plain,(
    ! [A_81,B_82,B_83] : k5_xboole_0(A_81,k5_xboole_0(B_82,k4_xboole_0(B_83,k5_xboole_0(A_81,B_82)))) = k2_xboole_0(k5_xboole_0(A_81,B_82),B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_350,plain,(
    ! [A_9,B_10,B_83] : k5_xboole_0(A_9,k5_xboole_0(k4_xboole_0(B_10,A_9),k4_xboole_0(B_83,k2_xboole_0(A_9,B_10)))) = k2_xboole_0(k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)),B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_284])).

tff(c_636,plain,(
    ! [A_136,B_137,B_138] : k5_xboole_0(A_136,k5_xboole_0(k4_xboole_0(B_137,A_136),k4_xboole_0(B_138,k2_xboole_0(A_136,B_137)))) = k2_xboole_0(A_136,k2_xboole_0(B_137,B_138)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8,c_350])).

tff(c_80,plain,(
    ! [A_9,B_10,C_49] : k5_xboole_0(A_9,k5_xboole_0(k4_xboole_0(B_10,A_9),C_49)) = k5_xboole_0(k2_xboole_0(A_9,B_10),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_742,plain,(
    ! [A_139,B_140,B_141] : k5_xboole_0(k2_xboole_0(A_139,B_140),k4_xboole_0(B_141,k2_xboole_0(A_139,B_140))) = k2_xboole_0(A_139,k2_xboole_0(B_140,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_80])).

tff(c_766,plain,(
    ! [A_19,A_66,A_123,B_20,B_141,A_103] : k5_xboole_0(k2_xboole_0(k2_enumset1(A_123,A_103,A_66,A_19),k1_tarski(B_20)),k4_xboole_0(B_141,k3_enumset1(A_123,A_103,A_66,A_19,B_20))) = k2_xboole_0(k2_enumset1(A_123,A_103,A_66,A_19),k2_xboole_0(k1_tarski(B_20),B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_742])).

tff(c_3228,plain,(
    ! [A_260,A_261,B_258,A_262,A_259,B_263] : k2_xboole_0(k2_enumset1(A_261,A_260,A_259,A_262),k2_xboole_0(k1_tarski(B_258),B_263)) = k2_xboole_0(k3_enumset1(A_261,A_260,A_259,A_262,B_258),B_263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_598,c_766])).

tff(c_3300,plain,(
    ! [A_24,A_260,B_25,D_27,C_26,A_261,A_262,A_259] : k2_xboole_0(k3_enumset1(A_261,A_260,A_259,A_262,A_24),k1_enumset1(B_25,C_26,D_27)) = k2_xboole_0(k2_enumset1(A_261,A_260,A_259,A_262),k2_enumset1(A_24,B_25,C_26,D_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3228])).

tff(c_3317,plain,(
    ! [A_24,A_260,B_25,D_27,C_26,A_261,A_262,A_259] : k2_xboole_0(k3_enumset1(A_261,A_260,A_259,A_262,A_24),k1_enumset1(B_25,C_26,D_27)) = k6_enumset1(A_261,A_260,A_259,A_262,A_24,B_25,C_26,D_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3300])).

tff(c_22,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.38  
% 9.57/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.39  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 9.57/3.39  
% 9.57/3.39  %Foreground sorts:
% 9.57/3.39  
% 9.57/3.39  
% 9.57/3.39  %Background operators:
% 9.57/3.39  
% 9.57/3.39  
% 9.57/3.39  %Foreground operators:
% 9.57/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.57/3.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.57/3.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.57/3.39  tff('#skF_7', type, '#skF_7': $i).
% 9.57/3.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.57/3.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.57/3.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.57/3.39  tff('#skF_5', type, '#skF_5': $i).
% 9.57/3.39  tff('#skF_6', type, '#skF_6': $i).
% 9.57/3.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.57/3.39  tff('#skF_2', type, '#skF_2': $i).
% 9.57/3.39  tff('#skF_3', type, '#skF_3': $i).
% 9.57/3.39  tff('#skF_1', type, '#skF_1': $i).
% 9.57/3.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.57/3.39  tff('#skF_8', type, '#skF_8': $i).
% 9.57/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.39  tff('#skF_4', type, '#skF_4': $i).
% 9.57/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.57/3.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.57/3.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.57/3.39  
% 9.57/3.40  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 9.57/3.40  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 9.57/3.40  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.57/3.40  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 9.57/3.40  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 9.57/3.40  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 9.57/3.40  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.57/3.40  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.57/3.40  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 9.57/3.40  tff(c_10, plain, (![G_17, F_16, D_14, E_15, H_18, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k2_enumset1(E_15, F_16, G_17, H_18))=k6_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17, H_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.57/3.40  tff(c_16, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.57/3.40  tff(c_8, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.57/3.40  tff(c_18, plain, (![C_30, E_32, D_31, B_29, A_28]: (k2_xboole_0(k1_tarski(A_28), k2_enumset1(B_29, C_30, D_31, E_32))=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.57/3.40  tff(c_14, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k1_tarski(A_21), k2_tarski(B_22, C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.57/3.40  tff(c_12, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.57/3.40  tff(c_89, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k2_xboole_0(A_50, B_51), C_52)=k2_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.57/3.40  tff(c_215, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k1_tarski(A_66), k2_xboole_0(k1_tarski(B_67), C_68))=k2_xboole_0(k2_tarski(A_66, B_67), C_68))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 9.57/3.40  tff(c_239, plain, (![A_66, A_19, B_20]: (k2_xboole_0(k2_tarski(A_66, A_19), k1_tarski(B_20))=k2_xboole_0(k1_tarski(A_66), k2_tarski(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_215])).
% 9.57/3.40  tff(c_244, plain, (![A_66, A_19, B_20]: (k2_xboole_0(k2_tarski(A_66, A_19), k1_tarski(B_20))=k1_enumset1(A_66, A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_239])).
% 9.57/3.40  tff(c_109, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k1_tarski(A_53), k2_tarski(B_54, C_55))=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.57/3.40  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.57/3.40  tff(c_487, plain, (![A_103, B_104, C_105, C_106]: (k2_xboole_0(k1_tarski(A_103), k2_xboole_0(k2_tarski(B_104, C_105), C_106))=k2_xboole_0(k1_enumset1(A_103, B_104, C_105), C_106))), inference(superposition, [status(thm), theory('equality')], [c_109, c_4])).
% 9.57/3.40  tff(c_505, plain, (![A_103, A_66, A_19, B_20]: (k2_xboole_0(k1_enumset1(A_103, A_66, A_19), k1_tarski(B_20))=k2_xboole_0(k1_tarski(A_103), k1_enumset1(A_66, A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_487])).
% 9.57/3.40  tff(c_510, plain, (![A_103, A_66, A_19, B_20]: (k2_xboole_0(k1_enumset1(A_103, A_66, A_19), k1_tarski(B_20))=k2_enumset1(A_103, A_66, A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_505])).
% 9.57/3.40  tff(c_121, plain, (![A_56, B_57, C_58, D_59]: (k2_xboole_0(k1_tarski(A_56), k1_enumset1(B_57, C_58, D_59))=k2_enumset1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.57/3.40  tff(c_573, plain, (![C_121, D_122, A_123, B_120, C_124]: (k2_xboole_0(k1_tarski(A_123), k2_xboole_0(k1_enumset1(B_120, C_121, D_122), C_124))=k2_xboole_0(k2_enumset1(A_123, B_120, C_121, D_122), C_124))), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 9.57/3.40  tff(c_594, plain, (![A_19, A_66, A_123, B_20, A_103]: (k2_xboole_0(k2_enumset1(A_123, A_103, A_66, A_19), k1_tarski(B_20))=k2_xboole_0(k1_tarski(A_123), k2_enumset1(A_103, A_66, A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_573])).
% 9.57/3.40  tff(c_598, plain, (![A_19, A_66, A_123, B_20, A_103]: (k2_xboole_0(k2_enumset1(A_123, A_103, A_66, A_19), k1_tarski(B_20))=k3_enumset1(A_123, A_103, A_66, A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_594])).
% 9.57/3.40  tff(c_50, plain, (![A_47, B_48, C_49]: (k5_xboole_0(k5_xboole_0(A_47, B_48), C_49)=k5_xboole_0(A_47, k5_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.57/3.40  tff(c_284, plain, (![A_81, B_82, B_83]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k4_xboole_0(B_83, k5_xboole_0(A_81, B_82))))=k2_xboole_0(k5_xboole_0(A_81, B_82), B_83))), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 9.57/3.40  tff(c_350, plain, (![A_9, B_10, B_83]: (k5_xboole_0(A_9, k5_xboole_0(k4_xboole_0(B_10, A_9), k4_xboole_0(B_83, k2_xboole_0(A_9, B_10))))=k2_xboole_0(k5_xboole_0(A_9, k4_xboole_0(B_10, A_9)), B_83))), inference(superposition, [status(thm), theory('equality')], [c_8, c_284])).
% 9.57/3.40  tff(c_636, plain, (![A_136, B_137, B_138]: (k5_xboole_0(A_136, k5_xboole_0(k4_xboole_0(B_137, A_136), k4_xboole_0(B_138, k2_xboole_0(A_136, B_137))))=k2_xboole_0(A_136, k2_xboole_0(B_137, B_138)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8, c_350])).
% 9.57/3.40  tff(c_80, plain, (![A_9, B_10, C_49]: (k5_xboole_0(A_9, k5_xboole_0(k4_xboole_0(B_10, A_9), C_49))=k5_xboole_0(k2_xboole_0(A_9, B_10), C_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_50])).
% 9.57/3.40  tff(c_742, plain, (![A_139, B_140, B_141]: (k5_xboole_0(k2_xboole_0(A_139, B_140), k4_xboole_0(B_141, k2_xboole_0(A_139, B_140)))=k2_xboole_0(A_139, k2_xboole_0(B_140, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_636, c_80])).
% 9.57/3.40  tff(c_766, plain, (![A_19, A_66, A_123, B_20, B_141, A_103]: (k5_xboole_0(k2_xboole_0(k2_enumset1(A_123, A_103, A_66, A_19), k1_tarski(B_20)), k4_xboole_0(B_141, k3_enumset1(A_123, A_103, A_66, A_19, B_20)))=k2_xboole_0(k2_enumset1(A_123, A_103, A_66, A_19), k2_xboole_0(k1_tarski(B_20), B_141)))), inference(superposition, [status(thm), theory('equality')], [c_598, c_742])).
% 9.57/3.40  tff(c_3228, plain, (![A_260, A_261, B_258, A_262, A_259, B_263]: (k2_xboole_0(k2_enumset1(A_261, A_260, A_259, A_262), k2_xboole_0(k1_tarski(B_258), B_263))=k2_xboole_0(k3_enumset1(A_261, A_260, A_259, A_262, B_258), B_263))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_598, c_766])).
% 9.57/3.40  tff(c_3300, plain, (![A_24, A_260, B_25, D_27, C_26, A_261, A_262, A_259]: (k2_xboole_0(k3_enumset1(A_261, A_260, A_259, A_262, A_24), k1_enumset1(B_25, C_26, D_27))=k2_xboole_0(k2_enumset1(A_261, A_260, A_259, A_262), k2_enumset1(A_24, B_25, C_26, D_27)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3228])).
% 9.57/3.40  tff(c_3317, plain, (![A_24, A_260, B_25, D_27, C_26, A_261, A_262, A_259]: (k2_xboole_0(k3_enumset1(A_261, A_260, A_259, A_262, A_24), k1_enumset1(B_25, C_26, D_27))=k6_enumset1(A_261, A_260, A_259, A_262, A_24, B_25, C_26, D_27))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3300])).
% 9.57/3.40  tff(c_22, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.57/3.40  tff(c_7711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3317, c_22])).
% 9.57/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.40  
% 9.57/3.40  Inference rules
% 9.57/3.40  ----------------------
% 9.57/3.40  #Ref     : 0
% 9.57/3.40  #Sup     : 1892
% 9.57/3.40  #Fact    : 0
% 9.57/3.40  #Define  : 0
% 9.57/3.40  #Split   : 0
% 9.57/3.40  #Chain   : 0
% 9.57/3.40  #Close   : 0
% 9.57/3.40  
% 9.57/3.40  Ordering : KBO
% 9.57/3.40  
% 9.57/3.40  Simplification rules
% 9.57/3.40  ----------------------
% 9.57/3.40  #Subsume      : 0
% 9.57/3.40  #Demod        : 4018
% 9.57/3.40  #Tautology    : 810
% 9.57/3.40  #SimpNegUnit  : 0
% 9.57/3.40  #BackRed      : 1
% 9.57/3.40  
% 9.57/3.40  #Partial instantiations: 0
% 9.57/3.40  #Strategies tried      : 1
% 9.57/3.40  
% 9.57/3.40  Timing (in seconds)
% 9.57/3.40  ----------------------
% 9.57/3.40  Preprocessing        : 0.28
% 9.57/3.40  Parsing              : 0.16
% 9.57/3.40  CNF conversion       : 0.02
% 9.57/3.40  Main loop            : 2.36
% 9.57/3.40  Inferencing          : 0.73
% 9.57/3.40  Reduction            : 1.28
% 9.57/3.40  Demodulation         : 1.15
% 9.57/3.40  BG Simplification    : 0.12
% 9.57/3.40  Subsumption          : 0.16
% 9.57/3.40  Abstraction          : 0.25
% 9.57/3.40  MUC search           : 0.00
% 9.57/3.40  Cooper               : 0.00
% 9.57/3.40  Total                : 2.67
% 9.57/3.40  Index Insertion      : 0.00
% 9.57/3.40  Index Deletion       : 0.00
% 9.57/3.40  Index Matching       : 0.00
% 9.57/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

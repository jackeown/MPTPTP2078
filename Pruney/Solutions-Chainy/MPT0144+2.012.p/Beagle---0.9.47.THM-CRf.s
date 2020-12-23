%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 110 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  90 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,G_14] : k2_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11),k1_enumset1(E_12,F_13,G_14)) = k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_15,B_16,C_37] : k2_xboole_0(k1_tarski(A_15),k2_xboole_0(k1_tarski(B_16),C_37)) = k2_xboole_0(k2_tarski(A_15,B_16),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_16,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : k2_xboole_0(k2_tarski(A_24,B_25),k1_enumset1(C_26,D_27,E_28)) = k3_enumset1(A_24,B_25,C_26,D_27,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_60,B_61,C_62,C_63] : k2_xboole_0(k1_tarski(A_60),k2_xboole_0(k2_tarski(B_61,C_62),C_63)) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_414,plain,(
    ! [C_115,A_119,D_120,E_117,A_118,B_116] : k2_xboole_0(k1_enumset1(A_119,A_118,B_116),k1_enumset1(C_115,D_120,E_117)) = k2_xboole_0(k1_tarski(A_119),k3_enumset1(A_118,B_116,C_115,D_120,E_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_78,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k1_tarski(A_41),k1_enumset1(B_42,C_43,D_44)) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [D_44,C_43,A_41,B_42,C_5] : k2_xboole_0(k1_tarski(A_41),k2_xboole_0(k1_enumset1(B_42,C_43,D_44),C_5)) = k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_423,plain,(
    ! [C_115,A_119,D_120,E_117,A_41,A_118,B_116] : k2_xboole_0(k1_tarski(A_41),k2_xboole_0(k1_tarski(A_119),k3_enumset1(A_118,B_116,C_115,D_120,E_117))) = k2_xboole_0(k2_enumset1(A_41,A_119,A_118,B_116),k1_enumset1(C_115,D_120,E_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_84])).

tff(c_432,plain,(
    ! [C_115,A_119,D_120,E_117,A_41,A_118,B_116] : k2_xboole_0(k2_tarski(A_41,A_119),k3_enumset1(A_118,B_116,C_115,D_120,E_117)) = k5_enumset1(A_41,A_119,A_118,B_116,C_115,D_120,E_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_61,c_423])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_tarski(A_20),k1_enumset1(B_21,C_22,D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_108,plain,(
    ! [C_22,A_45,D_23,A_20,B_21] : k2_xboole_0(k2_tarski(A_45,A_20),k1_enumset1(B_21,C_22,D_23)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_20,B_21,C_22,D_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_278,plain,(
    ! [C_89,D_92,B_91,A_93,A_90] : k2_xboole_0(k1_tarski(A_90),k2_enumset1(A_93,B_91,C_89,D_92)) = k3_enumset1(A_90,A_93,B_91,C_89,D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_108])).

tff(c_287,plain,(
    ! [C_89,D_92,A_15,B_91,A_93,A_90] : k2_xboole_0(k2_tarski(A_15,A_90),k2_enumset1(A_93,B_91,C_89,D_92)) = k2_xboole_0(k1_tarski(A_15),k3_enumset1(A_90,A_93,B_91,C_89,D_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_61])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_45,A_17,B_18,C_19] : k2_xboole_0(k2_tarski(A_45,A_17),k2_tarski(B_18,C_19)) = k2_xboole_0(k1_tarski(A_45),k1_enumset1(A_17,B_18,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_118,plain,(
    ! [A_45,A_17,B_18,C_19] : k2_xboole_0(k2_tarski(A_45,A_17),k2_tarski(B_18,C_19)) = k2_enumset1(A_45,A_17,B_18,C_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_132,plain,(
    ! [A_51,A_52,B_53,C_54] : k2_xboole_0(k2_tarski(A_51,A_52),k2_tarski(B_53,C_54)) = k2_enumset1(A_51,A_52,B_53,C_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_296,plain,(
    ! [A_95,C_97,B_96,C_98,A_94] : k2_xboole_0(k2_tarski(A_94,A_95),k2_xboole_0(k2_tarski(B_96,C_98),C_97)) = k2_xboole_0(k2_enumset1(A_94,A_95,B_96,C_98),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_4])).

tff(c_323,plain,(
    ! [A_95,A_45,C_19,B_18,A_17,A_94] : k2_xboole_0(k2_enumset1(A_94,A_95,A_45,A_17),k2_tarski(B_18,C_19)) = k2_xboole_0(k2_tarski(A_94,A_95),k2_enumset1(A_45,A_17,B_18,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_296])).

tff(c_570,plain,(
    ! [A_163,C_162,A_166,A_165,A_161,B_164] : k2_xboole_0(k2_enumset1(A_161,A_166,A_165,A_163),k2_tarski(B_164,C_162)) = k2_xboole_0(k1_tarski(A_161),k3_enumset1(A_166,A_165,A_163,B_164,C_162)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_323])).

tff(c_290,plain,(
    ! [C_89,D_92,B_91,C_5,A_93,A_90] : k2_xboole_0(k1_tarski(A_90),k2_xboole_0(k2_enumset1(A_93,B_91,C_89,D_92),C_5)) = k2_xboole_0(k3_enumset1(A_90,A_93,B_91,C_89,D_92),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_4])).

tff(c_576,plain,(
    ! [A_163,C_162,A_166,A_165,A_161,B_164,A_90] : k2_xboole_0(k1_tarski(A_90),k2_xboole_0(k1_tarski(A_161),k3_enumset1(A_166,A_165,A_163,B_164,C_162))) = k2_xboole_0(k3_enumset1(A_90,A_161,A_166,A_165,A_163),k2_tarski(B_164,C_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_290])).

tff(c_584,plain,(
    ! [A_163,C_162,A_166,A_165,A_161,B_164,A_90] : k2_xboole_0(k3_enumset1(A_90,A_161,A_166,A_165,A_163),k2_tarski(B_164,C_162)) = k5_enumset1(A_90,A_161,A_166,A_165,A_163,B_164,C_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_61,c_576])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:55:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.49  
% 2.91/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.49  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.49  
% 2.91/1.49  %Foreground sorts:
% 2.91/1.49  
% 2.91/1.49  
% 2.91/1.49  %Background operators:
% 2.91/1.49  
% 2.91/1.49  
% 2.91/1.49  %Foreground operators:
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.49  
% 3.04/1.51  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.04/1.51  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.04/1.51  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.04/1.51  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.04/1.51  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.04/1.51  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.04/1.51  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 3.04/1.51  tff(c_8, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, G_14]: (k2_xboole_0(k2_enumset1(A_8, B_9, C_10, D_11), k1_enumset1(E_12, F_13, G_14))=k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.51  tff(c_10, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.51  tff(c_46, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.04/1.51  tff(c_61, plain, (![A_15, B_16, C_37]: (k2_xboole_0(k1_tarski(A_15), k2_xboole_0(k1_tarski(B_16), C_37))=k2_xboole_0(k2_tarski(A_15, B_16), C_37))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 3.04/1.51  tff(c_16, plain, (![A_24, B_25, D_27, C_26, E_28]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_enumset1(C_26, D_27, E_28))=k3_enumset1(A_24, B_25, C_26, D_27, E_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.51  tff(c_66, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_39, C_40))=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.51  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.04/1.51  tff(c_156, plain, (![A_60, B_61, C_62, C_63]: (k2_xboole_0(k1_tarski(A_60), k2_xboole_0(k2_tarski(B_61, C_62), C_63))=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 3.04/1.51  tff(c_414, plain, (![C_115, A_119, D_120, E_117, A_118, B_116]: (k2_xboole_0(k1_enumset1(A_119, A_118, B_116), k1_enumset1(C_115, D_120, E_117))=k2_xboole_0(k1_tarski(A_119), k3_enumset1(A_118, B_116, C_115, D_120, E_117)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 3.04/1.51  tff(c_78, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k1_tarski(A_41), k1_enumset1(B_42, C_43, D_44))=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.51  tff(c_84, plain, (![D_44, C_43, A_41, B_42, C_5]: (k2_xboole_0(k1_tarski(A_41), k2_xboole_0(k1_enumset1(B_42, C_43, D_44), C_5))=k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), C_5))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 3.04/1.51  tff(c_423, plain, (![C_115, A_119, D_120, E_117, A_41, A_118, B_116]: (k2_xboole_0(k1_tarski(A_41), k2_xboole_0(k1_tarski(A_119), k3_enumset1(A_118, B_116, C_115, D_120, E_117)))=k2_xboole_0(k2_enumset1(A_41, A_119, A_118, B_116), k1_enumset1(C_115, D_120, E_117)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_84])).
% 3.04/1.51  tff(c_432, plain, (![C_115, A_119, D_120, E_117, A_41, A_118, B_116]: (k2_xboole_0(k2_tarski(A_41, A_119), k3_enumset1(A_118, B_116, C_115, D_120, E_117))=k5_enumset1(A_41, A_119, A_118, B_116, C_115, D_120, E_117))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_61, c_423])).
% 3.04/1.51  tff(c_14, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_tarski(A_20), k1_enumset1(B_21, C_22, D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.51  tff(c_90, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 3.04/1.51  tff(c_108, plain, (![C_22, A_45, D_23, A_20, B_21]: (k2_xboole_0(k2_tarski(A_45, A_20), k1_enumset1(B_21, C_22, D_23))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_20, B_21, C_22, D_23)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 3.04/1.51  tff(c_278, plain, (![C_89, D_92, B_91, A_93, A_90]: (k2_xboole_0(k1_tarski(A_90), k2_enumset1(A_93, B_91, C_89, D_92))=k3_enumset1(A_90, A_93, B_91, C_89, D_92))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_108])).
% 3.04/1.51  tff(c_287, plain, (![C_89, D_92, A_15, B_91, A_93, A_90]: (k2_xboole_0(k2_tarski(A_15, A_90), k2_enumset1(A_93, B_91, C_89, D_92))=k2_xboole_0(k1_tarski(A_15), k3_enumset1(A_90, A_93, B_91, C_89, D_92)))), inference(superposition, [status(thm), theory('equality')], [c_278, c_61])).
% 3.04/1.51  tff(c_12, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.51  tff(c_111, plain, (![A_45, A_17, B_18, C_19]: (k2_xboole_0(k2_tarski(A_45, A_17), k2_tarski(B_18, C_19))=k2_xboole_0(k1_tarski(A_45), k1_enumset1(A_17, B_18, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 3.04/1.51  tff(c_118, plain, (![A_45, A_17, B_18, C_19]: (k2_xboole_0(k2_tarski(A_45, A_17), k2_tarski(B_18, C_19))=k2_enumset1(A_45, A_17, B_18, C_19))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_111])).
% 3.04/1.51  tff(c_132, plain, (![A_51, A_52, B_53, C_54]: (k2_xboole_0(k2_tarski(A_51, A_52), k2_tarski(B_53, C_54))=k2_enumset1(A_51, A_52, B_53, C_54))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_111])).
% 3.04/1.51  tff(c_296, plain, (![A_95, C_97, B_96, C_98, A_94]: (k2_xboole_0(k2_tarski(A_94, A_95), k2_xboole_0(k2_tarski(B_96, C_98), C_97))=k2_xboole_0(k2_enumset1(A_94, A_95, B_96, C_98), C_97))), inference(superposition, [status(thm), theory('equality')], [c_132, c_4])).
% 3.04/1.51  tff(c_323, plain, (![A_95, A_45, C_19, B_18, A_17, A_94]: (k2_xboole_0(k2_enumset1(A_94, A_95, A_45, A_17), k2_tarski(B_18, C_19))=k2_xboole_0(k2_tarski(A_94, A_95), k2_enumset1(A_45, A_17, B_18, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_296])).
% 3.04/1.51  tff(c_570, plain, (![A_163, C_162, A_166, A_165, A_161, B_164]: (k2_xboole_0(k2_enumset1(A_161, A_166, A_165, A_163), k2_tarski(B_164, C_162))=k2_xboole_0(k1_tarski(A_161), k3_enumset1(A_166, A_165, A_163, B_164, C_162)))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_323])).
% 3.04/1.51  tff(c_290, plain, (![C_89, D_92, B_91, C_5, A_93, A_90]: (k2_xboole_0(k1_tarski(A_90), k2_xboole_0(k2_enumset1(A_93, B_91, C_89, D_92), C_5))=k2_xboole_0(k3_enumset1(A_90, A_93, B_91, C_89, D_92), C_5))), inference(superposition, [status(thm), theory('equality')], [c_278, c_4])).
% 3.04/1.51  tff(c_576, plain, (![A_163, C_162, A_166, A_165, A_161, B_164, A_90]: (k2_xboole_0(k1_tarski(A_90), k2_xboole_0(k1_tarski(A_161), k3_enumset1(A_166, A_165, A_163, B_164, C_162)))=k2_xboole_0(k3_enumset1(A_90, A_161, A_166, A_165, A_163), k2_tarski(B_164, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_570, c_290])).
% 3.04/1.51  tff(c_584, plain, (![A_163, C_162, A_166, A_165, A_161, B_164, A_90]: (k2_xboole_0(k3_enumset1(A_90, A_161, A_166, A_165, A_163), k2_tarski(B_164, C_162))=k5_enumset1(A_90, A_161, A_166, A_165, A_163, B_164, C_162))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_61, c_576])).
% 3.04/1.51  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.51  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_18])).
% 3.04/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.51  
% 3.04/1.51  Inference rules
% 3.04/1.51  ----------------------
% 3.04/1.51  #Ref     : 0
% 3.04/1.51  #Sup     : 161
% 3.04/1.51  #Fact    : 0
% 3.04/1.51  #Define  : 0
% 3.04/1.51  #Split   : 0
% 3.04/1.51  #Chain   : 0
% 3.04/1.51  #Close   : 0
% 3.04/1.51  
% 3.04/1.51  Ordering : KBO
% 3.04/1.51  
% 3.04/1.51  Simplification rules
% 3.04/1.51  ----------------------
% 3.04/1.51  #Subsume      : 0
% 3.04/1.51  #Demod        : 86
% 3.04/1.51  #Tautology    : 85
% 3.04/1.51  #SimpNegUnit  : 0
% 3.04/1.51  #BackRed      : 1
% 3.04/1.51  
% 3.04/1.51  #Partial instantiations: 0
% 3.04/1.51  #Strategies tried      : 1
% 3.04/1.51  
% 3.04/1.51  Timing (in seconds)
% 3.04/1.51  ----------------------
% 3.04/1.51  Preprocessing        : 0.30
% 3.04/1.51  Parsing              : 0.17
% 3.04/1.51  CNF conversion       : 0.02
% 3.04/1.51  Main loop            : 0.37
% 3.04/1.51  Inferencing          : 0.17
% 3.04/1.51  Reduction            : 0.12
% 3.04/1.51  Demodulation         : 0.10
% 3.04/1.51  BG Simplification    : 0.03
% 3.04/1.51  Subsumption          : 0.04
% 3.04/1.51  Abstraction          : 0.03
% 3.04/1.51  MUC search           : 0.00
% 3.04/1.51  Cooper               : 0.00
% 3.04/1.51  Total                : 0.71
% 3.04/1.51  Index Insertion      : 0.00
% 3.04/1.51  Index Deletion       : 0.00
% 3.04/1.51  Index Matching       : 0.00
% 3.04/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

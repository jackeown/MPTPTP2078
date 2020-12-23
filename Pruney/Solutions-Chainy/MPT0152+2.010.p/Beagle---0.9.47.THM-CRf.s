%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   38 (  73 expanded)
%              Number of equality atoms :   37 (  72 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_12,plain,(
    ! [C_22,H_27,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k1_tarski(A_20),k5_enumset1(B_21,C_22,D_23,E_24,F_25,G_26,H_27)) = k6_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26,H_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38,D_39] : k2_xboole_0(k1_tarski(A_36),k1_enumset1(B_37,C_38,D_39)) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [D_70,C_73,C_72,B_71,A_69] : k2_xboole_0(k1_tarski(A_69),k2_xboole_0(k1_enumset1(B_71,C_73,D_70),C_72)) = k2_xboole_0(k2_enumset1(A_69,B_71,C_73,D_70),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_222,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_69,D_16] : k2_xboole_0(k2_enumset1(A_69,A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k2_xboole_0(k1_tarski(A_69),k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_201])).

tff(c_556,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,A_69,D_16] : k2_xboole_0(k2_enumset1(A_69,A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k6_enumset1(A_69,A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_222])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k1_tarski(A_40),k2_xboole_0(k1_tarski(B_41),C_42)) = k2_xboole_0(k2_tarski(A_40,B_41),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_92,plain,(
    ! [A_40,A_4,B_5] : k2_xboole_0(k2_tarski(A_40,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_40),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_97,plain,(
    ! [A_40,A_4,B_5] : k2_xboole_0(k2_tarski(A_40,A_4),k1_tarski(B_5)) = k1_enumset1(A_40,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_44,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k2_tarski(B_34,C_35)) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_57,B_58,C_59,C_60] : k2_xboole_0(k1_tarski(A_57),k2_xboole_0(k2_tarski(B_58,C_59),C_60)) = k2_xboole_0(k1_enumset1(A_57,B_58,C_59),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_152,plain,(
    ! [A_57,A_40,A_4,B_5] : k2_xboole_0(k1_enumset1(A_57,A_40,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_57),k1_enumset1(A_40,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_134])).

tff(c_156,plain,(
    ! [A_57,A_40,A_4,B_5] : k2_xboole_0(k1_enumset1(A_57,A_40,A_4),k1_tarski(B_5)) = k2_enumset1(A_57,A_40,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_152])).

tff(c_50,plain,(
    ! [A_33,B_34,C_35,C_3] : k2_xboole_0(k1_tarski(A_33),k2_xboole_0(k2_tarski(B_34,C_35),C_3)) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_39,plain,(
    ! [A_4,B_5,C_32] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_32)) = k2_xboole_0(k2_tarski(A_4,B_5),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_227,plain,(
    ! [A_74,D_77,B_75,A_78,C_76] : k2_xboole_0(k2_tarski(A_74,A_78),k1_enumset1(B_75,C_76,D_77)) = k2_xboole_0(k1_tarski(A_74),k2_enumset1(A_78,B_75,C_76,D_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_233,plain,(
    ! [A_74,D_77,B_75,A_78,C_76,A_33] : k2_xboole_0(k1_tarski(A_33),k2_xboole_0(k1_tarski(A_74),k2_enumset1(A_78,B_75,C_76,D_77))) = k2_xboole_0(k1_enumset1(A_33,A_74,A_78),k1_enumset1(B_75,C_76,D_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_50])).

tff(c_371,plain,(
    ! [C_110,A_108,D_109,A_111,A_107,B_112] : k2_xboole_0(k1_enumset1(A_107,A_111,A_108),k1_enumset1(B_112,C_110,D_109)) = k2_xboole_0(k2_tarski(A_107,A_111),k2_enumset1(A_108,B_112,C_110,D_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_233])).

tff(c_62,plain,(
    ! [D_39,A_36,C_3,C_38,B_37] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k1_enumset1(B_37,C_38,D_39),C_3)) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_377,plain,(
    ! [C_110,A_108,D_109,A_36,A_111,A_107,B_112] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k2_tarski(A_107,A_111),k2_enumset1(A_108,B_112,C_110,D_109))) = k2_xboole_0(k2_enumset1(A_36,A_107,A_111,A_108),k1_enumset1(B_112,C_110,D_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_62])).

tff(c_409,plain,(
    ! [A_124,B_126,A_122,A_121,A_127,D_125,C_123] : k2_xboole_0(k2_enumset1(A_121,A_127,A_124,A_122),k1_enumset1(B_126,C_123,D_125)) = k5_enumset1(A_121,A_127,A_124,A_122,B_126,C_123,D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50,c_377])).

tff(c_650,plain,(
    ! [A_185,A_178,C_181,D_182,C_183,A_179,A_180,B_184] : k2_xboole_0(k2_enumset1(A_178,A_185,A_179,A_180),k2_xboole_0(k1_enumset1(B_184,C_181,D_182),C_183)) = k2_xboole_0(k5_enumset1(A_178,A_185,A_179,A_180,B_184,C_181,D_182),C_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_2])).

tff(c_680,plain,(
    ! [A_57,B_5,A_185,A_178,A_4,A_40,A_179,A_180] : k2_xboole_0(k5_enumset1(A_178,A_185,A_179,A_180,A_57,A_40,A_4),k1_tarski(B_5)) = k2_xboole_0(k2_enumset1(A_178,A_185,A_179,A_180),k2_enumset1(A_57,A_40,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_650])).

tff(c_687,plain,(
    ! [A_57,B_5,A_185,A_178,A_4,A_40,A_179,A_180] : k2_xboole_0(k5_enumset1(A_178,A_185,A_179,A_180,A_57,A_40,A_4),k1_tarski(B_5)) = k6_enumset1(A_178,A_185,A_179,A_180,A_57,A_40,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_680])).

tff(c_14,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  %$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.48  
% 3.12/1.50  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 3.12/1.50  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 3.12/1.50  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.12/1.50  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.12/1.50  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.12/1.50  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.12/1.50  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 3.12/1.50  tff(c_12, plain, (![C_22, H_27, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k1_tarski(A_20), k5_enumset1(B_21, C_22, D_23, E_24, F_25, G_26, H_27))=k6_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26, H_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.50  tff(c_10, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.50  tff(c_56, plain, (![A_36, B_37, C_38, D_39]: (k2_xboole_0(k1_tarski(A_36), k1_enumset1(B_37, C_38, D_39))=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.50  tff(c_201, plain, (![D_70, C_73, C_72, B_71, A_69]: (k2_xboole_0(k1_tarski(A_69), k2_xboole_0(k1_enumset1(B_71, C_73, D_70), C_72))=k2_xboole_0(k2_enumset1(A_69, B_71, C_73, D_70), C_72))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 3.12/1.50  tff(c_222, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_69, D_16]: (k2_xboole_0(k2_enumset1(A_69, A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k2_xboole_0(k1_tarski(A_69), k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_201])).
% 3.12/1.50  tff(c_556, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, A_69, D_16]: (k2_xboole_0(k2_enumset1(A_69, A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k6_enumset1(A_69, A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_222])).
% 3.12/1.50  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.50  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.50  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.50  tff(c_24, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.50  tff(c_68, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k1_tarski(A_40), k2_xboole_0(k1_tarski(B_41), C_42))=k2_xboole_0(k2_tarski(A_40, B_41), C_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 3.12/1.50  tff(c_92, plain, (![A_40, A_4, B_5]: (k2_xboole_0(k2_tarski(A_40, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_40), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 3.12/1.50  tff(c_97, plain, (![A_40, A_4, B_5]: (k2_xboole_0(k2_tarski(A_40, A_4), k1_tarski(B_5))=k1_enumset1(A_40, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 3.12/1.50  tff(c_44, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(B_34, C_35))=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.50  tff(c_134, plain, (![A_57, B_58, C_59, C_60]: (k2_xboole_0(k1_tarski(A_57), k2_xboole_0(k2_tarski(B_58, C_59), C_60))=k2_xboole_0(k1_enumset1(A_57, B_58, C_59), C_60))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2])).
% 3.12/1.50  tff(c_152, plain, (![A_57, A_40, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_57, A_40, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_57), k1_enumset1(A_40, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_134])).
% 3.12/1.50  tff(c_156, plain, (![A_57, A_40, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_57, A_40, A_4), k1_tarski(B_5))=k2_enumset1(A_57, A_40, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_152])).
% 3.12/1.50  tff(c_50, plain, (![A_33, B_34, C_35, C_3]: (k2_xboole_0(k1_tarski(A_33), k2_xboole_0(k2_tarski(B_34, C_35), C_3))=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), C_3))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2])).
% 3.12/1.50  tff(c_39, plain, (![A_4, B_5, C_32]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_32))=k2_xboole_0(k2_tarski(A_4, B_5), C_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 3.12/1.50  tff(c_227, plain, (![A_74, D_77, B_75, A_78, C_76]: (k2_xboole_0(k2_tarski(A_74, A_78), k1_enumset1(B_75, C_76, D_77))=k2_xboole_0(k1_tarski(A_74), k2_enumset1(A_78, B_75, C_76, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 3.12/1.50  tff(c_233, plain, (![A_74, D_77, B_75, A_78, C_76, A_33]: (k2_xboole_0(k1_tarski(A_33), k2_xboole_0(k1_tarski(A_74), k2_enumset1(A_78, B_75, C_76, D_77)))=k2_xboole_0(k1_enumset1(A_33, A_74, A_78), k1_enumset1(B_75, C_76, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_50])).
% 3.12/1.50  tff(c_371, plain, (![C_110, A_108, D_109, A_111, A_107, B_112]: (k2_xboole_0(k1_enumset1(A_107, A_111, A_108), k1_enumset1(B_112, C_110, D_109))=k2_xboole_0(k2_tarski(A_107, A_111), k2_enumset1(A_108, B_112, C_110, D_109)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_233])).
% 3.12/1.50  tff(c_62, plain, (![D_39, A_36, C_3, C_38, B_37]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k1_enumset1(B_37, C_38, D_39), C_3))=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), C_3))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 3.12/1.50  tff(c_377, plain, (![C_110, A_108, D_109, A_36, A_111, A_107, B_112]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k2_tarski(A_107, A_111), k2_enumset1(A_108, B_112, C_110, D_109)))=k2_xboole_0(k2_enumset1(A_36, A_107, A_111, A_108), k1_enumset1(B_112, C_110, D_109)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_62])).
% 3.12/1.50  tff(c_409, plain, (![A_124, B_126, A_122, A_121, A_127, D_125, C_123]: (k2_xboole_0(k2_enumset1(A_121, A_127, A_124, A_122), k1_enumset1(B_126, C_123, D_125))=k5_enumset1(A_121, A_127, A_124, A_122, B_126, C_123, D_125))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50, c_377])).
% 3.12/1.50  tff(c_650, plain, (![A_185, A_178, C_181, D_182, C_183, A_179, A_180, B_184]: (k2_xboole_0(k2_enumset1(A_178, A_185, A_179, A_180), k2_xboole_0(k1_enumset1(B_184, C_181, D_182), C_183))=k2_xboole_0(k5_enumset1(A_178, A_185, A_179, A_180, B_184, C_181, D_182), C_183))), inference(superposition, [status(thm), theory('equality')], [c_409, c_2])).
% 3.12/1.50  tff(c_680, plain, (![A_57, B_5, A_185, A_178, A_4, A_40, A_179, A_180]: (k2_xboole_0(k5_enumset1(A_178, A_185, A_179, A_180, A_57, A_40, A_4), k1_tarski(B_5))=k2_xboole_0(k2_enumset1(A_178, A_185, A_179, A_180), k2_enumset1(A_57, A_40, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_650])).
% 3.12/1.50  tff(c_687, plain, (![A_57, B_5, A_185, A_178, A_4, A_40, A_179, A_180]: (k2_xboole_0(k5_enumset1(A_178, A_185, A_179, A_180, A_57, A_40, A_4), k1_tarski(B_5))=k6_enumset1(A_178, A_185, A_179, A_180, A_57, A_40, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_680])).
% 3.12/1.50  tff(c_14, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.50  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_687, c_14])).
% 3.12/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  Inference rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Ref     : 0
% 3.12/1.50  #Sup     : 170
% 3.12/1.50  #Fact    : 0
% 3.12/1.50  #Define  : 0
% 3.12/1.50  #Split   : 0
% 3.12/1.50  #Chain   : 0
% 3.12/1.50  #Close   : 0
% 3.12/1.50  
% 3.12/1.50  Ordering : KBO
% 3.12/1.50  
% 3.12/1.50  Simplification rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Subsume      : 0
% 3.12/1.50  #Demod        : 144
% 3.12/1.50  #Tautology    : 101
% 3.12/1.50  #SimpNegUnit  : 0
% 3.12/1.50  #BackRed      : 1
% 3.12/1.50  
% 3.12/1.50  #Partial instantiations: 0
% 3.12/1.50  #Strategies tried      : 1
% 3.12/1.50  
% 3.12/1.50  Timing (in seconds)
% 3.12/1.50  ----------------------
% 3.25/1.50  Preprocessing        : 0.27
% 3.25/1.50  Parsing              : 0.15
% 3.25/1.50  CNF conversion       : 0.02
% 3.25/1.50  Main loop            : 0.46
% 3.25/1.50  Inferencing          : 0.20
% 3.25/1.50  Reduction            : 0.17
% 3.25/1.50  Demodulation         : 0.14
% 3.25/1.50  BG Simplification    : 0.03
% 3.25/1.50  Subsumption          : 0.05
% 3.25/1.50  Abstraction          : 0.04
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.76
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 120 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   40 ( 100 expanded)
%              Number of equality atoms :   39 (  99 expanded)
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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_10,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k1_enumset1(E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_20,B_21,C_37] : k2_xboole_0(k1_tarski(A_20),k2_xboole_0(k1_tarski(B_21),C_37)) = k2_xboole_0(k2_tarski(A_20,B_21),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k2_xboole_0(k1_enumset1(A_8,B_9,C_10),k2_tarski(D_11,E_12)) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_25,B_26,C_27,D_28] : k2_xboole_0(k1_tarski(A_25),k1_enumset1(B_26,C_27,D_28)) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_111,plain,(
    ! [A_45,A_22,B_23,C_24] : k2_xboole_0(k2_tarski(A_45,A_22),k2_tarski(B_23,C_24)) = k2_xboole_0(k1_tarski(A_45),k1_enumset1(A_22,B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_118,plain,(
    ! [A_45,A_22,B_23,C_24] : k2_xboole_0(k2_tarski(A_45,A_22),k2_tarski(B_23,C_24)) = k2_enumset1(A_45,A_22,B_23,C_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_66,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_60,B_61,C_62,C_63] : k2_xboole_0(k1_tarski(A_60),k2_xboole_0(k2_tarski(B_61,C_62),C_63)) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_171,plain,(
    ! [A_60,A_45,A_22,B_23,C_24] : k2_xboole_0(k1_enumset1(A_60,A_45,A_22),k2_tarski(B_23,C_24)) = k2_xboole_0(k1_tarski(A_60),k2_enumset1(A_45,A_22,B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_156])).

tff(c_225,plain,(
    ! [A_74,C_73,A_72,A_75,B_76] : k2_xboole_0(k1_tarski(A_75),k2_enumset1(A_74,A_72,B_76,C_73)) = k3_enumset1(A_75,A_74,A_72,B_76,C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_234,plain,(
    ! [A_74,C_73,A_20,A_72,A_75,B_76] : k2_xboole_0(k2_tarski(A_20,A_75),k2_enumset1(A_74,A_72,B_76,C_73)) = k2_xboole_0(k1_tarski(A_20),k3_enumset1(A_75,A_74,A_72,B_76,C_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_61])).

tff(c_114,plain,(
    ! [A_45,A_20,B_21] : k2_xboole_0(k2_tarski(A_45,A_20),k1_tarski(B_21)) = k2_xboole_0(k1_tarski(A_45),k2_tarski(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_120,plain,(
    ! [A_48,A_49,B_50] : k2_xboole_0(k2_tarski(A_48,A_49),k1_tarski(B_50)) = k1_enumset1(A_48,A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_192,plain,(
    ! [A_68,A_69,B_70,C_71] : k2_xboole_0(k2_tarski(A_68,A_69),k2_xboole_0(k1_tarski(B_70),C_71)) = k2_xboole_0(k1_enumset1(A_68,A_69,B_70),C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_4])).

tff(c_213,plain,(
    ! [A_25,C_27,D_28,A_69,A_68,B_26] : k2_xboole_0(k1_enumset1(A_68,A_69,A_25),k1_enumset1(B_26,C_27,D_28)) = k2_xboole_0(k2_tarski(A_68,A_69),k2_enumset1(A_25,B_26,C_27,D_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_192])).

tff(c_605,plain,(
    ! [A_170,A_167,A_166,D_165,C_168,B_169] : k2_xboole_0(k1_enumset1(A_170,A_167,A_166),k1_enumset1(B_169,C_168,D_165)) = k2_xboole_0(k1_tarski(A_170),k3_enumset1(A_167,A_166,B_169,C_168,D_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_213])).

tff(c_78,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k1_tarski(A_41),k1_enumset1(B_42,C_43,D_44)) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [D_44,C_43,A_41,B_42,C_5] : k2_xboole_0(k1_tarski(A_41),k2_xboole_0(k1_enumset1(B_42,C_43,D_44),C_5)) = k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_617,plain,(
    ! [A_170,A_167,A_166,A_41,D_165,C_168,B_169] : k2_xboole_0(k1_tarski(A_41),k2_xboole_0(k1_tarski(A_170),k3_enumset1(A_167,A_166,B_169,C_168,D_165))) = k2_xboole_0(k2_enumset1(A_41,A_170,A_167,A_166),k1_enumset1(B_169,C_168,D_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_84])).

tff(c_626,plain,(
    ! [A_170,A_167,A_166,A_41,D_165,C_168,B_169] : k2_xboole_0(k2_tarski(A_41,A_170),k3_enumset1(A_167,A_166,B_169,C_168,D_165)) = k5_enumset1(A_41,A_170,A_167,A_166,B_169,C_168,D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_61,c_617])).

tff(c_237,plain,(
    ! [A_74,C_73,A_72,C_5,A_75,B_76] : k2_xboole_0(k1_tarski(A_75),k2_xboole_0(k2_enumset1(A_74,A_72,B_76,C_73),C_5)) = k2_xboole_0(k3_enumset1(A_75,A_74,A_72,B_76,C_73),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_4])).

tff(c_270,plain,(
    ! [D_91,B_92,A_89,C_90,C_93] : k2_xboole_0(k1_tarski(A_89),k2_xboole_0(k1_enumset1(B_92,C_90,D_91),C_93)) = k2_xboole_0(k2_enumset1(A_89,B_92,C_90,D_91),C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_279,plain,(
    ! [D_91,B_92,A_20,A_89,C_90,C_93] : k2_xboole_0(k2_tarski(A_20,A_89),k2_xboole_0(k1_enumset1(B_92,C_90,D_91),C_93)) = k2_xboole_0(k1_tarski(A_20),k2_xboole_0(k2_enumset1(A_89,B_92,C_90,D_91),C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_61])).

tff(c_555,plain,(
    ! [C_158,A_156,C_155,D_153,A_157,B_154] : k2_xboole_0(k2_tarski(A_157,A_156),k2_xboole_0(k1_enumset1(B_154,C_158,D_153),C_155)) = k2_xboole_0(k3_enumset1(A_157,A_156,B_154,C_158,D_153),C_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_279])).

tff(c_585,plain,(
    ! [E_12,D_11,A_8,A_156,C_10,B_9,A_157] : k2_xboole_0(k3_enumset1(A_157,A_156,A_8,B_9,C_10),k2_tarski(D_11,E_12)) = k2_xboole_0(k2_tarski(A_157,A_156),k3_enumset1(A_8,B_9,C_10,D_11,E_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_555])).

tff(c_765,plain,(
    ! [E_12,D_11,A_8,A_156,C_10,B_9,A_157] : k2_xboole_0(k3_enumset1(A_157,A_156,A_8,B_9,C_10),k2_tarski(D_11,E_12)) = k5_enumset1(A_157,A_156,A_8,B_9,C_10,D_11,E_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_585])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.47  
% 2.74/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.47  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.74/1.47  
% 2.74/1.47  %Foreground sorts:
% 2.74/1.47  
% 2.74/1.47  
% 2.74/1.47  %Background operators:
% 2.74/1.47  
% 2.74/1.47  
% 2.74/1.47  %Foreground operators:
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.47  
% 3.17/1.48  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.17/1.48  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.17/1.48  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.17/1.48  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 3.17/1.48  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.17/1.48  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.17/1.48  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 3.17/1.48  tff(c_10, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k1_enumset1(E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.48  tff(c_12, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.48  tff(c_46, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.48  tff(c_61, plain, (![A_20, B_21, C_37]: (k2_xboole_0(k1_tarski(A_20), k2_xboole_0(k1_tarski(B_21), C_37))=k2_xboole_0(k2_tarski(A_20, B_21), C_37))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46])).
% 3.17/1.48  tff(c_8, plain, (![E_12, D_11, A_8, C_10, B_9]: (k2_xboole_0(k1_enumset1(A_8, B_9, C_10), k2_tarski(D_11, E_12))=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.48  tff(c_16, plain, (![A_25, B_26, C_27, D_28]: (k2_xboole_0(k1_tarski(A_25), k1_enumset1(B_26, C_27, D_28))=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.48  tff(c_14, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(B_23, C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.48  tff(c_90, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46])).
% 3.17/1.48  tff(c_111, plain, (![A_45, A_22, B_23, C_24]: (k2_xboole_0(k2_tarski(A_45, A_22), k2_tarski(B_23, C_24))=k2_xboole_0(k1_tarski(A_45), k1_enumset1(A_22, B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 3.17/1.48  tff(c_118, plain, (![A_45, A_22, B_23, C_24]: (k2_xboole_0(k2_tarski(A_45, A_22), k2_tarski(B_23, C_24))=k2_enumset1(A_45, A_22, B_23, C_24))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_111])).
% 3.17/1.48  tff(c_66, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_39, C_40))=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.48  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.48  tff(c_156, plain, (![A_60, B_61, C_62, C_63]: (k2_xboole_0(k1_tarski(A_60), k2_xboole_0(k2_tarski(B_61, C_62), C_63))=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 3.17/1.48  tff(c_171, plain, (![A_60, A_45, A_22, B_23, C_24]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_22), k2_tarski(B_23, C_24))=k2_xboole_0(k1_tarski(A_60), k2_enumset1(A_45, A_22, B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_156])).
% 3.17/1.48  tff(c_225, plain, (![A_74, C_73, A_72, A_75, B_76]: (k2_xboole_0(k1_tarski(A_75), k2_enumset1(A_74, A_72, B_76, C_73))=k3_enumset1(A_75, A_74, A_72, B_76, C_73))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_171])).
% 3.17/1.48  tff(c_234, plain, (![A_74, C_73, A_20, A_72, A_75, B_76]: (k2_xboole_0(k2_tarski(A_20, A_75), k2_enumset1(A_74, A_72, B_76, C_73))=k2_xboole_0(k1_tarski(A_20), k3_enumset1(A_75, A_74, A_72, B_76, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_225, c_61])).
% 3.17/1.48  tff(c_114, plain, (![A_45, A_20, B_21]: (k2_xboole_0(k2_tarski(A_45, A_20), k1_tarski(B_21))=k2_xboole_0(k1_tarski(A_45), k2_tarski(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 3.17/1.48  tff(c_120, plain, (![A_48, A_49, B_50]: (k2_xboole_0(k2_tarski(A_48, A_49), k1_tarski(B_50))=k1_enumset1(A_48, A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_114])).
% 3.17/1.48  tff(c_192, plain, (![A_68, A_69, B_70, C_71]: (k2_xboole_0(k2_tarski(A_68, A_69), k2_xboole_0(k1_tarski(B_70), C_71))=k2_xboole_0(k1_enumset1(A_68, A_69, B_70), C_71))), inference(superposition, [status(thm), theory('equality')], [c_120, c_4])).
% 3.17/1.48  tff(c_213, plain, (![A_25, C_27, D_28, A_69, A_68, B_26]: (k2_xboole_0(k1_enumset1(A_68, A_69, A_25), k1_enumset1(B_26, C_27, D_28))=k2_xboole_0(k2_tarski(A_68, A_69), k2_enumset1(A_25, B_26, C_27, D_28)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_192])).
% 3.17/1.48  tff(c_605, plain, (![A_170, A_167, A_166, D_165, C_168, B_169]: (k2_xboole_0(k1_enumset1(A_170, A_167, A_166), k1_enumset1(B_169, C_168, D_165))=k2_xboole_0(k1_tarski(A_170), k3_enumset1(A_167, A_166, B_169, C_168, D_165)))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_213])).
% 3.17/1.48  tff(c_78, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k1_tarski(A_41), k1_enumset1(B_42, C_43, D_44))=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.48  tff(c_84, plain, (![D_44, C_43, A_41, B_42, C_5]: (k2_xboole_0(k1_tarski(A_41), k2_xboole_0(k1_enumset1(B_42, C_43, D_44), C_5))=k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), C_5))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 3.17/1.48  tff(c_617, plain, (![A_170, A_167, A_166, A_41, D_165, C_168, B_169]: (k2_xboole_0(k1_tarski(A_41), k2_xboole_0(k1_tarski(A_170), k3_enumset1(A_167, A_166, B_169, C_168, D_165)))=k2_xboole_0(k2_enumset1(A_41, A_170, A_167, A_166), k1_enumset1(B_169, C_168, D_165)))), inference(superposition, [status(thm), theory('equality')], [c_605, c_84])).
% 3.17/1.48  tff(c_626, plain, (![A_170, A_167, A_166, A_41, D_165, C_168, B_169]: (k2_xboole_0(k2_tarski(A_41, A_170), k3_enumset1(A_167, A_166, B_169, C_168, D_165))=k5_enumset1(A_41, A_170, A_167, A_166, B_169, C_168, D_165))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_61, c_617])).
% 3.17/1.48  tff(c_237, plain, (![A_74, C_73, A_72, C_5, A_75, B_76]: (k2_xboole_0(k1_tarski(A_75), k2_xboole_0(k2_enumset1(A_74, A_72, B_76, C_73), C_5))=k2_xboole_0(k3_enumset1(A_75, A_74, A_72, B_76, C_73), C_5))), inference(superposition, [status(thm), theory('equality')], [c_225, c_4])).
% 3.17/1.48  tff(c_270, plain, (![D_91, B_92, A_89, C_90, C_93]: (k2_xboole_0(k1_tarski(A_89), k2_xboole_0(k1_enumset1(B_92, C_90, D_91), C_93))=k2_xboole_0(k2_enumset1(A_89, B_92, C_90, D_91), C_93))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 3.17/1.48  tff(c_279, plain, (![D_91, B_92, A_20, A_89, C_90, C_93]: (k2_xboole_0(k2_tarski(A_20, A_89), k2_xboole_0(k1_enumset1(B_92, C_90, D_91), C_93))=k2_xboole_0(k1_tarski(A_20), k2_xboole_0(k2_enumset1(A_89, B_92, C_90, D_91), C_93)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_61])).
% 3.17/1.48  tff(c_555, plain, (![C_158, A_156, C_155, D_153, A_157, B_154]: (k2_xboole_0(k2_tarski(A_157, A_156), k2_xboole_0(k1_enumset1(B_154, C_158, D_153), C_155))=k2_xboole_0(k3_enumset1(A_157, A_156, B_154, C_158, D_153), C_155))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_279])).
% 3.17/1.48  tff(c_585, plain, (![E_12, D_11, A_8, A_156, C_10, B_9, A_157]: (k2_xboole_0(k3_enumset1(A_157, A_156, A_8, B_9, C_10), k2_tarski(D_11, E_12))=k2_xboole_0(k2_tarski(A_157, A_156), k3_enumset1(A_8, B_9, C_10, D_11, E_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_555])).
% 3.17/1.48  tff(c_765, plain, (![E_12, D_11, A_8, A_156, C_10, B_9, A_157]: (k2_xboole_0(k3_enumset1(A_157, A_156, A_8, B_9, C_10), k2_tarski(D_11, E_12))=k5_enumset1(A_157, A_156, A_8, B_9, C_10, D_11, E_12))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_585])).
% 3.17/1.48  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.17/1.48  tff(c_768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_765, c_18])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 193
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 0
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 0
% 3.17/1.48  #Demod        : 113
% 3.17/1.48  #Tautology    : 101
% 3.17/1.48  #SimpNegUnit  : 0
% 3.17/1.48  #BackRed      : 3
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.49  Preprocessing        : 0.28
% 3.17/1.49  Parsing              : 0.16
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.41
% 3.17/1.49  Inferencing          : 0.19
% 3.17/1.49  Reduction            : 0.14
% 3.17/1.49  Demodulation         : 0.12
% 3.17/1.49  BG Simplification    : 0.03
% 3.17/1.49  Subsumption          : 0.04
% 3.17/1.49  Abstraction          : 0.03
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.73
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 (  88 expanded)
%              Number of equality atoms :   42 (  87 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,H_16,F_14,G_15,D_12,A_9] : k2_xboole_0(k2_enumset1(A_9,B_10,C_11,D_12),k2_enumset1(E_13,F_14,G_15,H_16)) = k6_enumset1(A_9,B_10,C_11,D_12,E_13,F_14,G_15,H_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] : k2_xboole_0(k1_tarski(A_31),k3_enumset1(B_32,C_33,D_34,E_35,F_36)) = k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [C_70,D_67,B_68,E_71,A_69] : k2_xboole_0(k1_tarski(A_69),k2_enumset1(B_68,C_70,D_67,E_71)) = k3_enumset1(A_69,B_68,C_70,D_67,E_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_17,B_18,C_46] : k2_xboole_0(k1_tarski(A_17),k2_xboole_0(k1_tarski(B_18),C_46)) = k2_xboole_0(k2_tarski(A_17,B_18),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_204,plain,(
    ! [C_70,D_67,B_68,A_17,E_71,A_69] : k2_xboole_0(k2_tarski(A_17,A_69),k2_enumset1(B_68,C_70,D_67,E_71)) = k2_xboole_0(k1_tarski(A_17),k3_enumset1(A_69,B_68,C_70,D_67,E_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_82])).

tff(c_1175,plain,(
    ! [E_177,A_178,C_180,D_175,A_179,B_176] : k2_xboole_0(k2_tarski(A_178,A_179),k2_enumset1(B_176,C_180,D_175,E_177)) = k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_204])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24,D_25] : k2_xboole_0(k1_tarski(A_22),k1_enumset1(B_23,C_24,D_25)) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k1_tarski(B_55),C_56)) = k2_xboole_0(k2_tarski(A_54,B_55),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_132,plain,(
    ! [A_54,A_19,B_20,C_21] : k2_xboole_0(k2_tarski(A_54,A_19),k2_tarski(B_20,C_21)) = k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_19,B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_186,plain,(
    ! [A_63,A_64,B_65,C_66] : k2_xboole_0(k2_tarski(A_63,A_64),k2_tarski(B_65,C_66)) = k2_enumset1(A_63,A_64,B_65,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [C_3,A_63,C_66,A_64,B_65] : k2_xboole_0(k2_tarski(A_63,A_64),k2_xboole_0(k2_tarski(B_65,C_66),C_3)) = k2_xboole_0(k2_enumset1(A_63,A_64,B_65,C_66),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_1181,plain,(
    ! [E_177,A_178,C_180,A_63,D_175,A_179,A_64,B_176] : k2_xboole_0(k2_enumset1(A_63,A_64,A_178,A_179),k2_enumset1(B_176,C_180,D_175,E_177)) = k2_xboole_0(k2_tarski(A_63,A_64),k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_192])).

tff(c_1204,plain,(
    ! [E_177,A_178,C_180,A_63,D_175,A_179,A_64,B_176] : k2_xboole_0(k2_tarski(A_63,A_64),k4_enumset1(A_178,A_179,B_176,C_180,D_175,E_177)) = k6_enumset1(A_63,A_64,A_178,A_179,B_176,C_180,D_175,E_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1181])).

tff(c_310,plain,(
    ! [B_84,E_85,F_87,D_83,C_88,A_86] : k2_xboole_0(k1_tarski(A_86),k3_enumset1(B_84,C_88,D_83,E_85,F_87)) = k4_enumset1(A_86,B_84,C_88,D_83,E_85,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_316,plain,(
    ! [B_84,E_85,A_17,F_87,D_83,C_88,A_86] : k2_xboole_0(k2_tarski(A_17,A_86),k3_enumset1(B_84,C_88,D_83,E_85,F_87)) = k2_xboole_0(k1_tarski(A_17),k4_enumset1(A_86,B_84,C_88,D_83,E_85,F_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_82])).

tff(c_16,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k2_xboole_0(k1_tarski(A_26),k2_enumset1(B_27,C_28,D_29,E_30)) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_54,A_19,B_20,C_21] : k2_xboole_0(k2_tarski(A_54,A_19),k2_tarski(B_20,C_21)) = k2_enumset1(A_54,A_19,B_20,C_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_87,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k1_tarski(A_47),k2_tarski(B_48,C_49)) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [A_72,B_73,C_74,C_75] : k2_xboole_0(k1_tarski(A_72),k2_xboole_0(k2_tarski(B_73,C_74),C_75)) = k2_xboole_0(k1_enumset1(A_72,B_73,C_74),C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_228,plain,(
    ! [A_19,A_72,C_21,B_20,A_54] : k2_xboole_0(k1_enumset1(A_72,A_54,A_19),k2_tarski(B_20,C_21)) = k2_xboole_0(k1_tarski(A_72),k2_enumset1(A_54,A_19,B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_213])).

tff(c_235,plain,(
    ! [A_19,A_72,C_21,B_20,A_54] : k2_xboole_0(k1_enumset1(A_72,A_54,A_19),k2_tarski(B_20,C_21)) = k3_enumset1(A_72,A_54,A_19,B_20,C_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_129,plain,(
    ! [A_22,B_23,D_25,C_24,A_54] : k2_xboole_0(k2_tarski(A_54,A_22),k1_enumset1(B_23,C_24,D_25)) = k2_xboole_0(k1_tarski(A_54),k2_enumset1(A_22,B_23,C_24,D_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_429,plain,(
    ! [A_116,D_119,B_120,A_118,C_117] : k2_xboole_0(k2_tarski(A_118,A_116),k1_enumset1(B_120,C_117,D_119)) = k3_enumset1(A_118,A_116,B_120,C_117,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_1256,plain,(
    ! [A_191,C_193,B_192,C_195,A_194,D_190] : k2_xboole_0(k2_tarski(A_191,A_194),k2_xboole_0(k1_enumset1(B_192,C_193,D_190),C_195)) = k2_xboole_0(k3_enumset1(A_191,A_194,B_192,C_193,D_190),C_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_2])).

tff(c_1292,plain,(
    ! [A_19,A_191,A_194,A_72,C_21,B_20,A_54] : k2_xboole_0(k3_enumset1(A_191,A_194,A_72,A_54,A_19),k2_tarski(B_20,C_21)) = k2_xboole_0(k2_tarski(A_191,A_194),k3_enumset1(A_72,A_54,A_19,B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_1256])).

tff(c_3191,plain,(
    ! [A_279,A_282,C_278,A_284,B_283,A_280,A_281] : k2_xboole_0(k3_enumset1(A_280,A_279,A_282,A_281,A_284),k2_tarski(B_283,C_278)) = k2_xboole_0(k1_tarski(A_280),k4_enumset1(A_279,A_282,A_281,A_284,B_283,C_278)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_1292])).

tff(c_319,plain,(
    ! [C_3,B_84,E_85,F_87,D_83,C_88,A_86] : k2_xboole_0(k1_tarski(A_86),k2_xboole_0(k3_enumset1(B_84,C_88,D_83,E_85,F_87),C_3)) = k2_xboole_0(k4_enumset1(A_86,B_84,C_88,D_83,E_85,F_87),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_2])).

tff(c_3212,plain,(
    ! [A_279,A_282,C_278,A_284,B_283,A_280,A_281,A_86] : k2_xboole_0(k1_tarski(A_86),k2_xboole_0(k1_tarski(A_280),k4_enumset1(A_279,A_282,A_281,A_284,B_283,C_278))) = k2_xboole_0(k4_enumset1(A_86,A_280,A_279,A_282,A_281,A_284),k2_tarski(B_283,C_278)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3191,c_319])).

tff(c_3234,plain,(
    ! [A_279,A_282,C_278,A_284,B_283,A_280,A_281,A_86] : k2_xboole_0(k4_enumset1(A_86,A_280,A_279,A_282,A_281,A_284),k2_tarski(B_283,C_278)) = k6_enumset1(A_86,A_280,A_279,A_282,A_281,A_284,B_283,C_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_82,c_3212])).

tff(c_20,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3234,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.22  
% 6.07/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.22  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.07/2.22  
% 6.07/2.22  %Foreground sorts:
% 6.07/2.22  
% 6.07/2.22  
% 6.07/2.22  %Background operators:
% 6.07/2.22  
% 6.07/2.22  
% 6.07/2.22  %Foreground operators:
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.07/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.07/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.07/2.22  tff('#skF_7', type, '#skF_7': $i).
% 6.07/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.07/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.07/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.07/2.22  tff('#skF_6', type, '#skF_6': $i).
% 6.07/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.07/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.07/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.07/2.22  tff('#skF_1', type, '#skF_1': $i).
% 6.07/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.07/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.07/2.22  tff('#skF_8', type, '#skF_8': $i).
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.07/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.07/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.07/2.22  
% 6.07/2.24  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 6.07/2.24  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 6.07/2.24  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 6.07/2.24  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.07/2.24  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.07/2.24  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 6.07/2.24  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.07/2.24  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 6.07/2.24  tff(c_8, plain, (![C_11, E_13, B_10, H_16, F_14, G_15, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_9, B_10, C_11, D_12), k2_enumset1(E_13, F_14, G_15, H_16))=k6_enumset1(A_9, B_10, C_11, D_12, E_13, F_14, G_15, H_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.07/2.24  tff(c_18, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k2_xboole_0(k1_tarski(A_31), k3_enumset1(B_32, C_33, D_34, E_35, F_36))=k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.24  tff(c_198, plain, (![C_70, D_67, B_68, E_71, A_69]: (k2_xboole_0(k1_tarski(A_69), k2_enumset1(B_68, C_70, D_67, E_71))=k3_enumset1(A_69, B_68, C_70, D_67, E_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.07/2.24  tff(c_10, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.24  tff(c_67, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.24  tff(c_82, plain, (![A_17, B_18, C_46]: (k2_xboole_0(k1_tarski(A_17), k2_xboole_0(k1_tarski(B_18), C_46))=k2_xboole_0(k2_tarski(A_17, B_18), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 6.07/2.24  tff(c_204, plain, (![C_70, D_67, B_68, A_17, E_71, A_69]: (k2_xboole_0(k2_tarski(A_17, A_69), k2_enumset1(B_68, C_70, D_67, E_71))=k2_xboole_0(k1_tarski(A_17), k3_enumset1(A_69, B_68, C_70, D_67, E_71)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_82])).
% 6.07/2.24  tff(c_1175, plain, (![E_177, A_178, C_180, D_175, A_179, B_176]: (k2_xboole_0(k2_tarski(A_178, A_179), k2_enumset1(B_176, C_180, D_175, E_177))=k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_204])).
% 6.07/2.24  tff(c_14, plain, (![A_22, B_23, C_24, D_25]: (k2_xboole_0(k1_tarski(A_22), k1_enumset1(B_23, C_24, D_25))=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.07/2.24  tff(c_12, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(B_20, C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.24  tff(c_111, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k1_tarski(B_55), C_56))=k2_xboole_0(k2_tarski(A_54, B_55), C_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 6.07/2.24  tff(c_132, plain, (![A_54, A_19, B_20, C_21]: (k2_xboole_0(k2_tarski(A_54, A_19), k2_tarski(B_20, C_21))=k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_19, B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 6.07/2.24  tff(c_186, plain, (![A_63, A_64, B_65, C_66]: (k2_xboole_0(k2_tarski(A_63, A_64), k2_tarski(B_65, C_66))=k2_enumset1(A_63, A_64, B_65, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_132])).
% 6.07/2.24  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.24  tff(c_192, plain, (![C_3, A_63, C_66, A_64, B_65]: (k2_xboole_0(k2_tarski(A_63, A_64), k2_xboole_0(k2_tarski(B_65, C_66), C_3))=k2_xboole_0(k2_enumset1(A_63, A_64, B_65, C_66), C_3))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 6.07/2.24  tff(c_1181, plain, (![E_177, A_178, C_180, A_63, D_175, A_179, A_64, B_176]: (k2_xboole_0(k2_enumset1(A_63, A_64, A_178, A_179), k2_enumset1(B_176, C_180, D_175, E_177))=k2_xboole_0(k2_tarski(A_63, A_64), k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177)))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_192])).
% 6.07/2.24  tff(c_1204, plain, (![E_177, A_178, C_180, A_63, D_175, A_179, A_64, B_176]: (k2_xboole_0(k2_tarski(A_63, A_64), k4_enumset1(A_178, A_179, B_176, C_180, D_175, E_177))=k6_enumset1(A_63, A_64, A_178, A_179, B_176, C_180, D_175, E_177))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1181])).
% 6.07/2.24  tff(c_310, plain, (![B_84, E_85, F_87, D_83, C_88, A_86]: (k2_xboole_0(k1_tarski(A_86), k3_enumset1(B_84, C_88, D_83, E_85, F_87))=k4_enumset1(A_86, B_84, C_88, D_83, E_85, F_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.24  tff(c_316, plain, (![B_84, E_85, A_17, F_87, D_83, C_88, A_86]: (k2_xboole_0(k2_tarski(A_17, A_86), k3_enumset1(B_84, C_88, D_83, E_85, F_87))=k2_xboole_0(k1_tarski(A_17), k4_enumset1(A_86, B_84, C_88, D_83, E_85, F_87)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_82])).
% 6.07/2.24  tff(c_16, plain, (![B_27, D_29, A_26, E_30, C_28]: (k2_xboole_0(k1_tarski(A_26), k2_enumset1(B_27, C_28, D_29, E_30))=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.07/2.24  tff(c_139, plain, (![A_54, A_19, B_20, C_21]: (k2_xboole_0(k2_tarski(A_54, A_19), k2_tarski(B_20, C_21))=k2_enumset1(A_54, A_19, B_20, C_21))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_132])).
% 6.07/2.24  tff(c_87, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(B_48, C_49))=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.24  tff(c_213, plain, (![A_72, B_73, C_74, C_75]: (k2_xboole_0(k1_tarski(A_72), k2_xboole_0(k2_tarski(B_73, C_74), C_75))=k2_xboole_0(k1_enumset1(A_72, B_73, C_74), C_75))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 6.07/2.24  tff(c_228, plain, (![A_19, A_72, C_21, B_20, A_54]: (k2_xboole_0(k1_enumset1(A_72, A_54, A_19), k2_tarski(B_20, C_21))=k2_xboole_0(k1_tarski(A_72), k2_enumset1(A_54, A_19, B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_213])).
% 6.07/2.24  tff(c_235, plain, (![A_19, A_72, C_21, B_20, A_54]: (k2_xboole_0(k1_enumset1(A_72, A_54, A_19), k2_tarski(B_20, C_21))=k3_enumset1(A_72, A_54, A_19, B_20, C_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_228])).
% 6.07/2.24  tff(c_129, plain, (![A_22, B_23, D_25, C_24, A_54]: (k2_xboole_0(k2_tarski(A_54, A_22), k1_enumset1(B_23, C_24, D_25))=k2_xboole_0(k1_tarski(A_54), k2_enumset1(A_22, B_23, C_24, D_25)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_111])).
% 6.07/2.24  tff(c_429, plain, (![A_116, D_119, B_120, A_118, C_117]: (k2_xboole_0(k2_tarski(A_118, A_116), k1_enumset1(B_120, C_117, D_119))=k3_enumset1(A_118, A_116, B_120, C_117, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_129])).
% 6.07/2.24  tff(c_1256, plain, (![A_191, C_193, B_192, C_195, A_194, D_190]: (k2_xboole_0(k2_tarski(A_191, A_194), k2_xboole_0(k1_enumset1(B_192, C_193, D_190), C_195))=k2_xboole_0(k3_enumset1(A_191, A_194, B_192, C_193, D_190), C_195))), inference(superposition, [status(thm), theory('equality')], [c_429, c_2])).
% 6.07/2.24  tff(c_1292, plain, (![A_19, A_191, A_194, A_72, C_21, B_20, A_54]: (k2_xboole_0(k3_enumset1(A_191, A_194, A_72, A_54, A_19), k2_tarski(B_20, C_21))=k2_xboole_0(k2_tarski(A_191, A_194), k3_enumset1(A_72, A_54, A_19, B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_1256])).
% 6.07/2.24  tff(c_3191, plain, (![A_279, A_282, C_278, A_284, B_283, A_280, A_281]: (k2_xboole_0(k3_enumset1(A_280, A_279, A_282, A_281, A_284), k2_tarski(B_283, C_278))=k2_xboole_0(k1_tarski(A_280), k4_enumset1(A_279, A_282, A_281, A_284, B_283, C_278)))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_1292])).
% 6.07/2.24  tff(c_319, plain, (![C_3, B_84, E_85, F_87, D_83, C_88, A_86]: (k2_xboole_0(k1_tarski(A_86), k2_xboole_0(k3_enumset1(B_84, C_88, D_83, E_85, F_87), C_3))=k2_xboole_0(k4_enumset1(A_86, B_84, C_88, D_83, E_85, F_87), C_3))), inference(superposition, [status(thm), theory('equality')], [c_310, c_2])).
% 6.07/2.24  tff(c_3212, plain, (![A_279, A_282, C_278, A_284, B_283, A_280, A_281, A_86]: (k2_xboole_0(k1_tarski(A_86), k2_xboole_0(k1_tarski(A_280), k4_enumset1(A_279, A_282, A_281, A_284, B_283, C_278)))=k2_xboole_0(k4_enumset1(A_86, A_280, A_279, A_282, A_281, A_284), k2_tarski(B_283, C_278)))), inference(superposition, [status(thm), theory('equality')], [c_3191, c_319])).
% 6.07/2.24  tff(c_3234, plain, (![A_279, A_282, C_278, A_284, B_283, A_280, A_281, A_86]: (k2_xboole_0(k4_enumset1(A_86, A_280, A_279, A_282, A_281, A_284), k2_tarski(B_283, C_278))=k6_enumset1(A_86, A_280, A_279, A_282, A_281, A_284, B_283, C_278))), inference(demodulation, [status(thm), theory('equality')], [c_1204, c_82, c_3212])).
% 6.07/2.24  tff(c_20, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.07/2.24  tff(c_3613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3234, c_20])).
% 6.07/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.24  
% 6.07/2.24  Inference rules
% 6.07/2.24  ----------------------
% 6.07/2.24  #Ref     : 0
% 6.07/2.24  #Sup     : 921
% 6.07/2.24  #Fact    : 0
% 6.07/2.24  #Define  : 0
% 6.07/2.24  #Split   : 0
% 6.07/2.24  #Chain   : 0
% 6.07/2.24  #Close   : 0
% 6.07/2.24  
% 6.07/2.24  Ordering : KBO
% 6.07/2.24  
% 6.07/2.24  Simplification rules
% 6.07/2.24  ----------------------
% 6.07/2.24  #Subsume      : 0
% 6.07/2.24  #Demod        : 1644
% 6.07/2.24  #Tautology    : 392
% 6.07/2.24  #SimpNegUnit  : 0
% 6.07/2.24  #BackRed      : 1
% 6.07/2.24  
% 6.07/2.24  #Partial instantiations: 0
% 6.07/2.24  #Strategies tried      : 1
% 6.07/2.24  
% 6.07/2.24  Timing (in seconds)
% 6.07/2.24  ----------------------
% 6.07/2.24  Preprocessing        : 0.29
% 6.07/2.24  Parsing              : 0.16
% 6.07/2.24  CNF conversion       : 0.02
% 6.07/2.24  Main loop            : 1.17
% 6.07/2.24  Inferencing          : 0.41
% 6.07/2.24  Reduction            : 0.56
% 6.07/2.24  Demodulation         : 0.47
% 6.07/2.24  BG Simplification    : 0.07
% 6.07/2.24  Subsumption          : 0.10
% 6.07/2.24  Abstraction          : 0.13
% 6.07/2.24  MUC search           : 0.00
% 6.07/2.24  Cooper               : 0.00
% 6.07/2.24  Total                : 1.49
% 6.07/2.24  Index Insertion      : 0.00
% 6.07/2.24  Index Deletion       : 0.00
% 6.07/2.24  Index Matching       : 0.00
% 6.07/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

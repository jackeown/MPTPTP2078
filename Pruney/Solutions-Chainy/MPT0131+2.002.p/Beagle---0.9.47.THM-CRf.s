%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:40 EST 2020

% Result     : Theorem 47.80s
% Output     : CNFRefutation 47.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 374 expanded)
%              Number of leaves         :   21 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :   67 ( 360 expanded)
%              Number of equality atoms :   66 ( 359 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_533,plain,(
    ! [A_50,B_49,E_51,C_48,D_47] : k2_xboole_0(k1_enumset1(A_50,B_49,C_48),k2_tarski(D_47,E_51)) = k3_enumset1(A_50,B_49,C_48,D_47,E_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_569,plain,(
    ! [A_50,B_49,E_51,C_48,D_47] : k2_xboole_0(k2_tarski(D_47,E_51),k1_enumset1(A_50,B_49,C_48)) = k3_enumset1(A_50,B_49,C_48,D_47,E_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_533])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k2_tarski(D_9,E_10)) = k3_enumset1(A_6,B_7,C_8,D_9,E_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k1_tarski(A_31),k2_tarski(B_32,C_33)) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [A_31,B_32,C_33,C_5] : k2_xboole_0(k1_tarski(A_31),k2_xboole_0(k2_tarski(B_32,C_33),C_5)) = k2_xboole_0(k1_enumset1(A_31,B_32,C_33),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_360,plain,(
    ! [B_37,C_38,A_39] : k2_xboole_0(k2_tarski(B_37,C_38),k1_tarski(A_39)) = k1_enumset1(A_39,B_37,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_133,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [B_2,A_28,B_29] : k2_xboole_0(B_2,k2_xboole_0(A_28,B_29)) = k2_xboole_0(A_28,k2_xboole_0(B_29,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_9400,plain,(
    ! [A_184,A_185,B_186,C_187] : k2_xboole_0(k1_tarski(A_184),k2_xboole_0(A_185,k2_tarski(B_186,C_187))) = k2_xboole_0(A_185,k1_enumset1(A_184,B_186,C_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_164])).

tff(c_9572,plain,(
    ! [C_187,A_31,C_33,B_32,B_186] : k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k2_tarski(B_186,C_187)) = k2_xboole_0(k2_tarski(B_32,C_33),k1_enumset1(A_31,B_186,C_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_9400])).

tff(c_9691,plain,(
    ! [C_187,A_31,C_33,B_32,B_186] : k3_enumset1(A_31,B_32,C_33,B_186,C_187) = k3_enumset1(A_31,B_186,C_187,B_32,C_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_6,c_9572])).

tff(c_497,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k1_tarski(D_46)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_518,plain,(
    ! [D_46,A_43,B_44,C_45] : k2_xboole_0(k1_tarski(D_46),k1_enumset1(A_43,B_44,C_45)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_2])).

tff(c_8,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2137,plain,(
    ! [A_77,B_78,C_79] : k2_xboole_0(k1_tarski(A_77),k2_xboole_0(k1_tarski(B_78),C_79)) = k2_xboole_0(k2_tarski(A_77,B_78),C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_133])).

tff(c_2269,plain,(
    ! [A_77,D_46,C_45,A_43,B_44] : k2_xboole_0(k2_tarski(A_77,D_46),k1_enumset1(A_43,B_44,C_45)) = k2_xboole_0(k1_tarski(A_77),k2_enumset1(A_43,B_44,C_45,D_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_2137])).

tff(c_66810,plain,(
    ! [A_77,D_46,C_45,A_43,B_44] : k2_xboole_0(k1_tarski(A_77),k2_enumset1(A_43,B_44,C_45,D_46)) = k3_enumset1(A_43,B_44,C_45,A_77,D_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_2269])).

tff(c_4776,plain,(
    ! [C_121,C_125,D_122,A_123,B_124] : k2_xboole_0(k1_enumset1(A_123,B_124,C_121),k2_xboole_0(k1_tarski(D_122),C_125)) = k2_xboole_0(k2_enumset1(A_123,B_124,C_121,D_122),C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_4])).

tff(c_4986,plain,(
    ! [C_121,A_123,B_124,B_12,A_11] : k2_xboole_0(k2_enumset1(A_123,B_124,C_121,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_enumset1(A_123,B_124,C_121),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4776])).

tff(c_35696,plain,(
    ! [A_326,B_327,C_330,A_328,B_329] : k2_xboole_0(k2_enumset1(A_326,B_327,C_330,A_328),k1_tarski(B_329)) = k3_enumset1(A_326,B_327,C_330,A_328,B_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4986])).

tff(c_48,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [B_23,A_22] : k2_xboole_0(k1_tarski(B_23),k1_tarski(A_22)) = k2_tarski(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_4983,plain,(
    ! [C_121,A_123,B_124,A_22,B_23] : k2_xboole_0(k2_enumset1(A_123,B_124,C_121,B_23),k1_tarski(A_22)) = k2_xboole_0(k1_enumset1(A_123,B_124,C_121),k2_tarski(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4776])).

tff(c_5022,plain,(
    ! [C_121,A_123,B_124,A_22,B_23] : k2_xboole_0(k2_enumset1(A_123,B_124,C_121,B_23),k1_tarski(A_22)) = k3_enumset1(A_123,B_124,C_121,A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4983])).

tff(c_35708,plain,(
    ! [A_326,B_327,C_330,A_328,B_329] : k3_enumset1(A_326,B_327,C_330,B_329,A_328) = k3_enumset1(A_326,B_327,C_330,A_328,B_329) ),
    inference(superposition,[status(thm),theory(equality)],[c_35696,c_5022])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_366,plain,(
    ! [B_37,C_38,A_39,B_2] : k2_xboole_0(k2_tarski(B_37,C_38),k2_xboole_0(k1_tarski(A_39),B_2)) = k2_xboole_0(B_2,k1_enumset1(A_39,B_37,C_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_164])).

tff(c_157,plain,(
    ! [A_11,B_12,C_30] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k1_tarski(B_12),C_30)) = k2_xboole_0(k2_tarski(A_11,B_12),C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_133])).

tff(c_2212,plain,(
    ! [A_77,A_11,B_12,C_30] : k2_xboole_0(k2_tarski(A_77,A_11),k2_xboole_0(k1_tarski(B_12),C_30)) = k2_xboole_0(k1_tarski(A_77),k2_xboole_0(k2_tarski(A_11,B_12),C_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2137])).

tff(c_46964,plain,(
    ! [A_398,A_399,B_400,C_401] : k2_xboole_0(k1_enumset1(A_398,A_399,B_400),C_401) = k2_xboole_0(C_401,k1_enumset1(B_400,A_398,A_399)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_185,c_2212])).

tff(c_2308,plain,(
    ! [B_78,C_79,A_77] : k2_xboole_0(k2_xboole_0(k1_tarski(B_78),C_79),k1_tarski(A_77)) = k2_xboole_0(k2_tarski(A_77,B_78),C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2137])).

tff(c_47482,plain,(
    ! [B_78,A_77,B_400,A_399,A_398] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_398,A_399,B_400),k1_tarski(B_78)),k1_tarski(A_77)) = k2_xboole_0(k2_tarski(A_77,B_78),k1_enumset1(B_400,A_398,A_399)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46964,c_2308])).

tff(c_48074,plain,(
    ! [B_78,A_77,B_400,A_399,A_398] : k3_enumset1(B_400,A_398,A_399,A_77,B_78) = k3_enumset1(A_398,A_399,B_400,A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5022,c_569,c_12,c_47482])).

tff(c_206,plain,(
    ! [B_32,C_33,A_31] : k2_xboole_0(k2_tarski(B_32,C_33),k1_tarski(A_31)) = k1_enumset1(A_31,B_32,C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_2904,plain,(
    ! [A_92,B_93,C_94,C_95] : k2_xboole_0(k1_tarski(A_92),k2_xboole_0(k2_tarski(B_93,C_94),C_95)) = k2_xboole_0(k1_enumset1(A_92,B_93,C_94),C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_3037,plain,(
    ! [A_92,B_32,C_33,A_31] : k2_xboole_0(k1_enumset1(A_92,B_32,C_33),k1_tarski(A_31)) = k2_xboole_0(k1_tarski(A_92),k1_enumset1(A_31,B_32,C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2904])).

tff(c_3089,plain,(
    ! [A_92,B_32,C_33,A_31] : k2_enumset1(A_92,B_32,C_33,A_31) = k2_enumset1(A_31,B_32,C_33,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_12,c_3037])).

tff(c_69,plain,(
    ! [B_24,A_25] : k2_xboole_0(k1_tarski(B_24),k1_tarski(A_25)) = k2_tarski(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_75,plain,(
    ! [B_24,A_25] : k2_tarski(B_24,A_25) = k2_tarski(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_3126,plain,(
    ! [A_100,B_101,A_102] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(A_102)) = k1_enumset1(A_102,B_101,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_360])).

tff(c_3132,plain,(
    ! [A_31,A_100,B_101,A_102] : k2_xboole_0(k1_enumset1(A_31,A_100,B_101),k1_tarski(A_102)) = k2_xboole_0(k1_tarski(A_31),k1_enumset1(A_102,B_101,A_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3126,c_185])).

tff(c_4715,plain,(
    ! [A_120,B_119,A_118,A_117] : k2_enumset1(A_120,B_119,A_118,A_117) = k2_enumset1(A_117,A_118,B_119,A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_12,c_3132])).

tff(c_4757,plain,(
    ! [A_92,C_33,B_32,A_31] : k2_enumset1(A_92,C_33,B_32,A_31) = k2_enumset1(A_92,B_32,C_33,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_3089,c_4715])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2291,plain,(
    ! [A_77,B_23,A_22] : k2_xboole_0(k2_tarski(A_77,B_23),k1_tarski(A_22)) = k2_xboole_0(k1_tarski(A_77),k2_tarski(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2137])).

tff(c_2328,plain,(
    ! [A_81,A_80,B_82] : k1_enumset1(A_81,A_80,B_82) = k1_enumset1(A_80,A_81,B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_10,c_2291])).

tff(c_7704,plain,(
    ! [A_164,A_165,B_166,D_167] : k2_xboole_0(k1_enumset1(A_164,A_165,B_166),k1_tarski(D_167)) = k2_enumset1(A_165,A_164,B_166,D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_2328,c_12])).

tff(c_7752,plain,(
    ! [A_165,A_164,B_166,D_167] : k2_enumset1(A_165,A_164,B_166,D_167) = k2_enumset1(A_164,A_165,B_166,D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_7704,c_12])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5024,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_14])).

tff(c_9019,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7752,c_5024])).

tff(c_9020,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_9019])).

tff(c_40251,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5')) != k3_enumset1('#skF_1','#skF_4','#skF_5','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9691,c_9020])).

tff(c_42403,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5')) != k3_enumset1('#skF_1','#skF_4','#skF_5','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35708,c_40251])).

tff(c_54403,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5')) != k3_enumset1('#skF_4','#skF_5','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48074,c_42403])).

tff(c_54404,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5')) != k3_enumset1('#skF_4','#skF_1','#skF_5','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9691,c_35708,c_9691,c_54403])).

tff(c_66811,plain,(
    k3_enumset1('#skF_4','#skF_3','#skF_2','#skF_1','#skF_5') != k3_enumset1('#skF_4','#skF_1','#skF_5','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66810,c_54404])).

tff(c_66814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9691,c_66811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.80/38.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.80/38.51  
% 47.80/38.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.80/38.51  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 47.80/38.51  
% 47.80/38.51  %Foreground sorts:
% 47.80/38.51  
% 47.80/38.51  
% 47.80/38.51  %Background operators:
% 47.80/38.51  
% 47.80/38.51  
% 47.80/38.51  %Foreground operators:
% 47.80/38.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.80/38.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 47.80/38.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 47.80/38.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 47.80/38.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 47.80/38.51  tff('#skF_5', type, '#skF_5': $i).
% 47.80/38.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 47.80/38.51  tff('#skF_2', type, '#skF_2': $i).
% 47.80/38.51  tff('#skF_3', type, '#skF_3': $i).
% 47.80/38.51  tff('#skF_1', type, '#skF_1': $i).
% 47.80/38.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.80/38.51  tff('#skF_4', type, '#skF_4': $i).
% 47.80/38.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.80/38.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 47.80/38.51  
% 47.80/38.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 47.80/38.53  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 47.80/38.53  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 47.80/38.53  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 47.80/38.53  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 47.80/38.53  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 47.80/38.53  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 47.80/38.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 47.80/38.53  tff(c_533, plain, (![A_50, B_49, E_51, C_48, D_47]: (k2_xboole_0(k1_enumset1(A_50, B_49, C_48), k2_tarski(D_47, E_51))=k3_enumset1(A_50, B_49, C_48, D_47, E_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.80/38.53  tff(c_569, plain, (![A_50, B_49, E_51, C_48, D_47]: (k2_xboole_0(k2_tarski(D_47, E_51), k1_enumset1(A_50, B_49, C_48))=k3_enumset1(A_50, B_49, C_48, D_47, E_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_533])).
% 47.80/38.53  tff(c_6, plain, (![B_7, D_9, C_8, E_10, A_6]: (k2_xboole_0(k1_enumset1(A_6, B_7, C_8), k2_tarski(D_9, E_10))=k3_enumset1(A_6, B_7, C_8, D_9, E_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.80/38.53  tff(c_179, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k1_tarski(A_31), k2_tarski(B_32, C_33))=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 47.80/38.53  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 47.80/38.53  tff(c_185, plain, (![A_31, B_32, C_33, C_5]: (k2_xboole_0(k1_tarski(A_31), k2_xboole_0(k2_tarski(B_32, C_33), C_5))=k2_xboole_0(k1_enumset1(A_31, B_32, C_33), C_5))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 47.80/38.53  tff(c_360, plain, (![B_37, C_38, A_39]: (k2_xboole_0(k2_tarski(B_37, C_38), k1_tarski(A_39))=k1_enumset1(A_39, B_37, C_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 47.80/38.53  tff(c_133, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 47.80/38.53  tff(c_164, plain, (![B_2, A_28, B_29]: (k2_xboole_0(B_2, k2_xboole_0(A_28, B_29))=k2_xboole_0(A_28, k2_xboole_0(B_29, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 47.80/38.53  tff(c_9400, plain, (![A_184, A_185, B_186, C_187]: (k2_xboole_0(k1_tarski(A_184), k2_xboole_0(A_185, k2_tarski(B_186, C_187)))=k2_xboole_0(A_185, k1_enumset1(A_184, B_186, C_187)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_164])).
% 47.80/38.53  tff(c_9572, plain, (![C_187, A_31, C_33, B_32, B_186]: (k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k2_tarski(B_186, C_187))=k2_xboole_0(k2_tarski(B_32, C_33), k1_enumset1(A_31, B_186, C_187)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_9400])).
% 47.80/38.53  tff(c_9691, plain, (![C_187, A_31, C_33, B_32, B_186]: (k3_enumset1(A_31, B_32, C_33, B_186, C_187)=k3_enumset1(A_31, B_186, C_187, B_32, C_33))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_6, c_9572])).
% 47.80/38.53  tff(c_497, plain, (![A_43, B_44, C_45, D_46]: (k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k1_tarski(D_46))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 47.80/38.53  tff(c_518, plain, (![D_46, A_43, B_44, C_45]: (k2_xboole_0(k1_tarski(D_46), k1_enumset1(A_43, B_44, C_45))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_497, c_2])).
% 47.80/38.53  tff(c_8, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 47.80/38.53  tff(c_2137, plain, (![A_77, B_78, C_79]: (k2_xboole_0(k1_tarski(A_77), k2_xboole_0(k1_tarski(B_78), C_79))=k2_xboole_0(k2_tarski(A_77, B_78), C_79))), inference(superposition, [status(thm), theory('equality')], [c_8, c_133])).
% 47.80/38.53  tff(c_2269, plain, (![A_77, D_46, C_45, A_43, B_44]: (k2_xboole_0(k2_tarski(A_77, D_46), k1_enumset1(A_43, B_44, C_45))=k2_xboole_0(k1_tarski(A_77), k2_enumset1(A_43, B_44, C_45, D_46)))), inference(superposition, [status(thm), theory('equality')], [c_518, c_2137])).
% 47.80/38.53  tff(c_66810, plain, (![A_77, D_46, C_45, A_43, B_44]: (k2_xboole_0(k1_tarski(A_77), k2_enumset1(A_43, B_44, C_45, D_46))=k3_enumset1(A_43, B_44, C_45, A_77, D_46))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_2269])).
% 47.80/38.53  tff(c_4776, plain, (![C_121, C_125, D_122, A_123, B_124]: (k2_xboole_0(k1_enumset1(A_123, B_124, C_121), k2_xboole_0(k1_tarski(D_122), C_125))=k2_xboole_0(k2_enumset1(A_123, B_124, C_121, D_122), C_125))), inference(superposition, [status(thm), theory('equality')], [c_497, c_4])).
% 47.80/38.53  tff(c_4986, plain, (![C_121, A_123, B_124, B_12, A_11]: (k2_xboole_0(k2_enumset1(A_123, B_124, C_121, A_11), k1_tarski(B_12))=k2_xboole_0(k1_enumset1(A_123, B_124, C_121), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4776])).
% 47.80/38.53  tff(c_35696, plain, (![A_326, B_327, C_330, A_328, B_329]: (k2_xboole_0(k2_enumset1(A_326, B_327, C_330, A_328), k1_tarski(B_329))=k3_enumset1(A_326, B_327, C_330, A_328, B_329))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4986])).
% 47.80/38.53  tff(c_48, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 47.80/38.53  tff(c_54, plain, (![B_23, A_22]: (k2_xboole_0(k1_tarski(B_23), k1_tarski(A_22))=k2_tarski(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 47.80/38.53  tff(c_4983, plain, (![C_121, A_123, B_124, A_22, B_23]: (k2_xboole_0(k2_enumset1(A_123, B_124, C_121, B_23), k1_tarski(A_22))=k2_xboole_0(k1_enumset1(A_123, B_124, C_121), k2_tarski(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4776])).
% 47.80/38.53  tff(c_5022, plain, (![C_121, A_123, B_124, A_22, B_23]: (k2_xboole_0(k2_enumset1(A_123, B_124, C_121, B_23), k1_tarski(A_22))=k3_enumset1(A_123, B_124, C_121, A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4983])).
% 47.80/38.53  tff(c_35708, plain, (![A_326, B_327, C_330, A_328, B_329]: (k3_enumset1(A_326, B_327, C_330, B_329, A_328)=k3_enumset1(A_326, B_327, C_330, A_328, B_329))), inference(superposition, [status(thm), theory('equality')], [c_35696, c_5022])).
% 47.80/38.53  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 47.80/38.53  tff(c_366, plain, (![B_37, C_38, A_39, B_2]: (k2_xboole_0(k2_tarski(B_37, C_38), k2_xboole_0(k1_tarski(A_39), B_2))=k2_xboole_0(B_2, k1_enumset1(A_39, B_37, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_164])).
% 47.80/38.53  tff(c_157, plain, (![A_11, B_12, C_30]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k1_tarski(B_12), C_30))=k2_xboole_0(k2_tarski(A_11, B_12), C_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_133])).
% 47.80/38.53  tff(c_2212, plain, (![A_77, A_11, B_12, C_30]: (k2_xboole_0(k2_tarski(A_77, A_11), k2_xboole_0(k1_tarski(B_12), C_30))=k2_xboole_0(k1_tarski(A_77), k2_xboole_0(k2_tarski(A_11, B_12), C_30)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2137])).
% 47.80/38.53  tff(c_46964, plain, (![A_398, A_399, B_400, C_401]: (k2_xboole_0(k1_enumset1(A_398, A_399, B_400), C_401)=k2_xboole_0(C_401, k1_enumset1(B_400, A_398, A_399)))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_185, c_2212])).
% 47.80/38.53  tff(c_2308, plain, (![B_78, C_79, A_77]: (k2_xboole_0(k2_xboole_0(k1_tarski(B_78), C_79), k1_tarski(A_77))=k2_xboole_0(k2_tarski(A_77, B_78), C_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2137])).
% 47.80/38.53  tff(c_47482, plain, (![B_78, A_77, B_400, A_399, A_398]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_398, A_399, B_400), k1_tarski(B_78)), k1_tarski(A_77))=k2_xboole_0(k2_tarski(A_77, B_78), k1_enumset1(B_400, A_398, A_399)))), inference(superposition, [status(thm), theory('equality')], [c_46964, c_2308])).
% 47.80/38.53  tff(c_48074, plain, (![B_78, A_77, B_400, A_399, A_398]: (k3_enumset1(B_400, A_398, A_399, A_77, B_78)=k3_enumset1(A_398, A_399, B_400, A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_5022, c_569, c_12, c_47482])).
% 47.80/38.53  tff(c_206, plain, (![B_32, C_33, A_31]: (k2_xboole_0(k2_tarski(B_32, C_33), k1_tarski(A_31))=k1_enumset1(A_31, B_32, C_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 47.80/38.53  tff(c_2904, plain, (![A_92, B_93, C_94, C_95]: (k2_xboole_0(k1_tarski(A_92), k2_xboole_0(k2_tarski(B_93, C_94), C_95))=k2_xboole_0(k1_enumset1(A_92, B_93, C_94), C_95))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 47.80/38.53  tff(c_3037, plain, (![A_92, B_32, C_33, A_31]: (k2_xboole_0(k1_enumset1(A_92, B_32, C_33), k1_tarski(A_31))=k2_xboole_0(k1_tarski(A_92), k1_enumset1(A_31, B_32, C_33)))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2904])).
% 47.80/38.53  tff(c_3089, plain, (![A_92, B_32, C_33, A_31]: (k2_enumset1(A_92, B_32, C_33, A_31)=k2_enumset1(A_31, B_32, C_33, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_12, c_3037])).
% 47.80/38.53  tff(c_69, plain, (![B_24, A_25]: (k2_xboole_0(k1_tarski(B_24), k1_tarski(A_25))=k2_tarski(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 47.80/38.53  tff(c_75, plain, (![B_24, A_25]: (k2_tarski(B_24, A_25)=k2_tarski(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_69, c_8])).
% 47.80/38.53  tff(c_3126, plain, (![A_100, B_101, A_102]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(A_102))=k1_enumset1(A_102, B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_75, c_360])).
% 47.80/38.53  tff(c_3132, plain, (![A_31, A_100, B_101, A_102]: (k2_xboole_0(k1_enumset1(A_31, A_100, B_101), k1_tarski(A_102))=k2_xboole_0(k1_tarski(A_31), k1_enumset1(A_102, B_101, A_100)))), inference(superposition, [status(thm), theory('equality')], [c_3126, c_185])).
% 47.80/38.53  tff(c_4715, plain, (![A_120, B_119, A_118, A_117]: (k2_enumset1(A_120, B_119, A_118, A_117)=k2_enumset1(A_117, A_118, B_119, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_12, c_3132])).
% 47.80/38.53  tff(c_4757, plain, (![A_92, C_33, B_32, A_31]: (k2_enumset1(A_92, C_33, B_32, A_31)=k2_enumset1(A_92, B_32, C_33, A_31))), inference(superposition, [status(thm), theory('equality')], [c_3089, c_4715])).
% 47.80/38.53  tff(c_10, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 47.80/38.53  tff(c_2291, plain, (![A_77, B_23, A_22]: (k2_xboole_0(k2_tarski(A_77, B_23), k1_tarski(A_22))=k2_xboole_0(k1_tarski(A_77), k2_tarski(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2137])).
% 47.80/38.53  tff(c_2328, plain, (![A_81, A_80, B_82]: (k1_enumset1(A_81, A_80, B_82)=k1_enumset1(A_80, A_81, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_10, c_2291])).
% 47.80/38.53  tff(c_7704, plain, (![A_164, A_165, B_166, D_167]: (k2_xboole_0(k1_enumset1(A_164, A_165, B_166), k1_tarski(D_167))=k2_enumset1(A_165, A_164, B_166, D_167))), inference(superposition, [status(thm), theory('equality')], [c_2328, c_12])).
% 47.80/38.53  tff(c_7752, plain, (![A_165, A_164, B_166, D_167]: (k2_enumset1(A_165, A_164, B_166, D_167)=k2_enumset1(A_164, A_165, B_166, D_167))), inference(superposition, [status(thm), theory('equality')], [c_7704, c_12])).
% 47.80/38.53  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 47.80/38.53  tff(c_5024, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4757, c_14])).
% 47.80/38.53  tff(c_9019, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7752, c_5024])).
% 47.80/38.53  tff(c_9020, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4757, c_9019])).
% 47.80/38.53  tff(c_40251, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_4', '#skF_5', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9691, c_9020])).
% 47.80/38.53  tff(c_42403, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_4', '#skF_5', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35708, c_40251])).
% 47.80/38.53  tff(c_54403, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5'))!=k3_enumset1('#skF_4', '#skF_5', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48074, c_42403])).
% 47.80/38.53  tff(c_54404, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5'))!=k3_enumset1('#skF_4', '#skF_1', '#skF_5', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9691, c_35708, c_9691, c_54403])).
% 47.80/38.53  tff(c_66811, plain, (k3_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1', '#skF_5')!=k3_enumset1('#skF_4', '#skF_1', '#skF_5', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66810, c_54404])).
% 47.80/38.53  tff(c_66814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9691, c_66811])).
% 47.80/38.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.80/38.53  
% 47.80/38.53  Inference rules
% 47.80/38.53  ----------------------
% 47.80/38.53  #Ref     : 0
% 47.80/38.53  #Sup     : 17793
% 47.80/38.53  #Fact    : 0
% 47.80/38.53  #Define  : 0
% 47.80/38.53  #Split   : 0
% 47.80/38.53  #Chain   : 0
% 47.80/38.53  #Close   : 0
% 47.80/38.53  
% 47.80/38.53  Ordering : KBO
% 47.80/38.53  
% 47.80/38.53  Simplification rules
% 47.80/38.53  ----------------------
% 47.80/38.53  #Subsume      : 3071
% 47.80/38.53  #Demod        : 12256
% 47.80/38.53  #Tautology    : 1549
% 47.80/38.53  #SimpNegUnit  : 0
% 47.80/38.53  #BackRed      : 6
% 47.80/38.53  
% 47.80/38.53  #Partial instantiations: 0
% 47.80/38.53  #Strategies tried      : 1
% 47.80/38.53  
% 47.80/38.53  Timing (in seconds)
% 47.80/38.53  ----------------------
% 47.80/38.53  Preprocessing        : 0.26
% 47.80/38.53  Parsing              : 0.14
% 47.80/38.53  CNF conversion       : 0.02
% 47.80/38.53  Main loop            : 37.51
% 47.80/38.53  Inferencing          : 2.79
% 47.80/38.53  Reduction            : 31.68
% 47.80/38.53  Demodulation         : 31.05
% 47.80/38.53  BG Simplification    : 0.59
% 47.80/38.53  Subsumption          : 1.91
% 47.80/38.53  Abstraction          : 0.89
% 47.80/38.53  MUC search           : 0.00
% 47.80/38.53  Cooper               : 0.00
% 47.80/38.53  Total                : 37.81
% 47.80/38.53  Index Insertion      : 0.00
% 47.80/38.53  Index Deletion       : 0.00
% 47.80/38.53  Index Matching       : 0.00
% 47.80/38.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

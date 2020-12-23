%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 13.50s
% Output     : CNFRefutation 13.50s
% Verified   : 
% Statistics : Number of formulae       :  101 (1093 expanded)
%              Number of leaves         :   20 ( 388 expanded)
%              Depth                    :   23
%              Number of atoms          :   91 (1083 expanded)
%              Number of equality atoms :   90 (1082 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(A_26,B_27),B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [B_27,A_26] : k2_xboole_0(B_27,k4_xboole_0(A_26,B_27)) = k2_xboole_0(B_27,k2_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_6])).

tff(c_771,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,k2_xboole_0(A_49,B_48)) = k2_xboole_0(B_48,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_156])).

tff(c_1054,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,k2_xboole_0(B_55,A_56)) = k2_xboole_0(B_55,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_771])).

tff(c_1105,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = k2_xboole_0(k3_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1054])).

tff(c_1203,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_1105])).

tff(c_40,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_1222,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_56])).

tff(c_407,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_441,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_407])).

tff(c_169,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k4_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_446,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_169])).

tff(c_1241,plain,(
    ! [B_60] : k3_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_56])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1272,plain,(
    ! [B_60,C_16] : k3_xboole_0(k1_xboole_0,k4_xboole_0(B_60,C_16)) = k4_xboole_0(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_16])).

tff(c_1290,plain,(
    ! [C_16] : k3_xboole_0(C_16,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_446,c_1272])).

tff(c_447,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_xboole_0(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_407])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_453,plain,(
    ! [A_37] : k4_xboole_0(A_37,k3_xboole_0(A_37,k1_xboole_0)) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_14])).

tff(c_1297,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_453])).

tff(c_1563,plain,(
    ! [A_67] : k3_xboole_0(A_67,A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1297])).

tff(c_1586,plain,(
    ! [A_67,C_16] : k3_xboole_0(A_67,k4_xboole_0(A_67,C_16)) = k4_xboole_0(A_67,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_16])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_561,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_607,plain,(
    ! [A_12,B_13,C_42] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_42)) = k4_xboole_0(k3_xboole_0(A_12,B_13),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_561])).

tff(c_5231,plain,(
    ! [A_12,B_13,C_42] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_42)) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_607])).

tff(c_184,plain,(
    ! [B_27,A_26] : k2_xboole_0(B_27,k2_xboole_0(A_26,B_27)) = k2_xboole_0(B_27,A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_156])).

tff(c_172,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_3093,plain,(
    ! [C_97,A_98,B_99] : k2_xboole_0(C_97,k4_xboole_0(A_98,k2_xboole_0(B_99,C_97))) = k2_xboole_0(C_97,k4_xboole_0(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_6])).

tff(c_3127,plain,(
    ! [A_98,B_99,C_97] : k4_xboole_0(k4_xboole_0(A_98,k2_xboole_0(B_99,C_97)),C_97) = k4_xboole_0(k2_xboole_0(C_97,k4_xboole_0(A_98,B_99)),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_172])).

tff(c_3246,plain,(
    ! [A_98,C_97,B_99] : k4_xboole_0(A_98,k2_xboole_0(C_97,B_99)) = k4_xboole_0(A_98,k2_xboole_0(B_99,C_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_12,c_172,c_2,c_12,c_3127])).

tff(c_584,plain,(
    ! [C_42,A_40,B_41] : k2_xboole_0(C_42,k4_xboole_0(A_40,k2_xboole_0(B_41,C_42))) = k2_xboole_0(C_42,k4_xboole_0(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_6])).

tff(c_578,plain,(
    ! [A_40,B_41,B_13] : k4_xboole_0(A_40,k2_xboole_0(B_41,k4_xboole_0(k4_xboole_0(A_40,B_41),B_13))) = k3_xboole_0(k4_xboole_0(A_40,B_41),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_14])).

tff(c_20638,plain,(
    ! [A_259,B_260,B_261] : k4_xboole_0(A_259,k2_xboole_0(B_260,k4_xboole_0(A_259,k2_xboole_0(B_260,B_261)))) = k3_xboole_0(k4_xboole_0(A_259,B_260),B_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_578])).

tff(c_21066,plain,(
    ! [A_259,B_2,A_1] : k4_xboole_0(A_259,k2_xboole_0(B_2,k4_xboole_0(A_259,k2_xboole_0(A_1,B_2)))) = k3_xboole_0(k4_xboole_0(A_259,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20638])).

tff(c_39596,plain,(
    ! [A_360,B_361,A_362] : k4_xboole_0(A_360,k2_xboole_0(B_361,k4_xboole_0(A_360,A_362))) = k3_xboole_0(k4_xboole_0(A_360,B_361),A_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_21066])).

tff(c_39891,plain,(
    ! [A_98,A_362,C_97] : k4_xboole_0(A_98,k2_xboole_0(k4_xboole_0(A_98,A_362),C_97)) = k3_xboole_0(k4_xboole_0(A_98,C_97),A_362) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_39596])).

tff(c_40186,plain,(
    ! [A_98,C_97,A_362] : k3_xboole_0(k4_xboole_0(A_98,C_97),A_362) = k3_xboole_0(A_98,k4_xboole_0(A_362,C_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5231,c_39891])).

tff(c_1299,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_441])).

tff(c_638,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k3_xboole_0(A_43,B_44),C_45) = k3_xboole_0(A_43,k4_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2769,plain,(
    ! [C_90,A_91,B_92] : k2_xboole_0(C_90,k3_xboole_0(A_91,k4_xboole_0(B_92,C_90))) = k2_xboole_0(C_90,k3_xboole_0(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_6])).

tff(c_2835,plain,(
    ! [A_6,A_91] : k2_xboole_0(A_6,k3_xboole_0(A_91,k1_xboole_0)) = k2_xboole_0(A_6,k3_xboole_0(A_91,A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_2769])).

tff(c_2889,plain,(
    ! [A_6,A_91] : k2_xboole_0(A_6,k3_xboole_0(A_91,A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1290,c_2835])).

tff(c_1143,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_1105])).

tff(c_1445,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_441])).

tff(c_1457,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k4_xboole_0(B_15,k3_xboole_0(A_14,B_15))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_16])).

tff(c_410,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_14])).

tff(c_3717,plain,(
    ! [A_106,B_107] : k4_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_410])).

tff(c_3784,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(B_15,k3_xboole_0(A_14,B_15))) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_3717])).

tff(c_5483,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k4_xboole_0(B_130,k3_xboole_0(A_129,B_130))) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3784])).

tff(c_336,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_360,plain,(
    ! [A_34] : k2_xboole_0(k3_xboole_0(A_34,k1_xboole_0),A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_336])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_366,plain,(
    ! [A_34] : k4_xboole_0(k3_xboole_0(A_34,k1_xboole_0),A_34) = k4_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_10])).

tff(c_892,plain,(
    ! [A_34] : k4_xboole_0(k3_xboole_0(A_34,k1_xboole_0),A_34) = k3_xboole_0(A_34,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_366])).

tff(c_1296,plain,(
    ! [A_34] : k4_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1290,c_892])).

tff(c_1460,plain,(
    ! [A_65,C_11] : k4_xboole_0(A_65,k2_xboole_0(A_65,C_11)) = k4_xboole_0(k1_xboole_0,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_12])).

tff(c_1708,plain,(
    ! [A_70,C_71] : k4_xboole_0(A_70,k2_xboole_0(A_70,C_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1460])).

tff(c_1983,plain,(
    ! [A_76,B_77] : k4_xboole_0(k3_xboole_0(A_76,B_77),A_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1708])).

tff(c_2028,plain,(
    ! [C_16,B_15] : k3_xboole_0(C_16,k4_xboole_0(B_15,C_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1983])).

tff(c_33638,plain,(
    ! [B_333,A_334] : k3_xboole_0(k4_xboole_0(B_333,k3_xboole_0(A_334,B_333)),A_334) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5483,c_2028])).

tff(c_581,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_40,B_41),C_42),k4_xboole_0(A_40,k2_xboole_0(B_41,C_42))) = k4_xboole_0(A_40,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_18])).

tff(c_33709,plain,(
    ! [B_333,A_334] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_333,k2_xboole_0(k3_xboole_0(A_334,B_333),A_334))) = k4_xboole_0(B_333,k3_xboole_0(A_334,B_333)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33638,c_581])).

tff(c_36300,plain,(
    ! [B_347,A_348] : k4_xboole_0(B_347,k3_xboole_0(A_348,B_347)) = k4_xboole_0(B_347,A_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_56,c_2,c_33709])).

tff(c_3787,plain,(
    ! [C_16,B_15] : k4_xboole_0(C_16,k4_xboole_0(B_15,C_16)) = k4_xboole_0(C_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_3717])).

tff(c_3831,plain,(
    ! [C_16,B_15] : k4_xboole_0(C_16,k4_xboole_0(B_15,C_16)) = C_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3787])).

tff(c_166,plain,(
    ! [A_4,B_5] : k4_xboole_0(k2_xboole_0(A_4,B_5),k4_xboole_0(B_5,A_4)) = k4_xboole_0(A_4,k4_xboole_0(B_5,A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_150])).

tff(c_3840,plain,(
    ! [A_4,B_5] : k4_xboole_0(k2_xboole_0(A_4,B_5),k4_xboole_0(B_5,A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3831,c_166])).

tff(c_36312,plain,(
    ! [A_348,B_347] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_348,B_347),B_347),k4_xboole_0(B_347,A_348)) = k3_xboole_0(A_348,B_347) ),
    inference(superposition,[status(thm),theory(equality)],[c_36300,c_3840])).

tff(c_36576,plain,(
    ! [B_347,A_348] : k3_xboole_0(B_347,A_348) = k3_xboole_0(A_348,B_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2889,c_2,c_36312])).

tff(c_20,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_36646,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36576,c_21])).

tff(c_51243,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40186,c_36646])).

tff(c_51255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_2,c_12,c_51243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.50/6.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/6.64  
% 13.50/6.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/6.64  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.50/6.64  
% 13.50/6.64  %Foreground sorts:
% 13.50/6.64  
% 13.50/6.64  
% 13.50/6.64  %Background operators:
% 13.50/6.64  
% 13.50/6.64  
% 13.50/6.64  %Foreground operators:
% 13.50/6.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.50/6.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.50/6.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.50/6.64  tff('#skF_2', type, '#skF_2': $i).
% 13.50/6.64  tff('#skF_3', type, '#skF_3': $i).
% 13.50/6.64  tff('#skF_1', type, '#skF_1': $i).
% 13.50/6.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.50/6.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.50/6.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.50/6.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.50/6.64  
% 13.50/6.66  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.50/6.66  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.50/6.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.50/6.66  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.50/6.66  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.50/6.66  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.50/6.66  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.50/6.66  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.50/6.66  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.50/6.66  tff(f_46, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 13.50/6.66  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.50/6.66  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.50/6.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.50/6.66  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.50/6.66  tff(c_150, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(A_26, B_27), B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.50/6.66  tff(c_156, plain, (![B_27, A_26]: (k2_xboole_0(B_27, k4_xboole_0(A_26, B_27))=k2_xboole_0(B_27, k2_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_6])).
% 13.50/6.66  tff(c_771, plain, (![B_48, A_49]: (k2_xboole_0(B_48, k2_xboole_0(A_49, B_48))=k2_xboole_0(B_48, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_156])).
% 13.50/6.66  tff(c_1054, plain, (![B_55, A_56]: (k2_xboole_0(B_55, k2_xboole_0(B_55, A_56))=k2_xboole_0(B_55, A_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_771])).
% 13.50/6.66  tff(c_1105, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=k2_xboole_0(k3_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1054])).
% 13.50/6.66  tff(c_1203, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k3_xboole_0(A_58, B_59))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_1105])).
% 13.50/6.66  tff(c_40, plain, (![B_21, A_22]: (k2_xboole_0(B_21, A_22)=k2_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.50/6.66  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.50/6.66  tff(c_56, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 13.50/6.66  tff(c_1222, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1203, c_56])).
% 13.50/6.66  tff(c_407, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.50/6.66  tff(c_441, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_407])).
% 13.50/6.66  tff(c_169, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k4_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_56, c_150])).
% 13.50/6.66  tff(c_446, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_169])).
% 13.50/6.66  tff(c_1241, plain, (![B_60]: (k3_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1203, c_56])).
% 13.50/6.66  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.50/6.66  tff(c_1272, plain, (![B_60, C_16]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(B_60, C_16))=k4_xboole_0(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_16])).
% 13.50/6.66  tff(c_1290, plain, (![C_16]: (k3_xboole_0(C_16, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_446, c_1272])).
% 13.50/6.66  tff(c_447, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_xboole_0(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_407])).
% 13.50/6.66  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.50/6.66  tff(c_453, plain, (![A_37]: (k4_xboole_0(A_37, k3_xboole_0(A_37, k1_xboole_0))=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_447, c_14])).
% 13.50/6.66  tff(c_1297, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_453])).
% 13.50/6.66  tff(c_1563, plain, (![A_67]: (k3_xboole_0(A_67, A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1297])).
% 13.50/6.66  tff(c_1586, plain, (![A_67, C_16]: (k3_xboole_0(A_67, k4_xboole_0(A_67, C_16))=k4_xboole_0(A_67, C_16))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_16])).
% 13.50/6.66  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.50/6.66  tff(c_561, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.50/6.66  tff(c_607, plain, (![A_12, B_13, C_42]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_42))=k4_xboole_0(k3_xboole_0(A_12, B_13), C_42))), inference(superposition, [status(thm), theory('equality')], [c_14, c_561])).
% 13.50/6.66  tff(c_5231, plain, (![A_12, B_13, C_42]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_42))=k3_xboole_0(A_12, k4_xboole_0(B_13, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_607])).
% 13.50/6.66  tff(c_184, plain, (![B_27, A_26]: (k2_xboole_0(B_27, k2_xboole_0(A_26, B_27))=k2_xboole_0(B_27, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_156])).
% 13.50/6.66  tff(c_172, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 13.50/6.66  tff(c_3093, plain, (![C_97, A_98, B_99]: (k2_xboole_0(C_97, k4_xboole_0(A_98, k2_xboole_0(B_99, C_97)))=k2_xboole_0(C_97, k4_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_561, c_6])).
% 13.50/6.66  tff(c_3127, plain, (![A_98, B_99, C_97]: (k4_xboole_0(k4_xboole_0(A_98, k2_xboole_0(B_99, C_97)), C_97)=k4_xboole_0(k2_xboole_0(C_97, k4_xboole_0(A_98, B_99)), C_97))), inference(superposition, [status(thm), theory('equality')], [c_3093, c_172])).
% 13.50/6.66  tff(c_3246, plain, (![A_98, C_97, B_99]: (k4_xboole_0(A_98, k2_xboole_0(C_97, B_99))=k4_xboole_0(A_98, k2_xboole_0(B_99, C_97)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_12, c_172, c_2, c_12, c_3127])).
% 13.50/6.66  tff(c_584, plain, (![C_42, A_40, B_41]: (k2_xboole_0(C_42, k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))=k2_xboole_0(C_42, k4_xboole_0(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_561, c_6])).
% 13.50/6.66  tff(c_578, plain, (![A_40, B_41, B_13]: (k4_xboole_0(A_40, k2_xboole_0(B_41, k4_xboole_0(k4_xboole_0(A_40, B_41), B_13)))=k3_xboole_0(k4_xboole_0(A_40, B_41), B_13))), inference(superposition, [status(thm), theory('equality')], [c_561, c_14])).
% 13.50/6.66  tff(c_20638, plain, (![A_259, B_260, B_261]: (k4_xboole_0(A_259, k2_xboole_0(B_260, k4_xboole_0(A_259, k2_xboole_0(B_260, B_261))))=k3_xboole_0(k4_xboole_0(A_259, B_260), B_261))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_578])).
% 13.50/6.66  tff(c_21066, plain, (![A_259, B_2, A_1]: (k4_xboole_0(A_259, k2_xboole_0(B_2, k4_xboole_0(A_259, k2_xboole_0(A_1, B_2))))=k3_xboole_0(k4_xboole_0(A_259, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20638])).
% 13.50/6.66  tff(c_39596, plain, (![A_360, B_361, A_362]: (k4_xboole_0(A_360, k2_xboole_0(B_361, k4_xboole_0(A_360, A_362)))=k3_xboole_0(k4_xboole_0(A_360, B_361), A_362))), inference(demodulation, [status(thm), theory('equality')], [c_584, c_21066])).
% 13.50/6.66  tff(c_39891, plain, (![A_98, A_362, C_97]: (k4_xboole_0(A_98, k2_xboole_0(k4_xboole_0(A_98, A_362), C_97))=k3_xboole_0(k4_xboole_0(A_98, C_97), A_362))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_39596])).
% 13.50/6.66  tff(c_40186, plain, (![A_98, C_97, A_362]: (k3_xboole_0(k4_xboole_0(A_98, C_97), A_362)=k3_xboole_0(A_98, k4_xboole_0(A_362, C_97)))), inference(demodulation, [status(thm), theory('equality')], [c_5231, c_39891])).
% 13.50/6.66  tff(c_1299, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_441])).
% 13.50/6.66  tff(c_638, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k3_xboole_0(A_43, B_44), C_45)=k3_xboole_0(A_43, k4_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.50/6.66  tff(c_2769, plain, (![C_90, A_91, B_92]: (k2_xboole_0(C_90, k3_xboole_0(A_91, k4_xboole_0(B_92, C_90)))=k2_xboole_0(C_90, k3_xboole_0(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_638, c_6])).
% 13.50/6.66  tff(c_2835, plain, (![A_6, A_91]: (k2_xboole_0(A_6, k3_xboole_0(A_91, k1_xboole_0))=k2_xboole_0(A_6, k3_xboole_0(A_91, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_2769])).
% 13.50/6.66  tff(c_2889, plain, (![A_6, A_91]: (k2_xboole_0(A_6, k3_xboole_0(A_91, A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1290, c_2835])).
% 13.50/6.66  tff(c_1143, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k3_xboole_0(A_17, B_18))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_1105])).
% 13.50/6.66  tff(c_1445, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_441])).
% 13.50/6.66  tff(c_1457, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k4_xboole_0(B_15, k3_xboole_0(A_14, B_15)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1445, c_16])).
% 13.50/6.66  tff(c_410, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k3_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_14])).
% 13.50/6.66  tff(c_3717, plain, (![A_106, B_107]: (k4_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_410])).
% 13.50/6.66  tff(c_3784, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(B_15, k3_xboole_0(A_14, B_15)))=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1457, c_3717])).
% 13.50/6.66  tff(c_5483, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k4_xboole_0(B_130, k3_xboole_0(A_129, B_130)))=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3784])).
% 13.50/6.66  tff(c_336, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.50/6.66  tff(c_360, plain, (![A_34]: (k2_xboole_0(k3_xboole_0(A_34, k1_xboole_0), A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_8, c_336])).
% 13.50/6.66  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.50/6.66  tff(c_366, plain, (![A_34]: (k4_xboole_0(k3_xboole_0(A_34, k1_xboole_0), A_34)=k4_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_360, c_10])).
% 13.50/6.66  tff(c_892, plain, (![A_34]: (k4_xboole_0(k3_xboole_0(A_34, k1_xboole_0), A_34)=k3_xboole_0(A_34, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_366])).
% 13.50/6.66  tff(c_1296, plain, (![A_34]: (k4_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1290, c_892])).
% 13.50/6.66  tff(c_1460, plain, (![A_65, C_11]: (k4_xboole_0(A_65, k2_xboole_0(A_65, C_11))=k4_xboole_0(k1_xboole_0, C_11))), inference(superposition, [status(thm), theory('equality')], [c_1445, c_12])).
% 13.50/6.66  tff(c_1708, plain, (![A_70, C_71]: (k4_xboole_0(A_70, k2_xboole_0(A_70, C_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1460])).
% 13.50/6.66  tff(c_1983, plain, (![A_76, B_77]: (k4_xboole_0(k3_xboole_0(A_76, B_77), A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1708])).
% 13.50/6.66  tff(c_2028, plain, (![C_16, B_15]: (k3_xboole_0(C_16, k4_xboole_0(B_15, C_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1983])).
% 13.50/6.66  tff(c_33638, plain, (![B_333, A_334]: (k3_xboole_0(k4_xboole_0(B_333, k3_xboole_0(A_334, B_333)), A_334)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5483, c_2028])).
% 13.50/6.66  tff(c_581, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_40, B_41), C_42), k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))=k4_xboole_0(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_561, c_18])).
% 13.50/6.66  tff(c_33709, plain, (![B_333, A_334]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_333, k2_xboole_0(k3_xboole_0(A_334, B_333), A_334)))=k4_xboole_0(B_333, k3_xboole_0(A_334, B_333)))), inference(superposition, [status(thm), theory('equality')], [c_33638, c_581])).
% 13.50/6.66  tff(c_36300, plain, (![B_347, A_348]: (k4_xboole_0(B_347, k3_xboole_0(A_348, B_347))=k4_xboole_0(B_347, A_348))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_56, c_2, c_33709])).
% 13.50/6.66  tff(c_3787, plain, (![C_16, B_15]: (k4_xboole_0(C_16, k4_xboole_0(B_15, C_16))=k4_xboole_0(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2028, c_3717])).
% 13.50/6.66  tff(c_3831, plain, (![C_16, B_15]: (k4_xboole_0(C_16, k4_xboole_0(B_15, C_16))=C_16)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3787])).
% 13.50/6.66  tff(c_166, plain, (![A_4, B_5]: (k4_xboole_0(k2_xboole_0(A_4, B_5), k4_xboole_0(B_5, A_4))=k4_xboole_0(A_4, k4_xboole_0(B_5, A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_150])).
% 13.50/6.66  tff(c_3840, plain, (![A_4, B_5]: (k4_xboole_0(k2_xboole_0(A_4, B_5), k4_xboole_0(B_5, A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_3831, c_166])).
% 13.50/6.66  tff(c_36312, plain, (![A_348, B_347]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_348, B_347), B_347), k4_xboole_0(B_347, A_348))=k3_xboole_0(A_348, B_347))), inference(superposition, [status(thm), theory('equality')], [c_36300, c_3840])).
% 13.50/6.66  tff(c_36576, plain, (![B_347, A_348]: (k3_xboole_0(B_347, A_348)=k3_xboole_0(A_348, B_347))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2889, c_2, c_36312])).
% 13.50/6.66  tff(c_20, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.50/6.66  tff(c_21, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 13.50/6.66  tff(c_36646, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36576, c_21])).
% 13.50/6.66  tff(c_51243, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40186, c_36646])).
% 13.50/6.66  tff(c_51255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1586, c_2, c_12, c_51243])).
% 13.50/6.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/6.66  
% 13.50/6.66  Inference rules
% 13.50/6.66  ----------------------
% 13.50/6.66  #Ref     : 0
% 13.50/6.66  #Sup     : 12852
% 13.50/6.66  #Fact    : 0
% 13.50/6.66  #Define  : 0
% 13.50/6.66  #Split   : 0
% 13.50/6.66  #Chain   : 0
% 13.50/6.66  #Close   : 0
% 13.50/6.66  
% 13.50/6.66  Ordering : KBO
% 13.50/6.66  
% 13.50/6.66  Simplification rules
% 13.50/6.66  ----------------------
% 13.50/6.66  #Subsume      : 131
% 13.50/6.66  #Demod        : 16219
% 13.50/6.66  #Tautology    : 8931
% 13.50/6.66  #SimpNegUnit  : 0
% 13.50/6.66  #BackRed      : 31
% 13.50/6.66  
% 13.50/6.66  #Partial instantiations: 0
% 13.50/6.66  #Strategies tried      : 1
% 13.50/6.66  
% 13.50/6.66  Timing (in seconds)
% 13.50/6.66  ----------------------
% 13.50/6.66  Preprocessing        : 0.29
% 13.50/6.66  Parsing              : 0.15
% 13.50/6.66  CNF conversion       : 0.02
% 13.50/6.66  Main loop            : 5.58
% 13.50/6.66  Inferencing          : 0.98
% 13.50/6.66  Reduction            : 3.45
% 13.50/6.66  Demodulation         : 3.17
% 13.50/6.66  BG Simplification    : 0.13
% 13.50/6.66  Subsumption          : 0.78
% 13.50/6.66  Abstraction          : 0.26
% 13.50/6.66  MUC search           : 0.00
% 13.50/6.66  Cooper               : 0.00
% 13.50/6.66  Total                : 5.92
% 13.50/6.67  Index Insertion      : 0.00
% 13.50/6.67  Index Deletion       : 0.00
% 13.50/6.67  Index Matching       : 0.00
% 13.50/6.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

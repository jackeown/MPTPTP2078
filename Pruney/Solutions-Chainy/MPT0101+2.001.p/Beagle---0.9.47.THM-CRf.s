%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:39 EST 2020

% Result     : Theorem 14.45s
% Output     : CNFRefutation 14.56s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 211 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 201 expanded)
%              Number of equality atoms :   78 ( 200 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_227,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_234,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_227])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_736,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k4_xboole_0(A_59,B_60),C_61) = k4_xboole_0(A_59,k2_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21588,plain,(
    ! [A_291,B_292,C_293] : k4_xboole_0(k4_xboole_0(A_291,B_292),k4_xboole_0(A_291,k2_xboole_0(B_292,C_293))) = k3_xboole_0(k4_xboole_0(A_291,B_292),C_293) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_20])).

tff(c_22031,plain,(
    ! [A_291,A_7] : k4_xboole_0(k4_xboole_0(A_291,A_7),k4_xboole_0(A_291,A_7)) = k3_xboole_0(k4_xboole_0(A_291,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_21588])).

tff(c_22167,plain,(
    ! [A_294,A_295] : k3_xboole_0(A_294,k4_xboole_0(A_295,A_294)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_4,c_22031])).

tff(c_668,plain,(
    ! [A_57,B_58] : k2_xboole_0(k5_xboole_0(A_57,B_58),k3_xboole_0(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_713,plain,(
    ! [A_3,B_4] : k2_xboole_0(k5_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_668])).

tff(c_22275,plain,(
    ! [A_295,A_294] : k2_xboole_0(k5_xboole_0(k4_xboole_0(A_295,A_294),A_294),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_295,A_294),A_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_22167,c_713])).

tff(c_22496,plain,(
    ! [A_294,A_295] : k5_xboole_0(A_294,k4_xboole_0(A_295,A_294)) = k2_xboole_0(A_294,A_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_10,c_6,c_22275])).

tff(c_487,plain,(
    ! [A_50,B_51] : k2_xboole_0(k3_xboole_0(A_50,B_51),k4_xboole_0(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1294,plain,(
    ! [B_77,A_78] : k2_xboole_0(k3_xboole_0(B_77,A_78),k4_xboole_0(A_78,B_77)) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_487])).

tff(c_258,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_276,plain,(
    ! [B_42,A_43] : k4_xboole_0(B_42,k2_xboole_0(A_43,B_42)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_18])).

tff(c_1389,plain,(
    ! [A_79,B_80] : k4_xboole_0(k4_xboole_0(A_79,B_80),A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_276])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1409,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_79,B_80),A_79),k1_xboole_0) = k4_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_22])).

tff(c_1462,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_1409])).

tff(c_523,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_542,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_523])).

tff(c_11762,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_542])).

tff(c_832,plain,(
    ! [A_62,B_63] : k4_xboole_0(k3_xboole_0(A_62,B_63),A_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_843,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_62,B_63),A_62),k1_xboole_0) = k3_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_22])).

tff(c_2662,plain,(
    ! [A_104,B_105] : k3_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_843])).

tff(c_2724,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2662])).

tff(c_12007,plain,(
    ! [A_212,B_213] : k4_xboole_0(A_212,k3_xboole_0(A_212,B_213)) = k4_xboole_0(A_212,B_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_542])).

tff(c_12087,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(B_4,A_3)) = k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2724,c_12007])).

tff(c_12162,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11762,c_12087])).

tff(c_1077,plain,(
    ! [B_71,A_72] : k4_xboole_0(k3_xboole_0(B_71,A_72),A_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_832])).

tff(c_1094,plain,(
    ! [A_72,B_71] : k2_xboole_0(A_72,k3_xboole_0(B_71,A_72)) = k2_xboole_0(A_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_12])).

tff(c_1131,plain,(
    ! [A_72,B_71] : k2_xboole_0(A_72,k3_xboole_0(B_71,A_72)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1094])).

tff(c_436,plain,(
    ! [B_48,A_49] : k4_xboole_0(B_48,k2_xboole_0(A_49,B_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_18])).

tff(c_444,plain,(
    ! [A_49,B_48] : k2_xboole_0(k2_xboole_0(A_49,B_48),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_49,B_48),B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_12])).

tff(c_3099,plain,(
    ! [A_113,B_114] : k2_xboole_0(k2_xboole_0(A_113,B_114),B_114) = k2_xboole_0(A_113,B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_444])).

tff(c_6516,plain,(
    ! [B_156,A_157] : k2_xboole_0(k2_xboole_0(B_156,A_157),B_156) = k2_xboole_0(A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3099])).

tff(c_6660,plain,(
    ! [B_71,A_72] : k2_xboole_0(k3_xboole_0(B_71,A_72),A_72) = k2_xboole_0(A_72,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_6516])).

tff(c_6735,plain,(
    ! [B_71,A_72] : k2_xboole_0(k3_xboole_0(B_71,A_72),A_72) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6660])).

tff(c_26913,plain,(
    ! [A_320,A_321] : k5_xboole_0(A_320,k4_xboole_0(A_321,A_320)) = k2_xboole_0(A_320,A_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_10,c_6,c_22275])).

tff(c_130,plain,(
    ! [B_36,A_37] : k5_xboole_0(B_36,A_37) = k5_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_146,plain,(
    ! [A_37] : k5_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_884,plain,(
    ! [A_64,B_65,C_66] : k5_xboole_0(k5_xboole_0(A_64,B_65),C_66) = k5_xboole_0(A_64,k5_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_940,plain,(
    ! [A_26,C_66] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_66)) = k5_xboole_0(k1_xboole_0,C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_884])).

tff(c_1012,plain,(
    ! [A_69,C_70] : k5_xboole_0(A_69,k5_xboole_0(A_69,C_70)) = C_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_940])).

tff(c_1215,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k5_xboole_0(B_76,A_75)) = B_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1012])).

tff(c_1055,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k5_xboole_0(B_6,A_5)) = B_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1012])).

tff(c_1218,plain,(
    ! [B_76,A_75] : k5_xboole_0(k5_xboole_0(B_76,A_75),B_76) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_1055])).

tff(c_30353,plain,(
    ! [A_339,A_340] : k5_xboole_0(k2_xboole_0(A_339,A_340),A_339) = k4_xboole_0(A_340,A_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_26913,c_1218])).

tff(c_30500,plain,(
    ! [A_72,B_71] : k5_xboole_0(A_72,k3_xboole_0(B_71,A_72)) = k4_xboole_0(A_72,k3_xboole_0(B_71,A_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6735,c_30353])).

tff(c_30618,plain,(
    ! [A_72,B_71] : k5_xboole_0(A_72,k3_xboole_0(B_71,A_72)) = k4_xboole_0(A_72,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12162,c_30500])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2'))) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32])).

tff(c_57524,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30618,c_33])).

tff(c_57529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22496,c_57524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.45/8.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.45/8.24  
% 14.45/8.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.45/8.24  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 14.45/8.24  
% 14.45/8.24  %Foreground sorts:
% 14.45/8.24  
% 14.45/8.24  
% 14.45/8.24  %Background operators:
% 14.45/8.24  
% 14.45/8.24  
% 14.45/8.24  %Foreground operators:
% 14.45/8.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.45/8.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.45/8.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.45/8.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.45/8.24  tff('#skF_2', type, '#skF_2': $i).
% 14.45/8.24  tff('#skF_1', type, '#skF_1': $i).
% 14.45/8.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.45/8.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.45/8.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.45/8.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.45/8.24  
% 14.56/8.26  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.56/8.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.56/8.26  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.56/8.26  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.56/8.26  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 14.56/8.26  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.56/8.26  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.56/8.26  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.56/8.26  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.56/8.26  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 14.56/8.26  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.56/8.26  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 14.56/8.26  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.56/8.26  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.56/8.26  tff(f_58, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.56/8.26  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.56/8.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.56/8.26  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.56/8.26  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.56/8.26  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.56/8.26  tff(c_227, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.56/8.26  tff(c_234, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_227])).
% 14.56/8.26  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.56/8.26  tff(c_736, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k4_xboole_0(A_59, B_60), C_61)=k4_xboole_0(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.56/8.26  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.56/8.26  tff(c_21588, plain, (![A_291, B_292, C_293]: (k4_xboole_0(k4_xboole_0(A_291, B_292), k4_xboole_0(A_291, k2_xboole_0(B_292, C_293)))=k3_xboole_0(k4_xboole_0(A_291, B_292), C_293))), inference(superposition, [status(thm), theory('equality')], [c_736, c_20])).
% 14.56/8.26  tff(c_22031, plain, (![A_291, A_7]: (k4_xboole_0(k4_xboole_0(A_291, A_7), k4_xboole_0(A_291, A_7))=k3_xboole_0(k4_xboole_0(A_291, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_21588])).
% 14.56/8.26  tff(c_22167, plain, (![A_294, A_295]: (k3_xboole_0(A_294, k4_xboole_0(A_295, A_294))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_234, c_4, c_22031])).
% 14.56/8.26  tff(c_668, plain, (![A_57, B_58]: (k2_xboole_0(k5_xboole_0(A_57, B_58), k3_xboole_0(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.56/8.26  tff(c_713, plain, (![A_3, B_4]: (k2_xboole_0(k5_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_668])).
% 14.56/8.26  tff(c_22275, plain, (![A_295, A_294]: (k2_xboole_0(k5_xboole_0(k4_xboole_0(A_295, A_294), A_294), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_295, A_294), A_294))), inference(superposition, [status(thm), theory('equality')], [c_22167, c_713])).
% 14.56/8.26  tff(c_22496, plain, (![A_294, A_295]: (k5_xboole_0(A_294, k4_xboole_0(A_295, A_294))=k2_xboole_0(A_294, A_295))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_10, c_6, c_22275])).
% 14.56/8.26  tff(c_487, plain, (![A_50, B_51]: (k2_xboole_0(k3_xboole_0(A_50, B_51), k4_xboole_0(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.56/8.26  tff(c_1294, plain, (![B_77, A_78]: (k2_xboole_0(k3_xboole_0(B_77, A_78), k4_xboole_0(A_78, B_77))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_4, c_487])).
% 14.56/8.26  tff(c_258, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.56/8.26  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.56/8.26  tff(c_276, plain, (![B_42, A_43]: (k4_xboole_0(B_42, k2_xboole_0(A_43, B_42))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_18])).
% 14.56/8.26  tff(c_1389, plain, (![A_79, B_80]: (k4_xboole_0(k4_xboole_0(A_79, B_80), A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1294, c_276])).
% 14.56/8.26  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.56/8.26  tff(c_1409, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_79, B_80), A_79), k1_xboole_0)=k4_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_22])).
% 14.56/8.26  tff(c_1462, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_1409])).
% 14.56/8.26  tff(c_523, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.56/8.26  tff(c_542, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_523])).
% 14.56/8.26  tff(c_11762, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_542])).
% 14.56/8.26  tff(c_832, plain, (![A_62, B_63]: (k4_xboole_0(k3_xboole_0(A_62, B_63), A_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_487, c_18])).
% 14.56/8.26  tff(c_843, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_62, B_63), A_62), k1_xboole_0)=k3_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_832, c_22])).
% 14.56/8.26  tff(c_2662, plain, (![A_104, B_105]: (k3_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_843])).
% 14.56/8.26  tff(c_2724, plain, (![B_4, A_3]: (k3_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k3_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2662])).
% 14.56/8.26  tff(c_12007, plain, (![A_212, B_213]: (k4_xboole_0(A_212, k3_xboole_0(A_212, B_213))=k4_xboole_0(A_212, B_213))), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_542])).
% 14.56/8.26  tff(c_12087, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(B_4, A_3))=k4_xboole_0(B_4, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_2724, c_12007])).
% 14.56/8.26  tff(c_12162, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11762, c_12087])).
% 14.56/8.26  tff(c_1077, plain, (![B_71, A_72]: (k4_xboole_0(k3_xboole_0(B_71, A_72), A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_832])).
% 14.56/8.26  tff(c_1094, plain, (![A_72, B_71]: (k2_xboole_0(A_72, k3_xboole_0(B_71, A_72))=k2_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_12])).
% 14.56/8.26  tff(c_1131, plain, (![A_72, B_71]: (k2_xboole_0(A_72, k3_xboole_0(B_71, A_72))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1094])).
% 14.56/8.26  tff(c_436, plain, (![B_48, A_49]: (k4_xboole_0(B_48, k2_xboole_0(A_49, B_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_18])).
% 14.56/8.26  tff(c_444, plain, (![A_49, B_48]: (k2_xboole_0(k2_xboole_0(A_49, B_48), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_49, B_48), B_48))), inference(superposition, [status(thm), theory('equality')], [c_436, c_12])).
% 14.56/8.26  tff(c_3099, plain, (![A_113, B_114]: (k2_xboole_0(k2_xboole_0(A_113, B_114), B_114)=k2_xboole_0(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_444])).
% 14.56/8.26  tff(c_6516, plain, (![B_156, A_157]: (k2_xboole_0(k2_xboole_0(B_156, A_157), B_156)=k2_xboole_0(A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3099])).
% 14.56/8.26  tff(c_6660, plain, (![B_71, A_72]: (k2_xboole_0(k3_xboole_0(B_71, A_72), A_72)=k2_xboole_0(A_72, A_72))), inference(superposition, [status(thm), theory('equality')], [c_1131, c_6516])).
% 14.56/8.26  tff(c_6735, plain, (![B_71, A_72]: (k2_xboole_0(k3_xboole_0(B_71, A_72), A_72)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6660])).
% 14.56/8.26  tff(c_26913, plain, (![A_320, A_321]: (k5_xboole_0(A_320, k4_xboole_0(A_321, A_320))=k2_xboole_0(A_320, A_321))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_10, c_6, c_22275])).
% 14.56/8.26  tff(c_130, plain, (![B_36, A_37]: (k5_xboole_0(B_36, A_37)=k5_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.56/8.26  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.56/8.26  tff(c_146, plain, (![A_37]: (k5_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_130, c_24])).
% 14.56/8.26  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.56/8.26  tff(c_884, plain, (![A_64, B_65, C_66]: (k5_xboole_0(k5_xboole_0(A_64, B_65), C_66)=k5_xboole_0(A_64, k5_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.56/8.26  tff(c_940, plain, (![A_26, C_66]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_66))=k5_xboole_0(k1_xboole_0, C_66))), inference(superposition, [status(thm), theory('equality')], [c_28, c_884])).
% 14.56/8.26  tff(c_1012, plain, (![A_69, C_70]: (k5_xboole_0(A_69, k5_xboole_0(A_69, C_70))=C_70)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_940])).
% 14.56/8.26  tff(c_1215, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k5_xboole_0(B_76, A_75))=B_76)), inference(superposition, [status(thm), theory('equality')], [c_6, c_1012])).
% 14.56/8.26  tff(c_1055, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k5_xboole_0(B_6, A_5))=B_6)), inference(superposition, [status(thm), theory('equality')], [c_6, c_1012])).
% 14.56/8.26  tff(c_1218, plain, (![B_76, A_75]: (k5_xboole_0(k5_xboole_0(B_76, A_75), B_76)=A_75)), inference(superposition, [status(thm), theory('equality')], [c_1215, c_1055])).
% 14.56/8.26  tff(c_30353, plain, (![A_339, A_340]: (k5_xboole_0(k2_xboole_0(A_339, A_340), A_339)=k4_xboole_0(A_340, A_339))), inference(superposition, [status(thm), theory('equality')], [c_26913, c_1218])).
% 14.56/8.26  tff(c_30500, plain, (![A_72, B_71]: (k5_xboole_0(A_72, k3_xboole_0(B_71, A_72))=k4_xboole_0(A_72, k3_xboole_0(B_71, A_72)))), inference(superposition, [status(thm), theory('equality')], [c_6735, c_30353])).
% 14.56/8.26  tff(c_30618, plain, (![A_72, B_71]: (k5_xboole_0(A_72, k3_xboole_0(B_71, A_72))=k4_xboole_0(A_72, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_12162, c_30500])).
% 14.56/8.26  tff(c_26, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.56/8.26  tff(c_32, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.56/8.26  tff(c_33, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2')))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32])).
% 14.56/8.26  tff(c_57524, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30618, c_33])).
% 14.56/8.26  tff(c_57529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22496, c_57524])).
% 14.56/8.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.56/8.26  
% 14.56/8.26  Inference rules
% 14.56/8.26  ----------------------
% 14.56/8.26  #Ref     : 0
% 14.56/8.26  #Sup     : 14634
% 14.56/8.26  #Fact    : 0
% 14.56/8.26  #Define  : 0
% 14.56/8.26  #Split   : 0
% 14.56/8.26  #Chain   : 0
% 14.56/8.26  #Close   : 0
% 14.56/8.26  
% 14.56/8.26  Ordering : KBO
% 14.56/8.26  
% 14.56/8.26  Simplification rules
% 14.56/8.26  ----------------------
% 14.56/8.26  #Subsume      : 145
% 14.56/8.26  #Demod        : 17275
% 14.56/8.26  #Tautology    : 9512
% 14.56/8.26  #SimpNegUnit  : 0
% 14.56/8.26  #BackRed      : 6
% 14.56/8.26  
% 14.56/8.26  #Partial instantiations: 0
% 14.56/8.26  #Strategies tried      : 1
% 14.56/8.26  
% 14.56/8.26  Timing (in seconds)
% 14.56/8.26  ----------------------
% 14.56/8.27  Preprocessing        : 0.28
% 14.56/8.27  Parsing              : 0.16
% 14.56/8.27  CNF conversion       : 0.02
% 14.56/8.27  Main loop            : 7.22
% 14.56/8.27  Inferencing          : 1.07
% 14.56/8.27  Reduction            : 4.59
% 14.56/8.27  Demodulation         : 4.25
% 14.56/8.27  BG Simplification    : 0.14
% 14.56/8.27  Subsumption          : 1.13
% 14.56/8.27  Abstraction          : 0.27
% 14.56/8.27  MUC search           : 0.00
% 14.56/8.27  Cooper               : 0.00
% 14.56/8.27  Total                : 7.53
% 14.56/8.27  Index Insertion      : 0.00
% 14.56/8.27  Index Deletion       : 0.00
% 14.56/8.27  Index Matching       : 0.00
% 14.56/8.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

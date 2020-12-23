%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 14.29s
% Output     : CNFRefutation 14.60s
% Verified   : 
% Statistics : Number of formulae       :  109 (1120 expanded)
%              Number of leaves         :   21 ( 385 expanded)
%              Depth                    :   19
%              Number of atoms          :   99 (1110 expanded)
%              Number of equality atoms :   98 (1109 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [B_23,A_24] : k5_xboole_0(B_23,A_24) = k5_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_14])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_371,plain,(
    ! [A_40,B_41,C_42] : k5_xboole_0(k5_xboole_0(A_40,B_41),C_42) = k5_xboole_0(A_40,k5_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_424,plain,(
    ! [A_17,C_42] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_42)) = k5_xboole_0(k1_xboole_0,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_371])).

tff(c_438,plain,(
    ! [A_43,C_44] : k5_xboole_0(A_43,k5_xboole_0(A_43,C_44)) = C_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_424])).

tff(c_916,plain,(
    ! [B_57,A_58] : k5_xboole_0(B_57,k5_xboole_0(A_58,B_57)) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_438])).

tff(c_481,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_438])).

tff(c_919,plain,(
    ! [A_58,B_57] : k5_xboole_0(k5_xboole_0(A_58,B_57),A_58) = B_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_481])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_162,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_162])).

tff(c_288,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k4_xboole_0(A_37,B_38),C_39) = k4_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_336,plain,(
    ! [A_5,C_39] : k4_xboole_0(k3_xboole_0(A_5,k1_xboole_0),C_39) = k4_xboole_0(A_5,k2_xboole_0(A_5,C_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_288])).

tff(c_500,plain,(
    ! [A_45,C_46] : k4_xboole_0(k3_xboole_0(A_45,k1_xboole_0),C_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_336])).

tff(c_530,plain,(
    ! [A_45] : k3_xboole_0(A_45,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_6])).

tff(c_725,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_180])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_737,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,k4_xboole_0(A_6,B_7))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_8])).

tff(c_1222,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k2_xboole_0(B_64,A_63)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_737])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1240,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k2_xboole_0(B_64,A_63)) = k4_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_12])).

tff(c_1285,plain,(
    ! [A_65,B_66] : k3_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1240])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1295,plain,(
    ! [A_65,B_66] : k5_xboole_0(k5_xboole_0(A_65,k2_xboole_0(B_66,A_65)),A_65) = k2_xboole_0(A_65,k2_xboole_0(B_66,A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_20])).

tff(c_1325,plain,(
    ! [A_65,B_66] : k2_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = k2_xboole_0(B_66,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_1295])).

tff(c_640,plain,(
    ! [A_49,B_50] : k5_xboole_0(k5_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_701,plain,(
    ! [A_13] : k5_xboole_0(A_13,k3_xboole_0(A_13,k1_xboole_0)) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_640])).

tff(c_708,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_530,c_701])).

tff(c_218,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_239,plain,(
    ! [A_9,B_10] : k2_xboole_0(k2_xboole_0(A_9,B_10),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_4733,plain,(
    ! [A_9,B_10] : k2_xboole_0(k2_xboole_0(A_9,B_10),A_9) = k2_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_239])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3618,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k5_xboole_0(B_113,k3_xboole_0(A_112,B_113))) = k2_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_16])).

tff(c_437,plain,(
    ! [A_17,C_42] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_42)) = C_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_424])).

tff(c_5099,plain,(
    ! [B_132,A_133] : k5_xboole_0(B_132,k3_xboole_0(A_133,B_132)) = k5_xboole_0(A_133,k2_xboole_0(A_133,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3618,c_437])).

tff(c_5237,plain,(
    ! [A_9,B_10] : k5_xboole_0(k2_xboole_0(A_9,B_10),k2_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,k3_xboole_0(k2_xboole_0(A_9,B_10),A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4733,c_5099])).

tff(c_7828,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k3_xboole_0(k2_xboole_0(A_162,B_163),A_162)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5237])).

tff(c_7879,plain,(
    ! [A_162,B_163] : k3_xboole_0(k2_xboole_0(A_162,B_163),A_162) = k5_xboole_0(k1_xboole_0,A_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_7828,c_919])).

tff(c_8005,plain,(
    ! [A_164,B_165] : k3_xboole_0(k2_xboole_0(A_164,B_165),A_164) = A_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7879])).

tff(c_8090,plain,(
    ! [B_66,A_65] : k3_xboole_0(k2_xboole_0(B_66,A_65),A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_8005])).

tff(c_7983,plain,(
    ! [A_162,B_163] : k3_xboole_0(k2_xboole_0(A_162,B_163),A_162) = A_162 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7879])).

tff(c_629,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_180])).

tff(c_5333,plain,(
    ! [C_134,A_135,B_136] : k2_xboole_0(C_134,k4_xboole_0(A_135,k2_xboole_0(B_136,C_134))) = k2_xboole_0(C_134,k4_xboole_0(A_135,B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_4])).

tff(c_5470,plain,(
    ! [C_134,B_136] : k2_xboole_0(C_134,k4_xboole_0(k2_xboole_0(B_136,C_134),B_136)) = k2_xboole_0(C_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_5333])).

tff(c_5522,plain,(
    ! [C_134,B_136] : k2_xboole_0(C_134,k4_xboole_0(k2_xboole_0(B_136,C_134),B_136)) = C_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_5470])).

tff(c_7623,plain,(
    ! [C_160,B_161] : k2_xboole_0(C_160,k4_xboole_0(k2_xboole_0(B_161,C_160),B_161)) = C_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_5470])).

tff(c_7668,plain,(
    ! [B_161,C_160] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_161,C_160),B_161),C_160) = k2_xboole_0(C_160,k4_xboole_0(k2_xboole_0(B_161,C_160),B_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7623,c_1325])).

tff(c_12227,plain,(
    ! [B_212,C_213] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_212,C_213),B_212),C_213) = C_213 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5522,c_7668])).

tff(c_343,plain,(
    ! [A_11,B_12,C_39] : k4_xboole_0(A_11,k2_xboole_0(k4_xboole_0(A_11,B_12),C_39)) = k4_xboole_0(k3_xboole_0(A_11,B_12),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_288])).

tff(c_12257,plain,(
    ! [B_212,C_213] : k4_xboole_0(k3_xboole_0(k2_xboole_0(B_212,C_213),B_212),C_213) = k4_xboole_0(k2_xboole_0(B_212,C_213),C_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_12227,c_343])).

tff(c_23358,plain,(
    ! [B_300,C_301] : k4_xboole_0(k2_xboole_0(B_300,C_301),C_301) = k4_xboole_0(B_300,C_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7983,c_12257])).

tff(c_764,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,A_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_737])).

tff(c_5456,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_5333])).

tff(c_5527,plain,(
    ! [A_137,B_138] : k2_xboole_0(A_137,k4_xboole_0(A_137,B_138)) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_5456])).

tff(c_5670,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5527])).

tff(c_5843,plain,(
    ! [A_141,B_142] : k2_xboole_0(A_141,k3_xboole_0(A_141,B_142)) = A_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5527])).

tff(c_5881,plain,(
    ! [A_141,B_142] : k2_xboole_0(k3_xboole_0(A_141,B_142),A_141) = k2_xboole_0(A_141,k3_xboole_0(A_141,B_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5843,c_1325])).

tff(c_5970,plain,(
    ! [A_141,B_142] : k2_xboole_0(k3_xboole_0(A_141,B_142),A_141) = A_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5670,c_5881])).

tff(c_5518,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_5456])).

tff(c_8673,plain,(
    ! [A_173,B_174] : k5_xboole_0(k5_xboole_0(A_173,B_174),k2_xboole_0(A_173,B_174)) = k3_xboole_0(A_173,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_437])).

tff(c_8781,plain,(
    ! [A_6,B_7] : k5_xboole_0(k5_xboole_0(A_6,k4_xboole_0(A_6,B_7)),A_6) = k3_xboole_0(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5518,c_8673])).

tff(c_8908,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_8781])).

tff(c_165,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_12])).

tff(c_10354,plain,(
    ! [A_191,B_192] : k4_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k4_xboole_0(A_191,B_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8908,c_165])).

tff(c_10411,plain,(
    ! [A_191,B_192] : k2_xboole_0(k3_xboole_0(A_191,B_192),k4_xboole_0(A_191,B_192)) = k2_xboole_0(k3_xboole_0(A_191,B_192),A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_10354,c_4])).

tff(c_10483,plain,(
    ! [A_191,B_192] : k2_xboole_0(k3_xboole_0(A_191,B_192),k4_xboole_0(A_191,B_192)) = A_191 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5970,c_10411])).

tff(c_23449,plain,(
    ! [B_300,C_301] : k2_xboole_0(k3_xboole_0(k2_xboole_0(B_300,C_301),C_301),k4_xboole_0(B_300,C_301)) = k2_xboole_0(B_300,C_301) ),
    inference(superposition,[status(thm),theory(equality)],[c_23358,c_10483])).

tff(c_23619,plain,(
    ! [C_301,B_300] : k2_xboole_0(C_301,B_300) = k2_xboole_0(B_300,C_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8090,c_23449])).

tff(c_740,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = k2_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_4])).

tff(c_765,plain,(
    ! [A_52] : k2_xboole_0(A_52,A_52) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_740])).

tff(c_13267,plain,(
    ! [A_223,B_224,C_225] : k4_xboole_0(k4_xboole_0(A_223,B_224),k4_xboole_0(A_223,k2_xboole_0(B_224,C_225))) = k3_xboole_0(k4_xboole_0(A_223,B_224),C_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_12])).

tff(c_13513,plain,(
    ! [A_223,A_52] : k4_xboole_0(k4_xboole_0(A_223,A_52),k4_xboole_0(A_223,A_52)) = k3_xboole_0(k4_xboole_0(A_223,A_52),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_13267])).

tff(c_13632,plain,(
    ! [A_226,A_227] : k3_xboole_0(k4_xboole_0(A_226,A_227),A_227) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_13513])).

tff(c_14771,plain,(
    ! [A_237,B_238] : k3_xboole_0(k3_xboole_0(A_237,B_238),k4_xboole_0(A_237,B_238)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_13632])).

tff(c_3664,plain,(
    ! [B_113,A_112] : k5_xboole_0(B_113,k3_xboole_0(A_112,B_113)) = k5_xboole_0(A_112,k2_xboole_0(A_112,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3618,c_437])).

tff(c_14842,plain,(
    ! [A_237,B_238] : k5_xboole_0(k3_xboole_0(A_237,B_238),k2_xboole_0(k3_xboole_0(A_237,B_238),k4_xboole_0(A_237,B_238))) = k5_xboole_0(k4_xboole_0(A_237,B_238),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14771,c_3664])).

tff(c_15025,plain,(
    ! [A_237,B_238] : k5_xboole_0(A_237,k3_xboole_0(A_237,B_238)) = k4_xboole_0(A_237,B_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10483,c_14,c_14842])).

tff(c_3765,plain,(
    ! [A_114,B_115] : k5_xboole_0(k5_xboole_0(A_114,B_115),k3_xboole_0(B_115,A_114)) = k2_xboole_0(B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_640])).

tff(c_3817,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k5_xboole_0(B_115,k3_xboole_0(B_115,A_114))) = k2_xboole_0(B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_3765,c_16])).

tff(c_19041,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(B_115,A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15025,c_3817])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19266,plain,(
    k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19041,c_22])).

tff(c_24817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23619,c_19266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.29/6.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.42/6.84  
% 14.42/6.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.42/6.85  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 14.42/6.85  
% 14.42/6.85  %Foreground sorts:
% 14.42/6.85  
% 14.42/6.85  
% 14.42/6.85  %Background operators:
% 14.42/6.85  
% 14.42/6.85  
% 14.42/6.85  %Foreground operators:
% 14.42/6.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.42/6.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.42/6.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.42/6.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.42/6.85  tff('#skF_2', type, '#skF_2': $i).
% 14.42/6.85  tff('#skF_1', type, '#skF_1': $i).
% 14.42/6.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.42/6.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.42/6.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.42/6.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.42/6.85  
% 14.60/6.88  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.60/6.88  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.60/6.88  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 14.60/6.88  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.60/6.88  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.60/6.88  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.60/6.88  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.60/6.88  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.60/6.88  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.60/6.88  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.60/6.88  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 14.60/6.88  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.60/6.88  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.60/6.88  tff(c_58, plain, (![B_23, A_24]: (k5_xboole_0(B_23, A_24)=k5_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.60/6.88  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.60/6.88  tff(c_74, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_58, c_14])).
% 14.60/6.88  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.60/6.88  tff(c_371, plain, (![A_40, B_41, C_42]: (k5_xboole_0(k5_xboole_0(A_40, B_41), C_42)=k5_xboole_0(A_40, k5_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.60/6.88  tff(c_424, plain, (![A_17, C_42]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_42))=k5_xboole_0(k1_xboole_0, C_42))), inference(superposition, [status(thm), theory('equality')], [c_18, c_371])).
% 14.60/6.88  tff(c_438, plain, (![A_43, C_44]: (k5_xboole_0(A_43, k5_xboole_0(A_43, C_44))=C_44)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_424])).
% 14.60/6.88  tff(c_916, plain, (![B_57, A_58]: (k5_xboole_0(B_57, k5_xboole_0(A_58, B_57))=A_58)), inference(superposition, [status(thm), theory('equality')], [c_2, c_438])).
% 14.60/6.88  tff(c_481, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_438])).
% 14.60/6.88  tff(c_919, plain, (![A_58, B_57]: (k5_xboole_0(k5_xboole_0(A_58, B_57), A_58)=B_57)), inference(superposition, [status(thm), theory('equality')], [c_916, c_481])).
% 14.60/6.88  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.60/6.88  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.60/6.88  tff(c_162, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.60/6.88  tff(c_180, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_162])).
% 14.60/6.88  tff(c_288, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k4_xboole_0(A_37, B_38), C_39)=k4_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.60/6.88  tff(c_336, plain, (![A_5, C_39]: (k4_xboole_0(k3_xboole_0(A_5, k1_xboole_0), C_39)=k4_xboole_0(A_5, k2_xboole_0(A_5, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_288])).
% 14.60/6.88  tff(c_500, plain, (![A_45, C_46]: (k4_xboole_0(k3_xboole_0(A_45, k1_xboole_0), C_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_336])).
% 14.60/6.88  tff(c_530, plain, (![A_45]: (k3_xboole_0(A_45, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_500, c_6])).
% 14.60/6.88  tff(c_725, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_530, c_180])).
% 14.60/6.88  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.60/6.88  tff(c_737, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, k4_xboole_0(A_6, B_7)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_725, c_8])).
% 14.60/6.88  tff(c_1222, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k2_xboole_0(B_64, A_63))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_737])).
% 14.60/6.88  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.60/6.88  tff(c_1240, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k2_xboole_0(B_64, A_63))=k4_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_12])).
% 14.60/6.88  tff(c_1285, plain, (![A_65, B_66]: (k3_xboole_0(A_65, k2_xboole_0(B_66, A_65))=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1240])).
% 14.60/6.88  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.60/6.88  tff(c_1295, plain, (![A_65, B_66]: (k5_xboole_0(k5_xboole_0(A_65, k2_xboole_0(B_66, A_65)), A_65)=k2_xboole_0(A_65, k2_xboole_0(B_66, A_65)))), inference(superposition, [status(thm), theory('equality')], [c_1285, c_20])).
% 14.60/6.88  tff(c_1325, plain, (![A_65, B_66]: (k2_xboole_0(A_65, k2_xboole_0(B_66, A_65))=k2_xboole_0(B_66, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_1295])).
% 14.60/6.88  tff(c_640, plain, (![A_49, B_50]: (k5_xboole_0(k5_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.60/6.88  tff(c_701, plain, (![A_13]: (k5_xboole_0(A_13, k3_xboole_0(A_13, k1_xboole_0))=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_640])).
% 14.60/6.88  tff(c_708, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_530, c_701])).
% 14.60/6.88  tff(c_218, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.60/6.88  tff(c_239, plain, (![A_9, B_10]: (k2_xboole_0(k2_xboole_0(A_9, B_10), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_218])).
% 14.60/6.88  tff(c_4733, plain, (![A_9, B_10]: (k2_xboole_0(k2_xboole_0(A_9, B_10), A_9)=k2_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_239])).
% 14.60/6.88  tff(c_16, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.60/6.88  tff(c_3618, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k5_xboole_0(B_113, k3_xboole_0(A_112, B_113)))=k2_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_640, c_16])).
% 14.60/6.88  tff(c_437, plain, (![A_17, C_42]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_42))=C_42)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_424])).
% 14.60/6.88  tff(c_5099, plain, (![B_132, A_133]: (k5_xboole_0(B_132, k3_xboole_0(A_133, B_132))=k5_xboole_0(A_133, k2_xboole_0(A_133, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_3618, c_437])).
% 14.60/6.88  tff(c_5237, plain, (![A_9, B_10]: (k5_xboole_0(k2_xboole_0(A_9, B_10), k2_xboole_0(A_9, B_10))=k5_xboole_0(A_9, k3_xboole_0(k2_xboole_0(A_9, B_10), A_9)))), inference(superposition, [status(thm), theory('equality')], [c_4733, c_5099])).
% 14.60/6.88  tff(c_7828, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k3_xboole_0(k2_xboole_0(A_162, B_163), A_162))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5237])).
% 14.60/6.88  tff(c_7879, plain, (![A_162, B_163]: (k3_xboole_0(k2_xboole_0(A_162, B_163), A_162)=k5_xboole_0(k1_xboole_0, A_162))), inference(superposition, [status(thm), theory('equality')], [c_7828, c_919])).
% 14.60/6.88  tff(c_8005, plain, (![A_164, B_165]: (k3_xboole_0(k2_xboole_0(A_164, B_165), A_164)=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7879])).
% 14.60/6.88  tff(c_8090, plain, (![B_66, A_65]: (k3_xboole_0(k2_xboole_0(B_66, A_65), A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_1325, c_8005])).
% 14.60/6.88  tff(c_7983, plain, (![A_162, B_163]: (k3_xboole_0(k2_xboole_0(A_162, B_163), A_162)=A_162)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7879])).
% 14.60/6.88  tff(c_629, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_530, c_180])).
% 14.60/6.88  tff(c_5333, plain, (![C_134, A_135, B_136]: (k2_xboole_0(C_134, k4_xboole_0(A_135, k2_xboole_0(B_136, C_134)))=k2_xboole_0(C_134, k4_xboole_0(A_135, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_4])).
% 14.60/6.88  tff(c_5470, plain, (![C_134, B_136]: (k2_xboole_0(C_134, k4_xboole_0(k2_xboole_0(B_136, C_134), B_136))=k2_xboole_0(C_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_629, c_5333])).
% 14.60/6.88  tff(c_5522, plain, (![C_134, B_136]: (k2_xboole_0(C_134, k4_xboole_0(k2_xboole_0(B_136, C_134), B_136))=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_708, c_5470])).
% 14.60/6.88  tff(c_7623, plain, (![C_160, B_161]: (k2_xboole_0(C_160, k4_xboole_0(k2_xboole_0(B_161, C_160), B_161))=C_160)), inference(demodulation, [status(thm), theory('equality')], [c_708, c_5470])).
% 14.60/6.88  tff(c_7668, plain, (![B_161, C_160]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_161, C_160), B_161), C_160)=k2_xboole_0(C_160, k4_xboole_0(k2_xboole_0(B_161, C_160), B_161)))), inference(superposition, [status(thm), theory('equality')], [c_7623, c_1325])).
% 14.60/6.88  tff(c_12227, plain, (![B_212, C_213]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_212, C_213), B_212), C_213)=C_213)), inference(demodulation, [status(thm), theory('equality')], [c_5522, c_7668])).
% 14.60/6.88  tff(c_343, plain, (![A_11, B_12, C_39]: (k4_xboole_0(A_11, k2_xboole_0(k4_xboole_0(A_11, B_12), C_39))=k4_xboole_0(k3_xboole_0(A_11, B_12), C_39))), inference(superposition, [status(thm), theory('equality')], [c_12, c_288])).
% 14.60/6.88  tff(c_12257, plain, (![B_212, C_213]: (k4_xboole_0(k3_xboole_0(k2_xboole_0(B_212, C_213), B_212), C_213)=k4_xboole_0(k2_xboole_0(B_212, C_213), C_213))), inference(superposition, [status(thm), theory('equality')], [c_12227, c_343])).
% 14.60/6.88  tff(c_23358, plain, (![B_300, C_301]: (k4_xboole_0(k2_xboole_0(B_300, C_301), C_301)=k4_xboole_0(B_300, C_301))), inference(demodulation, [status(thm), theory('equality')], [c_7983, c_12257])).
% 14.60/6.88  tff(c_764, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, A_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_737])).
% 14.60/6.88  tff(c_5456, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_764, c_5333])).
% 14.60/6.88  tff(c_5527, plain, (![A_137, B_138]: (k2_xboole_0(A_137, k4_xboole_0(A_137, B_138))=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_708, c_5456])).
% 14.60/6.88  tff(c_5670, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(superposition, [status(thm), theory('equality')], [c_12, c_5527])).
% 14.60/6.88  tff(c_5843, plain, (![A_141, B_142]: (k2_xboole_0(A_141, k3_xboole_0(A_141, B_142))=A_141)), inference(superposition, [status(thm), theory('equality')], [c_12, c_5527])).
% 14.60/6.88  tff(c_5881, plain, (![A_141, B_142]: (k2_xboole_0(k3_xboole_0(A_141, B_142), A_141)=k2_xboole_0(A_141, k3_xboole_0(A_141, B_142)))), inference(superposition, [status(thm), theory('equality')], [c_5843, c_1325])).
% 14.60/6.88  tff(c_5970, plain, (![A_141, B_142]: (k2_xboole_0(k3_xboole_0(A_141, B_142), A_141)=A_141)), inference(demodulation, [status(thm), theory('equality')], [c_5670, c_5881])).
% 14.60/6.88  tff(c_5518, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_708, c_5456])).
% 14.60/6.88  tff(c_8673, plain, (![A_173, B_174]: (k5_xboole_0(k5_xboole_0(A_173, B_174), k2_xboole_0(A_173, B_174))=k3_xboole_0(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_640, c_437])).
% 14.60/6.88  tff(c_8781, plain, (![A_6, B_7]: (k5_xboole_0(k5_xboole_0(A_6, k4_xboole_0(A_6, B_7)), A_6)=k3_xboole_0(A_6, k4_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_5518, c_8673])).
% 14.60/6.88  tff(c_8908, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_8781])).
% 14.60/6.88  tff(c_165, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k3_xboole_0(A_28, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_12])).
% 14.60/6.88  tff(c_10354, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k4_xboole_0(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_8908, c_165])).
% 14.60/6.88  tff(c_10411, plain, (![A_191, B_192]: (k2_xboole_0(k3_xboole_0(A_191, B_192), k4_xboole_0(A_191, B_192))=k2_xboole_0(k3_xboole_0(A_191, B_192), A_191))), inference(superposition, [status(thm), theory('equality')], [c_10354, c_4])).
% 14.60/6.88  tff(c_10483, plain, (![A_191, B_192]: (k2_xboole_0(k3_xboole_0(A_191, B_192), k4_xboole_0(A_191, B_192))=A_191)), inference(demodulation, [status(thm), theory('equality')], [c_5970, c_10411])).
% 14.60/6.88  tff(c_23449, plain, (![B_300, C_301]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(B_300, C_301), C_301), k4_xboole_0(B_300, C_301))=k2_xboole_0(B_300, C_301))), inference(superposition, [status(thm), theory('equality')], [c_23358, c_10483])).
% 14.60/6.88  tff(c_23619, plain, (![C_301, B_300]: (k2_xboole_0(C_301, B_300)=k2_xboole_0(B_300, C_301))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8090, c_23449])).
% 14.60/6.88  tff(c_740, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=k2_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_725, c_4])).
% 14.60/6.88  tff(c_765, plain, (![A_52]: (k2_xboole_0(A_52, A_52)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_708, c_740])).
% 14.60/6.88  tff(c_13267, plain, (![A_223, B_224, C_225]: (k4_xboole_0(k4_xboole_0(A_223, B_224), k4_xboole_0(A_223, k2_xboole_0(B_224, C_225)))=k3_xboole_0(k4_xboole_0(A_223, B_224), C_225))), inference(superposition, [status(thm), theory('equality')], [c_288, c_12])).
% 14.60/6.88  tff(c_13513, plain, (![A_223, A_52]: (k4_xboole_0(k4_xboole_0(A_223, A_52), k4_xboole_0(A_223, A_52))=k3_xboole_0(k4_xboole_0(A_223, A_52), A_52))), inference(superposition, [status(thm), theory('equality')], [c_765, c_13267])).
% 14.60/6.88  tff(c_13632, plain, (![A_226, A_227]: (k3_xboole_0(k4_xboole_0(A_226, A_227), A_227)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_629, c_13513])).
% 14.60/6.88  tff(c_14771, plain, (![A_237, B_238]: (k3_xboole_0(k3_xboole_0(A_237, B_238), k4_xboole_0(A_237, B_238))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_13632])).
% 14.60/6.88  tff(c_3664, plain, (![B_113, A_112]: (k5_xboole_0(B_113, k3_xboole_0(A_112, B_113))=k5_xboole_0(A_112, k2_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_3618, c_437])).
% 14.60/6.88  tff(c_14842, plain, (![A_237, B_238]: (k5_xboole_0(k3_xboole_0(A_237, B_238), k2_xboole_0(k3_xboole_0(A_237, B_238), k4_xboole_0(A_237, B_238)))=k5_xboole_0(k4_xboole_0(A_237, B_238), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14771, c_3664])).
% 14.60/6.88  tff(c_15025, plain, (![A_237, B_238]: (k5_xboole_0(A_237, k3_xboole_0(A_237, B_238))=k4_xboole_0(A_237, B_238))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10483, c_14, c_14842])).
% 14.60/6.88  tff(c_3765, plain, (![A_114, B_115]: (k5_xboole_0(k5_xboole_0(A_114, B_115), k3_xboole_0(B_115, A_114))=k2_xboole_0(B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_640])).
% 14.60/6.88  tff(c_3817, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k5_xboole_0(B_115, k3_xboole_0(B_115, A_114)))=k2_xboole_0(B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_3765, c_16])).
% 14.60/6.88  tff(c_19041, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(B_115, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_15025, c_3817])).
% 14.60/6.88  tff(c_22, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.60/6.88  tff(c_19266, plain, (k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19041, c_22])).
% 14.60/6.88  tff(c_24817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23619, c_19266])).
% 14.60/6.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.60/6.88  
% 14.60/6.88  Inference rules
% 14.60/6.88  ----------------------
% 14.60/6.88  #Ref     : 0
% 14.60/6.88  #Sup     : 6296
% 14.60/6.88  #Fact    : 0
% 14.60/6.88  #Define  : 0
% 14.60/6.88  #Split   : 0
% 14.60/6.88  #Chain   : 0
% 14.60/6.88  #Close   : 0
% 14.60/6.88  
% 14.60/6.88  Ordering : KBO
% 14.60/6.88  
% 14.60/6.88  Simplification rules
% 14.60/6.88  ----------------------
% 14.60/6.88  #Subsume      : 104
% 14.60/6.88  #Demod        : 7484
% 14.60/6.88  #Tautology    : 3855
% 14.60/6.88  #SimpNegUnit  : 0
% 14.60/6.88  #BackRed      : 14
% 14.60/6.88  
% 14.60/6.88  #Partial instantiations: 0
% 14.60/6.88  #Strategies tried      : 1
% 14.60/6.88  
% 14.60/6.88  Timing (in seconds)
% 14.60/6.88  ----------------------
% 14.60/6.89  Preprocessing        : 0.43
% 14.60/6.89  Parsing              : 0.23
% 14.60/6.89  CNF conversion       : 0.03
% 14.60/6.89  Main loop            : 5.56
% 14.60/6.89  Inferencing          : 1.12
% 14.60/6.89  Reduction            : 3.28
% 14.60/6.89  Demodulation         : 2.98
% 14.60/6.89  BG Simplification    : 0.17
% 14.60/6.89  Subsumption          : 0.74
% 14.60/6.89  Abstraction          : 0.26
% 14.60/6.89  MUC search           : 0.00
% 14.60/6.89  Cooper               : 0.00
% 14.60/6.89  Total                : 6.06
% 14.60/6.89  Index Insertion      : 0.00
% 14.60/6.89  Index Deletion       : 0.00
% 14.60/6.89  Index Matching       : 0.00
% 14.60/6.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------

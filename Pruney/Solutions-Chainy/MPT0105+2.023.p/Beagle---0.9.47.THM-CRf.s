%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 14.50s
% Output     : CNFRefutation 14.50s
% Verified   : 
% Statistics : Number of formulae       :  101 (1025 expanded)
%              Number of leaves         :   21 ( 362 expanded)
%              Depth                    :   17
%              Number of atoms          :   91 (1015 expanded)
%              Number of equality atoms :   90 (1014 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_101,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_127,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_122])).

tff(c_273,plain,(
    ! [A_39,B_40] : k4_xboole_0(k2_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k5_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_306,plain,(
    ! [A_5] : k4_xboole_0(A_5,k3_xboole_0(A_5,k1_xboole_0)) = k5_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_273])).

tff(c_314,plain,(
    ! [A_41] : k5_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_127,c_306])).

tff(c_330,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_314])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_541,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_588,plain,(
    ! [A_5,C_51] : k4_xboole_0(A_5,k2_xboole_0(A_5,C_51)) = k4_xboole_0(k1_xboole_0,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_541])).

tff(c_618,plain,(
    ! [C_52] : k4_xboole_0(k1_xboole_0,C_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_588])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_629,plain,(
    ! [C_52] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_16])).

tff(c_671,plain,(
    ! [C_53] : k3_xboole_0(k1_xboole_0,C_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_629])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_679,plain,(
    ! [C_53] : k4_xboole_0(k2_xboole_0(k1_xboole_0,C_53),k1_xboole_0) = k5_xboole_0(k1_xboole_0,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_4])).

tff(c_706,plain,(
    ! [C_53] : k2_xboole_0(k1_xboole_0,C_53) = C_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_10,c_679])).

tff(c_313,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_127,c_306])).

tff(c_154,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_154])).

tff(c_179,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_14656,plain,(
    ! [A_233,B_234,C_235] : k4_xboole_0(k4_xboole_0(A_233,B_234),k4_xboole_0(A_233,k2_xboole_0(B_234,C_235))) = k3_xboole_0(k4_xboole_0(A_233,B_234),C_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_16])).

tff(c_14984,plain,(
    ! [A_233,A_5] : k4_xboole_0(k4_xboole_0(A_233,A_5),k4_xboole_0(A_233,A_5)) = k3_xboole_0(k4_xboole_0(A_233,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_14656])).

tff(c_15094,plain,(
    ! [A_233,A_5] : k3_xboole_0(k4_xboole_0(A_233,A_5),A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_14984])).

tff(c_119,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_126,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_119])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_430,plain,(
    ! [A_46,B_47] : k5_xboole_0(k5_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_464,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k5_xboole_0(B_17,k3_xboole_0(A_16,B_17))) = k2_xboole_0(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_116,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_101])).

tff(c_125,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_116])).

tff(c_294,plain,(
    ! [A_5] : k4_xboole_0(A_5,k3_xboole_0(A_5,A_5)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_273])).

tff(c_496,plain,(
    ! [A_48] : k5_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_125,c_294])).

tff(c_508,plain,(
    ! [A_48,C_18] : k5_xboole_0(A_48,k5_xboole_0(A_48,C_18)) = k5_xboole_0(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_18])).

tff(c_534,plain,(
    ! [A_48,C_18] : k5_xboole_0(A_48,k5_xboole_0(A_48,C_18)) = C_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_508])).

tff(c_15103,plain,(
    ! [A_236,A_237] : k3_xboole_0(k4_xboole_0(A_236,A_237),A_237) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_14984])).

tff(c_16851,plain,(
    ! [A_249,B_250] : k3_xboole_0(k5_xboole_0(A_249,B_250),k3_xboole_0(A_249,B_250)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_15103])).

tff(c_18073,plain,(
    ! [C_258,A_259] : k3_xboole_0(C_258,k3_xboole_0(A_259,k5_xboole_0(A_259,C_258))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_16851])).

tff(c_18226,plain,(
    ! [B_17,A_16] : k3_xboole_0(k5_xboole_0(B_17,k3_xboole_0(A_16,B_17)),k3_xboole_0(A_16,k2_xboole_0(A_16,B_17))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_18073])).

tff(c_21285,plain,(
    ! [B_280,A_281] : k3_xboole_0(k5_xboole_0(B_280,k3_xboole_0(A_281,B_280)),A_281) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_18226])).

tff(c_21448,plain,(
    ! [A_5,A_233] : k3_xboole_0(k5_xboole_0(A_5,k1_xboole_0),k4_xboole_0(A_233,A_5)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15094,c_21285])).

tff(c_21557,plain,(
    ! [A_5,A_233] : k3_xboole_0(A_5,k4_xboole_0(A_233,A_5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_21448])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_592,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,k4_xboole_0(A_49,B_50))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_541])).

tff(c_616,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_592])).

tff(c_4702,plain,(
    ! [C_126,A_127,B_128] : k2_xboole_0(C_126,k4_xboole_0(A_127,k2_xboole_0(B_128,C_126))) = k2_xboole_0(C_126,k4_xboole_0(A_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_8])).

tff(c_4825,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k2_xboole_0(A_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_4702])).

tff(c_4889,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4825])).

tff(c_4899,plain,(
    ! [A_129,B_130] : k2_xboole_0(A_129,k4_xboole_0(A_129,B_130)) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4825])).

tff(c_772,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(B_56,A_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_592])).

tff(c_790,plain,(
    ! [A_55,B_56] : k3_xboole_0(A_55,k2_xboole_0(B_56,A_55)) = k4_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_16])).

tff(c_825,plain,(
    ! [A_55,B_56] : k3_xboole_0(A_55,k2_xboole_0(B_56,A_55)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_790])).

tff(c_1261,plain,(
    ! [A_67,B_68] : k5_xboole_0(k3_xboole_0(A_67,B_68),k5_xboole_0(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_1306,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k5_xboole_0(A_55,k2_xboole_0(B_56,A_55))) = k2_xboole_0(A_55,k2_xboole_0(B_56,A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_1261])).

tff(c_1343,plain,(
    ! [A_55,B_56] : k2_xboole_0(A_55,k2_xboole_0(B_56,A_55)) = k2_xboole_0(B_56,A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_1306])).

tff(c_4942,plain,(
    ! [A_129,B_130] : k2_xboole_0(k4_xboole_0(A_129,B_130),A_129) = k2_xboole_0(A_129,k4_xboole_0(A_129,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4899,c_1343])).

tff(c_5064,plain,(
    ! [A_129,B_130] : k2_xboole_0(k4_xboole_0(A_129,B_130),A_129) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_4942])).

tff(c_7464,plain,(
    ! [A_161,B_162] : k3_xboole_0(k4_xboole_0(A_161,B_162),A_161) = k4_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_4899,c_825])).

tff(c_7509,plain,(
    ! [A_161,B_162] : k4_xboole_0(k2_xboole_0(k4_xboole_0(A_161,B_162),A_161),k4_xboole_0(A_161,B_162)) = k5_xboole_0(k4_xboole_0(A_161,B_162),A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_7464,c_4])).

tff(c_9573,plain,(
    ! [A_186,B_187] : k5_xboole_0(A_186,k4_xboole_0(A_186,B_187)) = k3_xboole_0(A_186,B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5064,c_2,c_7509])).

tff(c_9622,plain,(
    ! [A_186,B_187] : k5_xboole_0(A_186,k3_xboole_0(A_186,B_187)) = k4_xboole_0(A_186,B_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_9573,c_534])).

tff(c_337,plain,(
    ! [A_42,B_43,C_44] : k5_xboole_0(k5_xboole_0(A_42,B_43),C_44) = k5_xboole_0(A_42,k5_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_353,plain,(
    ! [C_44,A_42,B_43] : k5_xboole_0(C_44,k5_xboole_0(A_42,B_43)) = k5_xboole_0(A_42,k5_xboole_0(B_43,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_2])).

tff(c_3315,plain,(
    ! [C_112,A_113,B_114] : k5_xboole_0(C_112,k5_xboole_0(A_113,B_114)) = k5_xboole_0(A_113,k5_xboole_0(B_114,C_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_2])).

tff(c_3580,plain,(
    ! [A_1,C_112] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_1,C_112)) = k5_xboole_0(C_112,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_3315])).

tff(c_22904,plain,(
    ! [A_290,B_291,C_292] : k5_xboole_0(k5_xboole_0(A_290,k5_xboole_0(B_291,C_292)),k3_xboole_0(k5_xboole_0(A_290,B_291),C_292)) = k2_xboole_0(k5_xboole_0(A_290,B_291),C_292) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_23147,plain,(
    ! [C_112,A_1] : k5_xboole_0(k5_xboole_0(C_112,A_1),k3_xboole_0(k5_xboole_0(k1_xboole_0,A_1),C_112)) = k2_xboole_0(k5_xboole_0(k1_xboole_0,A_1),C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_3580,c_22904])).

tff(c_24063,plain,(
    ! [C_297,A_298] : k5_xboole_0(C_297,k4_xboole_0(A_298,C_297)) = k2_xboole_0(A_298,C_297) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9622,c_353,c_330,c_2,c_330,c_23147])).

tff(c_279,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k5_xboole_0(A_39,B_40)) = k2_xboole_0(k3_xboole_0(A_39,B_40),k2_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_8])).

tff(c_24118,plain,(
    ! [C_297,A_298] : k2_xboole_0(k3_xboole_0(C_297,k4_xboole_0(A_298,C_297)),k2_xboole_0(C_297,k4_xboole_0(A_298,C_297))) = k2_xboole_0(k3_xboole_0(C_297,k4_xboole_0(A_298,C_297)),k2_xboole_0(A_298,C_297)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24063,c_279])).

tff(c_24326,plain,(
    ! [C_297,A_298] : k2_xboole_0(C_297,A_298) = k2_xboole_0(A_298,C_297) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_21557,c_706,c_21557,c_8,c_24118])).

tff(c_23373,plain,(
    ! [C_112,A_1] : k5_xboole_0(C_112,k4_xboole_0(A_1,C_112)) = k2_xboole_0(A_1,C_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9622,c_353,c_330,c_2,c_330,c_23147])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24062,plain,(
    k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23373,c_22])).

tff(c_24373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24326,c_24062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:26:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.50/6.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.50/6.46  
% 14.50/6.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.50/6.47  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 14.50/6.47  
% 14.50/6.47  %Foreground sorts:
% 14.50/6.47  
% 14.50/6.47  
% 14.50/6.47  %Background operators:
% 14.50/6.47  
% 14.50/6.47  
% 14.50/6.47  %Foreground operators:
% 14.50/6.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.50/6.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.50/6.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.50/6.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.50/6.47  tff('#skF_2', type, '#skF_2': $i).
% 14.50/6.47  tff('#skF_1', type, '#skF_1': $i).
% 14.50/6.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.50/6.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.50/6.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.50/6.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.50/6.47  
% 14.50/6.50  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.50/6.50  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.50/6.50  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.50/6.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.50/6.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.50/6.50  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 14.50/6.50  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.50/6.50  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.50/6.50  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.50/6.50  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.50/6.50  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 14.50/6.50  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.50/6.50  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.50/6.50  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.50/6.50  tff(c_74, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(A_25, B_26))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.50/6.50  tff(c_81, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 14.50/6.50  tff(c_101, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.50/6.50  tff(c_122, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 14.50/6.50  tff(c_127, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_122])).
% 14.50/6.50  tff(c_273, plain, (![A_39, B_40]: (k4_xboole_0(k2_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k5_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.50/6.50  tff(c_306, plain, (![A_5]: (k4_xboole_0(A_5, k3_xboole_0(A_5, k1_xboole_0))=k5_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_273])).
% 14.50/6.50  tff(c_314, plain, (![A_41]: (k5_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_127, c_306])).
% 14.50/6.50  tff(c_330, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_314])).
% 14.50/6.50  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.50/6.50  tff(c_541, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.50/6.50  tff(c_588, plain, (![A_5, C_51]: (k4_xboole_0(A_5, k2_xboole_0(A_5, C_51))=k4_xboole_0(k1_xboole_0, C_51))), inference(superposition, [status(thm), theory('equality')], [c_81, c_541])).
% 14.50/6.50  tff(c_618, plain, (![C_52]: (k4_xboole_0(k1_xboole_0, C_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_588])).
% 14.50/6.50  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.50/6.50  tff(c_629, plain, (![C_52]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, C_52))), inference(superposition, [status(thm), theory('equality')], [c_618, c_16])).
% 14.50/6.50  tff(c_671, plain, (![C_53]: (k3_xboole_0(k1_xboole_0, C_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_629])).
% 14.50/6.50  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.50/6.50  tff(c_679, plain, (![C_53]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, C_53), k1_xboole_0)=k5_xboole_0(k1_xboole_0, C_53))), inference(superposition, [status(thm), theory('equality')], [c_671, c_4])).
% 14.50/6.50  tff(c_706, plain, (![C_53]: (k2_xboole_0(k1_xboole_0, C_53)=C_53)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_10, c_679])).
% 14.50/6.50  tff(c_313, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_127, c_306])).
% 14.50/6.50  tff(c_154, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.50/6.50  tff(c_169, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_81, c_154])).
% 14.50/6.50  tff(c_179, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_169])).
% 14.50/6.50  tff(c_14656, plain, (![A_233, B_234, C_235]: (k4_xboole_0(k4_xboole_0(A_233, B_234), k4_xboole_0(A_233, k2_xboole_0(B_234, C_235)))=k3_xboole_0(k4_xboole_0(A_233, B_234), C_235))), inference(superposition, [status(thm), theory('equality')], [c_541, c_16])).
% 14.50/6.50  tff(c_14984, plain, (![A_233, A_5]: (k4_xboole_0(k4_xboole_0(A_233, A_5), k4_xboole_0(A_233, A_5))=k3_xboole_0(k4_xboole_0(A_233, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_179, c_14656])).
% 14.50/6.50  tff(c_15094, plain, (![A_233, A_5]: (k3_xboole_0(k4_xboole_0(A_233, A_5), A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_14984])).
% 14.50/6.50  tff(c_119, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_101])).
% 14.50/6.50  tff(c_126, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_119])).
% 14.50/6.50  tff(c_18, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.50/6.50  tff(c_430, plain, (![A_46, B_47]: (k5_xboole_0(k5_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.50/6.50  tff(c_464, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k5_xboole_0(B_17, k3_xboole_0(A_16, B_17)))=k2_xboole_0(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_430])).
% 14.50/6.50  tff(c_116, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_81, c_101])).
% 14.50/6.50  tff(c_125, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_116])).
% 14.50/6.50  tff(c_294, plain, (![A_5]: (k4_xboole_0(A_5, k3_xboole_0(A_5, A_5))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_179, c_273])).
% 14.50/6.50  tff(c_496, plain, (![A_48]: (k5_xboole_0(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_125, c_294])).
% 14.50/6.50  tff(c_508, plain, (![A_48, C_18]: (k5_xboole_0(A_48, k5_xboole_0(A_48, C_18))=k5_xboole_0(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_496, c_18])).
% 14.50/6.50  tff(c_534, plain, (![A_48, C_18]: (k5_xboole_0(A_48, k5_xboole_0(A_48, C_18))=C_18)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_508])).
% 14.50/6.50  tff(c_15103, plain, (![A_236, A_237]: (k3_xboole_0(k4_xboole_0(A_236, A_237), A_237)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_14984])).
% 14.50/6.50  tff(c_16851, plain, (![A_249, B_250]: (k3_xboole_0(k5_xboole_0(A_249, B_250), k3_xboole_0(A_249, B_250))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_15103])).
% 14.50/6.50  tff(c_18073, plain, (![C_258, A_259]: (k3_xboole_0(C_258, k3_xboole_0(A_259, k5_xboole_0(A_259, C_258)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_534, c_16851])).
% 14.50/6.50  tff(c_18226, plain, (![B_17, A_16]: (k3_xboole_0(k5_xboole_0(B_17, k3_xboole_0(A_16, B_17)), k3_xboole_0(A_16, k2_xboole_0(A_16, B_17)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_464, c_18073])).
% 14.50/6.50  tff(c_21285, plain, (![B_280, A_281]: (k3_xboole_0(k5_xboole_0(B_280, k3_xboole_0(A_281, B_280)), A_281)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_18226])).
% 14.50/6.50  tff(c_21448, plain, (![A_5, A_233]: (k3_xboole_0(k5_xboole_0(A_5, k1_xboole_0), k4_xboole_0(A_233, A_5))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15094, c_21285])).
% 14.50/6.50  tff(c_21557, plain, (![A_5, A_233]: (k3_xboole_0(A_5, k4_xboole_0(A_233, A_5))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_21448])).
% 14.50/6.50  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.50/6.50  tff(c_592, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, k4_xboole_0(A_49, B_50)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_541])).
% 14.50/6.50  tff(c_616, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, A_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_592])).
% 14.50/6.50  tff(c_4702, plain, (![C_126, A_127, B_128]: (k2_xboole_0(C_126, k4_xboole_0(A_127, k2_xboole_0(B_128, C_126)))=k2_xboole_0(C_126, k4_xboole_0(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_541, c_8])).
% 14.50/6.50  tff(c_4825, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k2_xboole_0(A_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_616, c_4702])).
% 14.50/6.50  tff(c_4889, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(A_49, B_50))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4825])).
% 14.50/6.50  tff(c_4899, plain, (![A_129, B_130]: (k2_xboole_0(A_129, k4_xboole_0(A_129, B_130))=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4825])).
% 14.50/6.50  tff(c_772, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(B_56, A_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_592])).
% 14.50/6.50  tff(c_790, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k2_xboole_0(B_56, A_55))=k4_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_772, c_16])).
% 14.50/6.50  tff(c_825, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k2_xboole_0(B_56, A_55))=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_790])).
% 14.50/6.50  tff(c_1261, plain, (![A_67, B_68]: (k5_xboole_0(k3_xboole_0(A_67, B_68), k5_xboole_0(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_430])).
% 14.50/6.50  tff(c_1306, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k5_xboole_0(A_55, k2_xboole_0(B_56, A_55)))=k2_xboole_0(A_55, k2_xboole_0(B_56, A_55)))), inference(superposition, [status(thm), theory('equality')], [c_825, c_1261])).
% 14.50/6.50  tff(c_1343, plain, (![A_55, B_56]: (k2_xboole_0(A_55, k2_xboole_0(B_56, A_55))=k2_xboole_0(B_56, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_1306])).
% 14.50/6.50  tff(c_4942, plain, (![A_129, B_130]: (k2_xboole_0(k4_xboole_0(A_129, B_130), A_129)=k2_xboole_0(A_129, k4_xboole_0(A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_4899, c_1343])).
% 14.50/6.50  tff(c_5064, plain, (![A_129, B_130]: (k2_xboole_0(k4_xboole_0(A_129, B_130), A_129)=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_4942])).
% 14.50/6.50  tff(c_7464, plain, (![A_161, B_162]: (k3_xboole_0(k4_xboole_0(A_161, B_162), A_161)=k4_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_4899, c_825])).
% 14.50/6.50  tff(c_7509, plain, (![A_161, B_162]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_161, B_162), A_161), k4_xboole_0(A_161, B_162))=k5_xboole_0(k4_xboole_0(A_161, B_162), A_161))), inference(superposition, [status(thm), theory('equality')], [c_7464, c_4])).
% 14.50/6.50  tff(c_9573, plain, (![A_186, B_187]: (k5_xboole_0(A_186, k4_xboole_0(A_186, B_187))=k3_xboole_0(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5064, c_2, c_7509])).
% 14.50/6.50  tff(c_9622, plain, (![A_186, B_187]: (k5_xboole_0(A_186, k3_xboole_0(A_186, B_187))=k4_xboole_0(A_186, B_187))), inference(superposition, [status(thm), theory('equality')], [c_9573, c_534])).
% 14.50/6.50  tff(c_337, plain, (![A_42, B_43, C_44]: (k5_xboole_0(k5_xboole_0(A_42, B_43), C_44)=k5_xboole_0(A_42, k5_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.50/6.50  tff(c_353, plain, (![C_44, A_42, B_43]: (k5_xboole_0(C_44, k5_xboole_0(A_42, B_43))=k5_xboole_0(A_42, k5_xboole_0(B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_2])).
% 14.50/6.50  tff(c_3315, plain, (![C_112, A_113, B_114]: (k5_xboole_0(C_112, k5_xboole_0(A_113, B_114))=k5_xboole_0(A_113, k5_xboole_0(B_114, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_2])).
% 14.50/6.50  tff(c_3580, plain, (![A_1, C_112]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_1, C_112))=k5_xboole_0(C_112, A_1))), inference(superposition, [status(thm), theory('equality')], [c_330, c_3315])).
% 14.50/6.50  tff(c_22904, plain, (![A_290, B_291, C_292]: (k5_xboole_0(k5_xboole_0(A_290, k5_xboole_0(B_291, C_292)), k3_xboole_0(k5_xboole_0(A_290, B_291), C_292))=k2_xboole_0(k5_xboole_0(A_290, B_291), C_292))), inference(superposition, [status(thm), theory('equality')], [c_18, c_430])).
% 14.50/6.50  tff(c_23147, plain, (![C_112, A_1]: (k5_xboole_0(k5_xboole_0(C_112, A_1), k3_xboole_0(k5_xboole_0(k1_xboole_0, A_1), C_112))=k2_xboole_0(k5_xboole_0(k1_xboole_0, A_1), C_112))), inference(superposition, [status(thm), theory('equality')], [c_3580, c_22904])).
% 14.50/6.50  tff(c_24063, plain, (![C_297, A_298]: (k5_xboole_0(C_297, k4_xboole_0(A_298, C_297))=k2_xboole_0(A_298, C_297))), inference(demodulation, [status(thm), theory('equality')], [c_9622, c_353, c_330, c_2, c_330, c_23147])).
% 14.50/6.50  tff(c_279, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k5_xboole_0(A_39, B_40))=k2_xboole_0(k3_xboole_0(A_39, B_40), k2_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_273, c_8])).
% 14.50/6.50  tff(c_24118, plain, (![C_297, A_298]: (k2_xboole_0(k3_xboole_0(C_297, k4_xboole_0(A_298, C_297)), k2_xboole_0(C_297, k4_xboole_0(A_298, C_297)))=k2_xboole_0(k3_xboole_0(C_297, k4_xboole_0(A_298, C_297)), k2_xboole_0(A_298, C_297)))), inference(superposition, [status(thm), theory('equality')], [c_24063, c_279])).
% 14.50/6.50  tff(c_24326, plain, (![C_297, A_298]: (k2_xboole_0(C_297, A_298)=k2_xboole_0(A_298, C_297))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_21557, c_706, c_21557, c_8, c_24118])).
% 14.50/6.50  tff(c_23373, plain, (![C_112, A_1]: (k5_xboole_0(C_112, k4_xboole_0(A_1, C_112))=k2_xboole_0(A_1, C_112))), inference(demodulation, [status(thm), theory('equality')], [c_9622, c_353, c_330, c_2, c_330, c_23147])).
% 14.50/6.50  tff(c_22, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.50/6.50  tff(c_24062, plain, (k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23373, c_22])).
% 14.50/6.50  tff(c_24373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24326, c_24062])).
% 14.50/6.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.50/6.50  
% 14.50/6.50  Inference rules
% 14.50/6.50  ----------------------
% 14.50/6.50  #Ref     : 0
% 14.50/6.50  #Sup     : 6203
% 14.50/6.50  #Fact    : 0
% 14.50/6.50  #Define  : 0
% 14.50/6.50  #Split   : 0
% 14.50/6.50  #Chain   : 0
% 14.50/6.50  #Close   : 0
% 14.50/6.50  
% 14.50/6.50  Ordering : KBO
% 14.50/6.50  
% 14.50/6.50  Simplification rules
% 14.50/6.50  ----------------------
% 14.50/6.50  #Subsume      : 44
% 14.50/6.50  #Demod        : 7266
% 14.50/6.50  #Tautology    : 3902
% 14.50/6.50  #SimpNegUnit  : 0
% 14.50/6.50  #BackRed      : 6
% 14.50/6.50  
% 14.50/6.50  #Partial instantiations: 0
% 14.50/6.50  #Strategies tried      : 1
% 14.50/6.50  
% 14.50/6.50  Timing (in seconds)
% 14.50/6.50  ----------------------
% 14.87/6.51  Preprocessing        : 0.42
% 14.87/6.51  Parsing              : 0.23
% 14.87/6.51  CNF conversion       : 0.03
% 14.87/6.51  Main loop            : 5.15
% 14.87/6.51  Inferencing          : 1.04
% 14.87/6.51  Reduction            : 2.93
% 14.87/6.51  Demodulation         : 2.62
% 14.87/6.51  BG Simplification    : 0.16
% 14.87/6.51  Subsumption          : 0.76
% 14.87/6.51  Abstraction          : 0.24
% 14.87/6.51  MUC search           : 0.00
% 14.87/6.51  Cooper               : 0.00
% 14.87/6.51  Total                : 5.64
% 14.87/6.51  Index Insertion      : 0.00
% 14.87/6.51  Index Deletion       : 0.00
% 14.87/6.51  Index Matching       : 0.00
% 14.87/6.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

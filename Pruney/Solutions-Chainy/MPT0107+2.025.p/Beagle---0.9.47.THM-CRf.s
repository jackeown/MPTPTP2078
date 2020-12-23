%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.56s
% Verified   : 
% Statistics : Number of formulae       :   99 (3728 expanded)
%              Number of leaves         :   23 (1288 expanded)
%              Depth                    :   28
%              Number of atoms          :   86 (3715 expanded)
%              Number of equality atoms :   85 (3714 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_26,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,k4_xboole_0(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_28])).

tff(c_663,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_95])).

tff(c_36,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_320,plain,(
    ! [A_52,B_53] : k4_xboole_0(k2_xboole_0(A_52,B_53),k3_xboole_0(A_52,B_53)) = k5_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_664,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_95])).

tff(c_706,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k3_xboole_0(k2_xboole_0(A_1,B_2),k5_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_664])).

tff(c_1761,plain,(
    ! [A_128,B_129] : k3_xboole_0(k2_xboole_0(A_128,B_129),k5_xboole_0(A_128,B_129)) = k5_xboole_0(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_706])).

tff(c_1830,plain,(
    ! [A_22] : k3_xboole_0(k2_xboole_0(A_22,k1_xboole_0),A_22) = k5_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1761])).

tff(c_1839,plain,(
    ! [A_130] : k3_xboole_0(k2_xboole_0(A_130,k1_xboole_0),A_130) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1830])).

tff(c_1903,plain,(
    ! [A_130] : k3_xboole_0(A_130,k2_xboole_0(A_130,k1_xboole_0)) = A_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_2])).

tff(c_1930,plain,(
    ! [A_131] : k3_xboole_0(A_131,k2_xboole_0(A_131,k1_xboole_0)) = A_131 ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_2])).

tff(c_117,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k3_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_28])).

tff(c_143,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_126])).

tff(c_1962,plain,(
    ! [A_131] : k3_xboole_0(A_131,k2_xboole_0(A_131,k1_xboole_0)) = k3_xboole_0(A_131,A_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_143])).

tff(c_1989,plain,(
    ! [A_131] : k3_xboole_0(A_131,A_131) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1903,c_1962])).

tff(c_166,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2772,plain,(
    ! [C_148,A_149,B_150] : k5_xboole_0(C_148,k3_xboole_0(A_149,k4_xboole_0(B_150,C_148))) = k2_xboole_0(C_148,k3_xboole_0(A_149,B_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_36])).

tff(c_2800,plain,(
    ! [C_148,B_150] : k2_xboole_0(C_148,k3_xboole_0(k4_xboole_0(B_150,C_148),B_150)) = k5_xboole_0(C_148,k4_xboole_0(B_150,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_2772])).

tff(c_2847,plain,(
    ! [C_148,B_150] : k2_xboole_0(C_148,k4_xboole_0(B_150,C_148)) = k2_xboole_0(C_148,B_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_36,c_2,c_2800])).

tff(c_145,plain,(
    ! [A_40,B_41] : k2_xboole_0(k3_xboole_0(A_40,B_41),k4_xboole_0(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_145])).

tff(c_32,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2853,plain,(
    ! [C_151,B_152] : k2_xboole_0(C_151,k4_xboole_0(B_152,C_151)) = k2_xboole_0(C_151,B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_36,c_2,c_2800])).

tff(c_2899,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = k2_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2853])).

tff(c_2912,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2899])).

tff(c_2990,plain,(
    ! [A_155,B_156] : k2_xboole_0(k3_xboole_0(A_155,B_156),A_155) = A_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2899])).

tff(c_3725,plain,(
    ! [B_173] : k3_xboole_0(k3_xboole_0(k1_xboole_0,B_173),k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_1903])).

tff(c_24,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k5_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3773,plain,(
    ! [B_173] : k4_xboole_0(k2_xboole_0(k3_xboole_0(k1_xboole_0,B_173),k1_xboole_0),k3_xboole_0(k1_xboole_0,B_173)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,B_173),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3725,c_24])).

tff(c_3871,plain,(
    ! [B_174] : k4_xboole_0(k1_xboole_0,B_174) = k3_xboole_0(k1_xboole_0,B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2912,c_34,c_3773])).

tff(c_22,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_10,A_9)) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3954,plain,(
    ! [B_174] : k2_xboole_0(k3_xboole_0(k1_xboole_0,B_174),k4_xboole_0(B_174,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_3871,c_22])).

tff(c_4030,plain,(
    ! [B_175] : k5_xboole_0(k1_xboole_0,B_175) = B_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_3954])).

tff(c_4061,plain,(
    ! [B_24] : k4_xboole_0(B_24,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4030,c_36])).

tff(c_141,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_2893,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k2_xboole_0(k3_xboole_0(A_1,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2853])).

tff(c_2914,plain,(
    ! [A_153,B_154] : k2_xboole_0(k3_xboole_0(A_153,B_154),B_154) = B_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_2893])).

tff(c_2942,plain,(
    ! [B_154,A_153] : k4_xboole_0(B_154,k3_xboole_0(k3_xboole_0(A_153,B_154),B_154)) = k5_xboole_0(k3_xboole_0(A_153,B_154),B_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_24])).

tff(c_5551,plain,(
    ! [A_193,B_194] : k5_xboole_0(k3_xboole_0(A_193,B_194),B_194) = k4_xboole_0(B_194,A_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_26,c_2,c_2942])).

tff(c_5574,plain,(
    ! [A_193] : k4_xboole_0(k1_xboole_0,A_193) = k3_xboole_0(A_193,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5551,c_34])).

tff(c_3019,plain,(
    ! [A_155,B_156] : k4_xboole_0(A_155,k3_xboole_0(A_155,k3_xboole_0(A_155,B_156))) = k5_xboole_0(k3_xboole_0(A_155,B_156),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_353])).

tff(c_3067,plain,(
    ! [A_155,B_156] : k5_xboole_0(k3_xboole_0(A_155,B_156),A_155) = k4_xboole_0(A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_3019])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_489,plain,(
    ! [A_61,B_62] : k2_xboole_0(k4_xboole_0(A_61,B_62),k4_xboole_0(B_62,A_61)) = k5_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_522,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_13,B_14),A_13),k4_xboole_0(A_13,B_14)) = k5_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_489])).

tff(c_536,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,k4_xboole_0(B_14,A_13)),k4_xboole_0(A_13,B_14)) = k5_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_522])).

tff(c_6741,plain,(
    ! [A_207,B_208] : k2_xboole_0(k3_xboole_0(A_207,k4_xboole_0(B_208,A_207)),k4_xboole_0(A_207,B_208)) = k4_xboole_0(A_207,B_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_536])).

tff(c_6763,plain,(
    ! [A_193] : k2_xboole_0(k3_xboole_0(A_193,k3_xboole_0(A_193,k1_xboole_0)),k4_xboole_0(A_193,k1_xboole_0)) = k4_xboole_0(A_193,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5574,c_6741])).

tff(c_6854,plain,(
    ! [A_193] : k2_xboole_0(k1_xboole_0,A_193) = A_193 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4061,c_32,c_143,c_6763])).

tff(c_6972,plain,(
    ! [B_210] : k4_xboole_0(B_210,k1_xboole_0) = B_210 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6854,c_4061])).

tff(c_7087,plain,(
    ! [B_210] : k2_xboole_0(B_210,k4_xboole_0(k1_xboole_0,B_210)) = k5_xboole_0(B_210,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6972,c_22])).

tff(c_7153,plain,(
    ! [B_210] : k2_xboole_0(B_210,k1_xboole_0) = B_210 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_34,c_7087])).

tff(c_3855,plain,(
    ! [B_173] : k4_xboole_0(k1_xboole_0,B_173) = k3_xboole_0(k1_xboole_0,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2912,c_34,c_3773])).

tff(c_697,plain,(
    ! [A_71,B_72] : k2_xboole_0(k4_xboole_0(A_71,B_72),k4_xboole_0(A_71,k4_xboole_0(A_71,B_72))) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_32])).

tff(c_725,plain,(
    ! [A_71,B_72] : k2_xboole_0(k4_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_697])).

tff(c_528,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(k4_xboole_0(A_15,B_16),A_15),k3_xboole_0(A_15,B_16)) = k5_xboole_0(k4_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_489])).

tff(c_7006,plain,(
    ! [B_16] : k2_xboole_0(k4_xboole_0(k1_xboole_0,B_16),k3_xboole_0(k1_xboole_0,B_16)) = k5_xboole_0(k4_xboole_0(k1_xboole_0,B_16),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6972,c_528])).

tff(c_7141,plain,(
    ! [B_16] : k3_xboole_0(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_725,c_34,c_7006])).

tff(c_1837,plain,(
    ! [A_22] : k3_xboole_0(k2_xboole_0(A_22,k1_xboole_0),A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1830])).

tff(c_2929,plain,(
    ! [A_153] : k3_xboole_0(k1_xboole_0,k3_xboole_0(A_153,k1_xboole_0)) = k3_xboole_0(A_153,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_1837])).

tff(c_7296,plain,(
    ! [A_153] : k3_xboole_0(A_153,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7141,c_2929])).

tff(c_7106,plain,(
    ! [B_210] : k4_xboole_0(B_210,B_210) = k3_xboole_0(B_210,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6972,c_28])).

tff(c_8346,plain,(
    ! [B_210] : k4_xboole_0(B_210,B_210) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7296,c_7106])).

tff(c_11472,plain,(
    ! [C_272,A_273,B_274] : k2_xboole_0(k4_xboole_0(C_272,k3_xboole_0(A_273,B_274)),k3_xboole_0(A_273,k4_xboole_0(B_274,C_272))) = k5_xboole_0(C_272,k3_xboole_0(A_273,B_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_489])).

tff(c_11613,plain,(
    ! [B_2,A_1] : k2_xboole_0(k4_xboole_0(B_2,A_1),k3_xboole_0(A_1,k4_xboole_0(B_2,B_2))) = k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_11472])).

tff(c_11679,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7296,c_8346,c_11613])).

tff(c_38,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_11914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11679,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:23:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.40/3.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.56/3.10  
% 8.56/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.56/3.11  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.56/3.11  
% 8.56/3.11  %Foreground sorts:
% 8.56/3.11  
% 8.56/3.11  
% 8.56/3.11  %Background operators:
% 8.56/3.11  
% 8.56/3.11  
% 8.56/3.11  %Foreground operators:
% 8.56/3.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.56/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.56/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.56/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.56/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.56/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.56/3.11  tff('#skF_3', type, '#skF_3': $i).
% 8.56/3.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.56/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.56/3.11  tff('#skF_4', type, '#skF_4': $i).
% 8.56/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.56/3.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.56/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.56/3.11  
% 8.56/3.13  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.56/3.13  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.56/3.13  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.56/3.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.56/3.13  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.56/3.13  tff(f_41, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.56/3.13  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.56/3.13  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.56/3.13  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 8.56/3.13  tff(f_56, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.56/3.13  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.56/3.13  tff(c_92, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.56/3.13  tff(c_28, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.56/3.13  tff(c_95, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k3_xboole_0(A_33, k4_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_28])).
% 8.56/3.13  tff(c_663, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_95])).
% 8.56/3.13  tff(c_36, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.56/3.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.56/3.13  tff(c_34, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.56/3.13  tff(c_320, plain, (![A_52, B_53]: (k4_xboole_0(k2_xboole_0(A_52, B_53), k3_xboole_0(A_52, B_53))=k5_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.56/3.13  tff(c_353, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 8.56/3.13  tff(c_664, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_95])).
% 8.56/3.13  tff(c_706, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k3_xboole_0(k2_xboole_0(A_1, B_2), k5_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_353, c_664])).
% 8.56/3.13  tff(c_1761, plain, (![A_128, B_129]: (k3_xboole_0(k2_xboole_0(A_128, B_129), k5_xboole_0(A_128, B_129))=k5_xboole_0(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_706])).
% 8.56/3.13  tff(c_1830, plain, (![A_22]: (k3_xboole_0(k2_xboole_0(A_22, k1_xboole_0), A_22)=k5_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1761])).
% 8.56/3.13  tff(c_1839, plain, (![A_130]: (k3_xboole_0(k2_xboole_0(A_130, k1_xboole_0), A_130)=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1830])).
% 8.56/3.13  tff(c_1903, plain, (![A_130]: (k3_xboole_0(A_130, k2_xboole_0(A_130, k1_xboole_0))=A_130)), inference(superposition, [status(thm), theory('equality')], [c_1839, c_2])).
% 8.56/3.13  tff(c_1930, plain, (![A_131]: (k3_xboole_0(A_131, k2_xboole_0(A_131, k1_xboole_0))=A_131)), inference(superposition, [status(thm), theory('equality')], [c_1839, c_2])).
% 8.56/3.13  tff(c_117, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.56/3.13  tff(c_126, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k3_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_28])).
% 8.56/3.13  tff(c_143, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_126])).
% 8.56/3.13  tff(c_1962, plain, (![A_131]: (k3_xboole_0(A_131, k2_xboole_0(A_131, k1_xboole_0))=k3_xboole_0(A_131, A_131))), inference(superposition, [status(thm), theory('equality')], [c_1930, c_143])).
% 8.56/3.13  tff(c_1989, plain, (![A_131]: (k3_xboole_0(A_131, A_131)=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_1903, c_1962])).
% 8.56/3.13  tff(c_166, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.56/3.13  tff(c_2772, plain, (![C_148, A_149, B_150]: (k5_xboole_0(C_148, k3_xboole_0(A_149, k4_xboole_0(B_150, C_148)))=k2_xboole_0(C_148, k3_xboole_0(A_149, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_36])).
% 8.56/3.13  tff(c_2800, plain, (![C_148, B_150]: (k2_xboole_0(C_148, k3_xboole_0(k4_xboole_0(B_150, C_148), B_150))=k5_xboole_0(C_148, k4_xboole_0(B_150, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_1989, c_2772])).
% 8.56/3.13  tff(c_2847, plain, (![C_148, B_150]: (k2_xboole_0(C_148, k4_xboole_0(B_150, C_148))=k2_xboole_0(C_148, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_36, c_2, c_2800])).
% 8.56/3.13  tff(c_145, plain, (![A_40, B_41]: (k2_xboole_0(k3_xboole_0(A_40, B_41), k4_xboole_0(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.56/3.13  tff(c_163, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_145])).
% 8.56/3.13  tff(c_32, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.56/3.13  tff(c_2853, plain, (![C_151, B_152]: (k2_xboole_0(C_151, k4_xboole_0(B_152, C_151))=k2_xboole_0(C_151, B_152))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_36, c_2, c_2800])).
% 8.56/3.13  tff(c_2899, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=k2_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2853])).
% 8.56/3.13  tff(c_2912, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2899])).
% 8.56/3.13  tff(c_2990, plain, (![A_155, B_156]: (k2_xboole_0(k3_xboole_0(A_155, B_156), A_155)=A_155)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2899])).
% 8.56/3.13  tff(c_3725, plain, (![B_173]: (k3_xboole_0(k3_xboole_0(k1_xboole_0, B_173), k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_173))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_1903])).
% 8.56/3.13  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k5_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.56/3.13  tff(c_3773, plain, (![B_173]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(k1_xboole_0, B_173), k1_xboole_0), k3_xboole_0(k1_xboole_0, B_173))=k5_xboole_0(k3_xboole_0(k1_xboole_0, B_173), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3725, c_24])).
% 8.56/3.13  tff(c_3871, plain, (![B_174]: (k4_xboole_0(k1_xboole_0, B_174)=k3_xboole_0(k1_xboole_0, B_174))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2912, c_34, c_3773])).
% 8.56/3.13  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_10, A_9))=k5_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.56/3.13  tff(c_3954, plain, (![B_174]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, B_174), k4_xboole_0(B_174, k1_xboole_0))=k5_xboole_0(k1_xboole_0, B_174))), inference(superposition, [status(thm), theory('equality')], [c_3871, c_22])).
% 8.56/3.13  tff(c_4030, plain, (![B_175]: (k5_xboole_0(k1_xboole_0, B_175)=B_175)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_3954])).
% 8.56/3.13  tff(c_4061, plain, (![B_24]: (k4_xboole_0(B_24, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_24))), inference(superposition, [status(thm), theory('equality')], [c_4030, c_36])).
% 8.56/3.13  tff(c_141, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 8.56/3.13  tff(c_2893, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k2_xboole_0(k3_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_141, c_2853])).
% 8.56/3.13  tff(c_2914, plain, (![A_153, B_154]: (k2_xboole_0(k3_xboole_0(A_153, B_154), B_154)=B_154)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_2893])).
% 8.56/3.13  tff(c_2942, plain, (![B_154, A_153]: (k4_xboole_0(B_154, k3_xboole_0(k3_xboole_0(A_153, B_154), B_154))=k5_xboole_0(k3_xboole_0(A_153, B_154), B_154))), inference(superposition, [status(thm), theory('equality')], [c_2914, c_24])).
% 8.56/3.13  tff(c_5551, plain, (![A_193, B_194]: (k5_xboole_0(k3_xboole_0(A_193, B_194), B_194)=k4_xboole_0(B_194, A_193))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_26, c_2, c_2942])).
% 8.56/3.13  tff(c_5574, plain, (![A_193]: (k4_xboole_0(k1_xboole_0, A_193)=k3_xboole_0(A_193, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5551, c_34])).
% 8.56/3.13  tff(c_3019, plain, (![A_155, B_156]: (k4_xboole_0(A_155, k3_xboole_0(A_155, k3_xboole_0(A_155, B_156)))=k5_xboole_0(k3_xboole_0(A_155, B_156), A_155))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_353])).
% 8.56/3.13  tff(c_3067, plain, (![A_155, B_156]: (k5_xboole_0(k3_xboole_0(A_155, B_156), A_155)=k4_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_3019])).
% 8.56/3.13  tff(c_30, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.56/3.13  tff(c_489, plain, (![A_61, B_62]: (k2_xboole_0(k4_xboole_0(A_61, B_62), k4_xboole_0(B_62, A_61))=k5_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.56/3.13  tff(c_522, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_13, B_14), A_13), k4_xboole_0(A_13, B_14))=k5_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_489])).
% 8.56/3.13  tff(c_536, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, k4_xboole_0(B_14, A_13)), k4_xboole_0(A_13, B_14))=k5_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_522])).
% 8.56/3.13  tff(c_6741, plain, (![A_207, B_208]: (k2_xboole_0(k3_xboole_0(A_207, k4_xboole_0(B_208, A_207)), k4_xboole_0(A_207, B_208))=k4_xboole_0(A_207, B_208))), inference(demodulation, [status(thm), theory('equality')], [c_3067, c_536])).
% 8.56/3.13  tff(c_6763, plain, (![A_193]: (k2_xboole_0(k3_xboole_0(A_193, k3_xboole_0(A_193, k1_xboole_0)), k4_xboole_0(A_193, k1_xboole_0))=k4_xboole_0(A_193, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5574, c_6741])).
% 8.56/3.13  tff(c_6854, plain, (![A_193]: (k2_xboole_0(k1_xboole_0, A_193)=A_193)), inference(demodulation, [status(thm), theory('equality')], [c_4061, c_32, c_143, c_6763])).
% 8.56/3.13  tff(c_6972, plain, (![B_210]: (k4_xboole_0(B_210, k1_xboole_0)=B_210)), inference(demodulation, [status(thm), theory('equality')], [c_6854, c_4061])).
% 8.56/3.13  tff(c_7087, plain, (![B_210]: (k2_xboole_0(B_210, k4_xboole_0(k1_xboole_0, B_210))=k5_xboole_0(B_210, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6972, c_22])).
% 8.56/3.13  tff(c_7153, plain, (![B_210]: (k2_xboole_0(B_210, k1_xboole_0)=B_210)), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_34, c_7087])).
% 8.56/3.13  tff(c_3855, plain, (![B_173]: (k4_xboole_0(k1_xboole_0, B_173)=k3_xboole_0(k1_xboole_0, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2912, c_34, c_3773])).
% 8.56/3.13  tff(c_697, plain, (![A_71, B_72]: (k2_xboole_0(k4_xboole_0(A_71, B_72), k4_xboole_0(A_71, k4_xboole_0(A_71, B_72)))=A_71)), inference(superposition, [status(thm), theory('equality')], [c_664, c_32])).
% 8.56/3.13  tff(c_725, plain, (![A_71, B_72]: (k2_xboole_0(k4_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72))=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_697])).
% 8.56/3.13  tff(c_528, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_15, B_16), A_15), k3_xboole_0(A_15, B_16))=k5_xboole_0(k4_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_28, c_489])).
% 8.56/3.13  tff(c_7006, plain, (![B_16]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, B_16), k3_xboole_0(k1_xboole_0, B_16))=k5_xboole_0(k4_xboole_0(k1_xboole_0, B_16), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6972, c_528])).
% 8.56/3.13  tff(c_7141, plain, (![B_16]: (k3_xboole_0(k1_xboole_0, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_725, c_34, c_7006])).
% 8.56/3.13  tff(c_1837, plain, (![A_22]: (k3_xboole_0(k2_xboole_0(A_22, k1_xboole_0), A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1830])).
% 8.56/3.13  tff(c_2929, plain, (![A_153]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(A_153, k1_xboole_0))=k3_xboole_0(A_153, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2914, c_1837])).
% 8.56/3.13  tff(c_7296, plain, (![A_153]: (k3_xboole_0(A_153, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7141, c_2929])).
% 8.56/3.13  tff(c_7106, plain, (![B_210]: (k4_xboole_0(B_210, B_210)=k3_xboole_0(B_210, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6972, c_28])).
% 8.56/3.13  tff(c_8346, plain, (![B_210]: (k4_xboole_0(B_210, B_210)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7296, c_7106])).
% 8.56/3.13  tff(c_11472, plain, (![C_272, A_273, B_274]: (k2_xboole_0(k4_xboole_0(C_272, k3_xboole_0(A_273, B_274)), k3_xboole_0(A_273, k4_xboole_0(B_274, C_272)))=k5_xboole_0(C_272, k3_xboole_0(A_273, B_274)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_489])).
% 8.56/3.13  tff(c_11613, plain, (![B_2, A_1]: (k2_xboole_0(k4_xboole_0(B_2, A_1), k3_xboole_0(A_1, k4_xboole_0(B_2, B_2)))=k5_xboole_0(B_2, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_11472])).
% 8.56/3.13  tff(c_11679, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7296, c_8346, c_11613])).
% 8.56/3.13  tff(c_38, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.56/3.13  tff(c_39, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 8.56/3.13  tff(c_11914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11679, c_39])).
% 8.56/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.56/3.13  
% 8.56/3.13  Inference rules
% 8.56/3.13  ----------------------
% 8.56/3.13  #Ref     : 0
% 8.56/3.13  #Sup     : 2958
% 8.56/3.13  #Fact    : 0
% 8.56/3.13  #Define  : 0
% 8.56/3.13  #Split   : 0
% 8.56/3.13  #Chain   : 0
% 8.56/3.13  #Close   : 0
% 8.56/3.13  
% 8.56/3.13  Ordering : KBO
% 8.56/3.13  
% 8.56/3.13  Simplification rules
% 8.56/3.13  ----------------------
% 8.56/3.13  #Subsume      : 167
% 8.56/3.13  #Demod        : 3516
% 8.56/3.13  #Tautology    : 1429
% 8.56/3.13  #SimpNegUnit  : 0
% 8.56/3.13  #BackRed      : 25
% 8.56/3.13  
% 8.56/3.13  #Partial instantiations: 0
% 8.56/3.13  #Strategies tried      : 1
% 8.56/3.13  
% 8.56/3.13  Timing (in seconds)
% 8.56/3.13  ----------------------
% 8.56/3.13  Preprocessing        : 0.33
% 8.56/3.13  Parsing              : 0.17
% 8.56/3.13  CNF conversion       : 0.02
% 8.56/3.13  Main loop            : 2.00
% 8.56/3.13  Inferencing          : 0.52
% 8.56/3.13  Reduction            : 1.02
% 8.56/3.13  Demodulation         : 0.90
% 8.56/3.13  BG Simplification    : 0.07
% 8.56/3.13  Subsumption          : 0.28
% 8.56/3.13  Abstraction          : 0.12
% 8.56/3.13  MUC search           : 0.00
% 8.56/3.13  Cooper               : 0.00
% 8.56/3.13  Total                : 2.37
% 8.56/3.13  Index Insertion      : 0.00
% 8.56/3.13  Index Deletion       : 0.00
% 8.56/3.13  Index Matching       : 0.00
% 8.56/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

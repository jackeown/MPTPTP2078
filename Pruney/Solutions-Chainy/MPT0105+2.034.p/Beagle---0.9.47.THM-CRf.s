%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 6.92s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 217 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :   71 ( 207 expanded)
%              Number of equality atoms :   70 ( 206 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_84,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_81])).

tff(c_332,plain,(
    ! [A_44,B_45] : k5_xboole_0(k5_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_353,plain,(
    ! [A_4] : k5_xboole_0(k5_xboole_0(A_4,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_332])).

tff(c_359,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_353])).

tff(c_364,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_353])).

tff(c_145,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_36,k4_xboole_0(A_35,B_36))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_84])).

tff(c_199,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_36,A_35)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_155])).

tff(c_377,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_199])).

tff(c_620,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k4_xboole_0(A_56,B_57),k3_xboole_0(A_56,C_58)) = k4_xboole_0(A_56,k4_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_665,plain,(
    ! [A_7,C_58] : k4_xboole_0(A_7,k4_xboole_0(k1_xboole_0,C_58)) = k2_xboole_0(A_7,k3_xboole_0(A_7,C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_620])).

tff(c_675,plain,(
    ! [A_7,C_58] : k2_xboole_0(A_7,k3_xboole_0(A_7,C_58)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_377,c_665])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_844,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k4_xboole_0(A_65,B_66),k4_xboole_0(A_65,C_67)) = k4_xboole_0(A_65,k3_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_923,plain,(
    ! [A_7,B_66] : k4_xboole_0(A_7,k3_xboole_0(B_66,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_7,B_66),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_844])).

tff(c_939,plain,(
    ! [A_68,B_69] : k2_xboole_0(k4_xboole_0(A_68,B_69),A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4,c_923])).

tff(c_983,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_939])).

tff(c_980,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_939])).

tff(c_550,plain,(
    ! [A_53,B_54,C_55] : k3_xboole_0(k4_xboole_0(A_53,B_54),k4_xboole_0(A_53,C_55)) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_600,plain,(
    ! [A_7,C_55] : k4_xboole_0(A_7,k2_xboole_0(k1_xboole_0,C_55)) = k3_xboole_0(A_7,k4_xboole_0(A_7,C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_550])).

tff(c_3710,plain,(
    ! [A_7,C_55] : k3_xboole_0(A_7,k4_xboole_0(A_7,C_55)) = k4_xboole_0(A_7,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_600])).

tff(c_75,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_3863,plain,(
    ! [A_127,B_128] : k4_xboole_0(A_127,k3_xboole_0(A_127,B_128)) = k4_xboole_0(A_127,B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3710,c_75])).

tff(c_3926,plain,(
    ! [A_127,B_128] : k2_xboole_0(k3_xboole_0(A_127,B_128),k4_xboole_0(A_127,B_128)) = k2_xboole_0(k3_xboole_0(A_127,B_128),A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_3863,c_6])).

tff(c_4346,plain,(
    ! [A_134,B_135] : k2_xboole_0(k3_xboole_0(A_134,B_135),k4_xboole_0(A_134,B_135)) = A_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_3926])).

tff(c_575,plain,(
    ! [A_35,B_54,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_54,k2_xboole_0(B_36,A_35))) = k3_xboole_0(k4_xboole_0(A_35,B_54),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_550])).

tff(c_610,plain,(
    ! [A_35,B_54,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_54,k2_xboole_0(B_36,A_35))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_575])).

tff(c_4527,plain,(
    ! [A_136,B_137,B_138] : k4_xboole_0(k4_xboole_0(A_136,B_137),k2_xboole_0(B_138,A_136)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4346,c_610])).

tff(c_5092,plain,(
    ! [A_144,C_145,B_146] : k4_xboole_0(k4_xboole_0(k3_xboole_0(A_144,C_145),B_146),A_144) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_4527])).

tff(c_5148,plain,(
    ! [A_144,C_145,B_146] : k2_xboole_0(A_144,k4_xboole_0(k3_xboole_0(A_144,C_145),B_146)) = k2_xboole_0(A_144,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_6])).

tff(c_5271,plain,(
    ! [A_144,C_145,B_146] : k2_xboole_0(A_144,k4_xboole_0(k3_xboole_0(A_144,C_145),B_146)) = A_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_5148])).

tff(c_938,plain,(
    ! [A_7,B_66] : k2_xboole_0(k4_xboole_0(A_7,B_66),A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4,c_923])).

tff(c_205,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_155])).

tff(c_217,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = k4_xboole_0(A_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_12])).

tff(c_237,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_217])).

tff(c_374,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_237])).

tff(c_588,plain,(
    ! [A_7,C_55] : k4_xboole_0(A_7,k2_xboole_0(A_7,C_55)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_7,C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_550])).

tff(c_710,plain,(
    ! [A_61,C_62] : k4_xboole_0(A_61,k2_xboole_0(A_61,C_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_588])).

tff(c_737,plain,(
    ! [A_61,C_62] : k3_xboole_0(A_61,k2_xboole_0(A_61,C_62)) = k4_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_12])).

tff(c_1178,plain,(
    ! [A_75,C_76] : k3_xboole_0(A_75,k2_xboole_0(A_75,C_76)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k4_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1193,plain,(
    ! [A_75,B_14,C_76] : k4_xboole_0(A_75,k4_xboole_0(B_14,k2_xboole_0(A_75,C_76))) = k2_xboole_0(k4_xboole_0(A_75,B_14),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_14])).

tff(c_5928,plain,(
    ! [A_156,B_157,C_158] : k4_xboole_0(A_156,k4_xboole_0(B_157,k2_xboole_0(A_156,C_158))) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1193])).

tff(c_6158,plain,(
    ! [A_159,B_160] : k4_xboole_0(A_159,k4_xboole_0(B_160,A_159)) = A_159 ),
    inference(superposition,[status(thm),theory(equality)],[c_5271,c_5928])).

tff(c_6228,plain,(
    ! [A_159,B_160] : k3_xboole_0(A_159,k4_xboole_0(B_160,A_159)) = k4_xboole_0(A_159,A_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_6158,c_12])).

tff(c_6852,plain,(
    ! [A_166,B_167] : k3_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6228])).

tff(c_413,plain,(
    ! [A_48,B_49,C_50] : k5_xboole_0(k5_xboole_0(A_48,B_49),C_50) = k5_xboole_0(A_48,k5_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_426,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k5_xboole_0(B_49,k3_xboole_0(A_48,B_49))) = k2_xboole_0(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_22])).

tff(c_6894,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k5_xboole_0(k4_xboole_0(B_167,A_166),k1_xboole_0)) = k2_xboole_0(A_166,k4_xboole_0(B_167,A_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6852,c_426])).

tff(c_7030,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = k2_xboole_0(A_166,B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18,c_6894])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7030,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.92/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.69  
% 6.92/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.69  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 6.92/2.69  
% 6.92/2.69  %Foreground sorts:
% 6.92/2.69  
% 6.92/2.69  
% 6.92/2.69  %Background operators:
% 6.92/2.69  
% 6.92/2.69  
% 6.92/2.69  %Foreground operators:
% 6.92/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.92/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.92/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.92/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.92/2.69  tff('#skF_2', type, '#skF_2': $i).
% 6.92/2.69  tff('#skF_1', type, '#skF_1': $i).
% 6.92/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.92/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.92/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.92/2.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.92/2.69  
% 6.92/2.71  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.92/2.71  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.92/2.71  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.92/2.71  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.92/2.71  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.92/2.71  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.92/2.71  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.92/2.71  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.92/2.71  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 6.92/2.71  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 6.92/2.71  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.92/2.71  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.92/2.71  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.92/2.71  tff(c_18, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.71  tff(c_4, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.92/2.71  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.92/2.71  tff(c_63, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.92/2.71  tff(c_81, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 6.92/2.71  tff(c_84, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_81])).
% 6.92/2.71  tff(c_332, plain, (![A_44, B_45]: (k5_xboole_0(k5_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.92/2.71  tff(c_353, plain, (![A_4]: (k5_xboole_0(k5_xboole_0(A_4, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_332])).
% 6.92/2.71  tff(c_359, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_353])).
% 6.92/2.71  tff(c_364, plain, (![A_46]: (k2_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_353])).
% 6.92/2.71  tff(c_145, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.92/2.71  tff(c_155, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_36, k4_xboole_0(A_35, B_36)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_84])).
% 6.92/2.71  tff(c_199, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_36, A_35))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_155])).
% 6.92/2.71  tff(c_377, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_364, c_199])).
% 6.92/2.71  tff(c_620, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k4_xboole_0(A_56, B_57), k3_xboole_0(A_56, C_58))=k4_xboole_0(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.92/2.71  tff(c_665, plain, (![A_7, C_58]: (k4_xboole_0(A_7, k4_xboole_0(k1_xboole_0, C_58))=k2_xboole_0(A_7, k3_xboole_0(A_7, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_620])).
% 6.92/2.71  tff(c_675, plain, (![A_7, C_58]: (k2_xboole_0(A_7, k3_xboole_0(A_7, C_58))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_377, c_665])).
% 6.92/2.71  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.92/2.71  tff(c_844, plain, (![A_65, B_66, C_67]: (k2_xboole_0(k4_xboole_0(A_65, B_66), k4_xboole_0(A_65, C_67))=k4_xboole_0(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.92/2.71  tff(c_923, plain, (![A_7, B_66]: (k4_xboole_0(A_7, k3_xboole_0(B_66, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_7, B_66), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_844])).
% 6.92/2.71  tff(c_939, plain, (![A_68, B_69]: (k2_xboole_0(k4_xboole_0(A_68, B_69), A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4, c_923])).
% 6.92/2.71  tff(c_983, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_12, c_939])).
% 6.92/2.71  tff(c_980, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(superposition, [status(thm), theory('equality')], [c_84, c_939])).
% 6.92/2.71  tff(c_550, plain, (![A_53, B_54, C_55]: (k3_xboole_0(k4_xboole_0(A_53, B_54), k4_xboole_0(A_53, C_55))=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.92/2.71  tff(c_600, plain, (![A_7, C_55]: (k4_xboole_0(A_7, k2_xboole_0(k1_xboole_0, C_55))=k3_xboole_0(A_7, k4_xboole_0(A_7, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_550])).
% 6.92/2.71  tff(c_3710, plain, (![A_7, C_55]: (k3_xboole_0(A_7, k4_xboole_0(A_7, C_55))=k4_xboole_0(A_7, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_980, c_600])).
% 6.92/2.71  tff(c_75, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_63])).
% 6.92/2.71  tff(c_3863, plain, (![A_127, B_128]: (k4_xboole_0(A_127, k3_xboole_0(A_127, B_128))=k4_xboole_0(A_127, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_3710, c_75])).
% 6.92/2.71  tff(c_3926, plain, (![A_127, B_128]: (k2_xboole_0(k3_xboole_0(A_127, B_128), k4_xboole_0(A_127, B_128))=k2_xboole_0(k3_xboole_0(A_127, B_128), A_127))), inference(superposition, [status(thm), theory('equality')], [c_3863, c_6])).
% 6.92/2.71  tff(c_4346, plain, (![A_134, B_135]: (k2_xboole_0(k3_xboole_0(A_134, B_135), k4_xboole_0(A_134, B_135))=A_134)), inference(demodulation, [status(thm), theory('equality')], [c_983, c_3926])).
% 6.92/2.71  tff(c_575, plain, (![A_35, B_54, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_54, k2_xboole_0(B_36, A_35)))=k3_xboole_0(k4_xboole_0(A_35, B_54), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_199, c_550])).
% 6.92/2.71  tff(c_610, plain, (![A_35, B_54, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_54, k2_xboole_0(B_36, A_35)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_575])).
% 6.92/2.71  tff(c_4527, plain, (![A_136, B_137, B_138]: (k4_xboole_0(k4_xboole_0(A_136, B_137), k2_xboole_0(B_138, A_136))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4346, c_610])).
% 6.92/2.71  tff(c_5092, plain, (![A_144, C_145, B_146]: (k4_xboole_0(k4_xboole_0(k3_xboole_0(A_144, C_145), B_146), A_144)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_675, c_4527])).
% 6.92/2.71  tff(c_5148, plain, (![A_144, C_145, B_146]: (k2_xboole_0(A_144, k4_xboole_0(k3_xboole_0(A_144, C_145), B_146))=k2_xboole_0(A_144, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5092, c_6])).
% 6.92/2.71  tff(c_5271, plain, (![A_144, C_145, B_146]: (k2_xboole_0(A_144, k4_xboole_0(k3_xboole_0(A_144, C_145), B_146))=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_359, c_5148])).
% 6.92/2.71  tff(c_938, plain, (![A_7, B_66]: (k2_xboole_0(k4_xboole_0(A_7, B_66), A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4, c_923])).
% 6.92/2.71  tff(c_205, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, A_38))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_155])).
% 6.92/2.71  tff(c_217, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k2_xboole_0(B_39, A_38))=k4_xboole_0(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_205, c_12])).
% 6.92/2.71  tff(c_237, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k2_xboole_0(B_39, A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_217])).
% 6.92/2.71  tff(c_374, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_364, c_237])).
% 6.92/2.71  tff(c_588, plain, (![A_7, C_55]: (k4_xboole_0(A_7, k2_xboole_0(A_7, C_55))=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_7, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_550])).
% 6.92/2.71  tff(c_710, plain, (![A_61, C_62]: (k4_xboole_0(A_61, k2_xboole_0(A_61, C_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_588])).
% 6.92/2.71  tff(c_737, plain, (![A_61, C_62]: (k3_xboole_0(A_61, k2_xboole_0(A_61, C_62))=k4_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_710, c_12])).
% 6.92/2.71  tff(c_1178, plain, (![A_75, C_76]: (k3_xboole_0(A_75, k2_xboole_0(A_75, C_76))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_737])).
% 6.92/2.71  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k4_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.92/2.71  tff(c_1193, plain, (![A_75, B_14, C_76]: (k4_xboole_0(A_75, k4_xboole_0(B_14, k2_xboole_0(A_75, C_76)))=k2_xboole_0(k4_xboole_0(A_75, B_14), A_75))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_14])).
% 6.92/2.71  tff(c_5928, plain, (![A_156, B_157, C_158]: (k4_xboole_0(A_156, k4_xboole_0(B_157, k2_xboole_0(A_156, C_158)))=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1193])).
% 6.92/2.71  tff(c_6158, plain, (![A_159, B_160]: (k4_xboole_0(A_159, k4_xboole_0(B_160, A_159))=A_159)), inference(superposition, [status(thm), theory('equality')], [c_5271, c_5928])).
% 6.92/2.71  tff(c_6228, plain, (![A_159, B_160]: (k3_xboole_0(A_159, k4_xboole_0(B_160, A_159))=k4_xboole_0(A_159, A_159))), inference(superposition, [status(thm), theory('equality')], [c_6158, c_12])).
% 6.92/2.71  tff(c_6852, plain, (![A_166, B_167]: (k3_xboole_0(A_166, k4_xboole_0(B_167, A_166))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6228])).
% 6.92/2.71  tff(c_413, plain, (![A_48, B_49, C_50]: (k5_xboole_0(k5_xboole_0(A_48, B_49), C_50)=k5_xboole_0(A_48, k5_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.71  tff(c_22, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.92/2.71  tff(c_426, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k5_xboole_0(B_49, k3_xboole_0(A_48, B_49)))=k2_xboole_0(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_413, c_22])).
% 6.92/2.71  tff(c_6894, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k5_xboole_0(k4_xboole_0(B_167, A_166), k1_xboole_0))=k2_xboole_0(A_166, k4_xboole_0(B_167, A_166)))), inference(superposition, [status(thm), theory('equality')], [c_6852, c_426])).
% 6.92/2.71  tff(c_7030, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k4_xboole_0(B_167, A_166))=k2_xboole_0(A_166, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18, c_6894])).
% 6.92/2.71  tff(c_24, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.92/2.71  tff(c_16047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7030, c_24])).
% 6.92/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.71  
% 6.92/2.71  Inference rules
% 6.92/2.71  ----------------------
% 6.92/2.71  #Ref     : 0
% 6.92/2.71  #Sup     : 3992
% 6.92/2.71  #Fact    : 0
% 6.92/2.71  #Define  : 0
% 6.92/2.71  #Split   : 0
% 6.92/2.71  #Chain   : 0
% 6.92/2.71  #Close   : 0
% 6.92/2.71  
% 6.92/2.71  Ordering : KBO
% 6.92/2.71  
% 6.92/2.71  Simplification rules
% 6.92/2.71  ----------------------
% 6.92/2.71  #Subsume      : 0
% 6.92/2.71  #Demod        : 4117
% 6.92/2.71  #Tautology    : 2951
% 6.92/2.71  #SimpNegUnit  : 0
% 6.92/2.71  #BackRed      : 6
% 6.92/2.71  
% 6.92/2.71  #Partial instantiations: 0
% 6.92/2.71  #Strategies tried      : 1
% 6.92/2.71  
% 6.92/2.71  Timing (in seconds)
% 6.92/2.71  ----------------------
% 6.92/2.71  Preprocessing        : 0.27
% 6.92/2.71  Parsing              : 0.15
% 6.92/2.72  CNF conversion       : 0.02
% 6.92/2.72  Main loop            : 1.64
% 6.92/2.72  Inferencing          : 0.47
% 6.92/2.72  Reduction            : 0.81
% 6.92/2.72  Demodulation         : 0.69
% 6.92/2.72  BG Simplification    : 0.05
% 6.92/2.72  Subsumption          : 0.22
% 6.92/2.72  Abstraction          : 0.09
% 6.92/2.72  MUC search           : 0.00
% 6.92/2.72  Cooper               : 0.00
% 6.92/2.72  Total                : 1.95
% 6.92/2.72  Index Insertion      : 0.00
% 6.92/2.72  Index Deletion       : 0.00
% 6.92/2.72  Index Matching       : 0.00
% 6.92/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

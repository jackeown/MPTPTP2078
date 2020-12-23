%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 8.10s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 197 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :   59 ( 187 expanded)
%              Number of equality atoms :   58 ( 186 expanded)
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

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_xboole_0(A_2,k4_xboole_0(B_3,A_2)) = k2_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_68,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6256,plain,(
    ! [A_160,B_161,C_162] : k4_xboole_0(A_160,k2_xboole_0(k4_xboole_0(A_160,B_161),C_162)) = k4_xboole_0(k3_xboole_0(A_160,B_161),C_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_635,plain,(
    ! [A_58,B_59,C_60] : k2_xboole_0(k4_xboole_0(A_58,B_59),k4_xboole_0(A_58,C_60)) = k4_xboole_0(A_58,k3_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_699,plain,(
    ! [A_4,B_59] : k4_xboole_0(A_4,k3_xboole_0(B_59,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_4,B_59),A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_635])).

tff(c_712,plain,(
    ! [A_4,B_59] : k2_xboole_0(k4_xboole_0(A_4,B_59),A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_699])).

tff(c_6552,plain,(
    ! [A_163,B_164,C_165] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_163,B_164),C_165),A_163) = A_163 ),
    inference(superposition,[status(thm),theory(equality)],[c_6256,c_712])).

tff(c_6733,plain,(
    ! [A_163,B_164,B_9] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_163,B_164),B_9),A_163) = A_163 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6552])).

tff(c_6793,plain,(
    ! [A_166,B_167,B_168] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_166,B_167),B_168),A_166) = A_166 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6552])).

tff(c_332,plain,(
    ! [A_44,B_45] : k5_xboole_0(k5_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_353,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_332])).

tff(c_359,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_353])).

tff(c_364,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_353])).

tff(c_158,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_36,k4_xboole_0(A_35,B_36))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_68])).

tff(c_205,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_158])).

tff(c_220,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = k4_xboole_0(A_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_10])).

tff(c_237,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_220])).

tff(c_374,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_237])).

tff(c_922,plain,(
    ! [A_68,B_69,C_70] : k3_xboole_0(k4_xboole_0(A_68,B_69),k4_xboole_0(A_68,C_70)) = k4_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_978,plain,(
    ! [A_4,C_70] : k4_xboole_0(A_4,k2_xboole_0(A_4,C_70)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_4,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_922])).

tff(c_1078,plain,(
    ! [A_73,C_74] : k4_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_978])).

tff(c_1117,plain,(
    ! [A_73,C_74] : k2_xboole_0(k2_xboole_0(A_73,C_74),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_73,C_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_4])).

tff(c_1174,plain,(
    ! [A_73,C_74] : k2_xboole_0(k2_xboole_0(A_73,C_74),A_73) = k2_xboole_0(A_73,C_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_1117])).

tff(c_6825,plain,(
    ! [A_166,B_167,B_168] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_166,B_167),B_168),A_166) = k2_xboole_0(A_166,k3_xboole_0(k3_xboole_0(A_166,B_167),B_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6793,c_1174])).

tff(c_6971,plain,(
    ! [A_166,B_167,B_168] : k2_xboole_0(A_166,k3_xboole_0(k3_xboole_0(A_166,B_167),B_168)) = A_166 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6733,c_6825])).

tff(c_1120,plain,(
    ! [A_73,C_74] : k3_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = k4_xboole_0(A_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_10])).

tff(c_1291,plain,(
    ! [A_77,C_78] : k3_xboole_0(A_77,k2_xboole_0(A_77,C_78)) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1120])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k4_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1306,plain,(
    ! [A_77,B_11,C_78] : k4_xboole_0(A_77,k4_xboole_0(B_11,k2_xboole_0(A_77,C_78))) = k2_xboole_0(k4_xboole_0(A_77,B_11),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_12])).

tff(c_7745,plain,(
    ! [A_178,B_179,C_180] : k4_xboole_0(A_178,k4_xboole_0(B_179,k2_xboole_0(A_178,C_180))) = A_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_1306])).

tff(c_8018,plain,(
    ! [A_181,B_182] : k4_xboole_0(A_181,k4_xboole_0(B_182,A_181)) = A_181 ),
    inference(superposition,[status(thm),theory(equality)],[c_6971,c_7745])).

tff(c_8104,plain,(
    ! [A_181,B_182] : k3_xboole_0(A_181,k4_xboole_0(B_182,A_181)) = k4_xboole_0(A_181,A_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_8018,c_10])).

tff(c_8446,plain,(
    ! [A_186,B_187] : k3_xboole_0(A_186,k4_xboole_0(B_187,A_186)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8104])).

tff(c_413,plain,(
    ! [A_48,B_49,C_50] : k5_xboole_0(k5_xboole_0(A_48,B_49),C_50) = k5_xboole_0(A_48,k5_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_426,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k5_xboole_0(B_49,k3_xboole_0(A_48,B_49))) = k2_xboole_0(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_22])).

tff(c_8511,plain,(
    ! [A_186,B_187] : k5_xboole_0(A_186,k5_xboole_0(k4_xboole_0(B_187,A_186),k1_xboole_0)) = k2_xboole_0(A_186,k4_xboole_0(B_187,A_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8446,c_426])).

tff(c_8656,plain,(
    ! [A_186,B_187] : k5_xboole_0(A_186,k4_xboole_0(B_187,A_186)) = k2_xboole_0(A_186,B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_8511])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8656,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.10/3.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.10/3.05  
% 8.10/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.10/3.05  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.10/3.05  
% 8.10/3.05  %Foreground sorts:
% 8.10/3.05  
% 8.10/3.05  
% 8.10/3.05  %Background operators:
% 8.10/3.05  
% 8.10/3.05  
% 8.10/3.05  %Foreground operators:
% 8.10/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.10/3.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.10/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.10/3.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.10/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.10/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.10/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.10/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.10/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.10/3.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.10/3.05  
% 8.10/3.07  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.10/3.07  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.10/3.07  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.10/3.07  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.10/3.07  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.10/3.07  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.10/3.07  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 8.10/3.07  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.10/3.07  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 8.10/3.07  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 8.10/3.07  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.10/3.07  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.10/3.07  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, k4_xboole_0(B_3, A_2))=k2_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.10/3.07  tff(c_18, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.10/3.07  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.10/3.07  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/3.07  tff(c_50, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.10/3.07  tff(c_65, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_50])).
% 8.10/3.07  tff(c_68, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_65])).
% 8.10/3.07  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.10/3.07  tff(c_145, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.10/3.07  tff(c_6256, plain, (![A_160, B_161, C_162]: (k4_xboole_0(A_160, k2_xboole_0(k4_xboole_0(A_160, B_161), C_162))=k4_xboole_0(k3_xboole_0(A_160, B_161), C_162))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 8.10/3.07  tff(c_635, plain, (![A_58, B_59, C_60]: (k2_xboole_0(k4_xboole_0(A_58, B_59), k4_xboole_0(A_58, C_60))=k4_xboole_0(A_58, k3_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.10/3.07  tff(c_699, plain, (![A_4, B_59]: (k4_xboole_0(A_4, k3_xboole_0(B_59, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_4, B_59), A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_635])).
% 8.10/3.07  tff(c_712, plain, (![A_4, B_59]: (k2_xboole_0(k4_xboole_0(A_4, B_59), A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_699])).
% 8.10/3.07  tff(c_6552, plain, (![A_163, B_164, C_165]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_163, B_164), C_165), A_163)=A_163)), inference(superposition, [status(thm), theory('equality')], [c_6256, c_712])).
% 8.10/3.07  tff(c_6733, plain, (![A_163, B_164, B_9]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_163, B_164), B_9), A_163)=A_163)), inference(superposition, [status(thm), theory('equality')], [c_10, c_6552])).
% 8.10/3.07  tff(c_6793, plain, (![A_166, B_167, B_168]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_166, B_167), B_168), A_166)=A_166)), inference(superposition, [status(thm), theory('equality')], [c_10, c_6552])).
% 8.10/3.07  tff(c_332, plain, (![A_44, B_45]: (k5_xboole_0(k5_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.10/3.07  tff(c_353, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_332])).
% 8.10/3.07  tff(c_359, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_353])).
% 8.10/3.07  tff(c_364, plain, (![A_46]: (k2_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_353])).
% 8.10/3.07  tff(c_158, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_36, k4_xboole_0(A_35, B_36)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_68])).
% 8.10/3.07  tff(c_205, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, A_38))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_158])).
% 8.10/3.07  tff(c_220, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k2_xboole_0(B_39, A_38))=k4_xboole_0(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_205, c_10])).
% 8.10/3.07  tff(c_237, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k2_xboole_0(B_39, A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_220])).
% 8.10/3.07  tff(c_374, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_364, c_237])).
% 8.10/3.07  tff(c_922, plain, (![A_68, B_69, C_70]: (k3_xboole_0(k4_xboole_0(A_68, B_69), k4_xboole_0(A_68, C_70))=k4_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.10/3.07  tff(c_978, plain, (![A_4, C_70]: (k4_xboole_0(A_4, k2_xboole_0(A_4, C_70))=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_4, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_922])).
% 8.10/3.07  tff(c_1078, plain, (![A_73, C_74]: (k4_xboole_0(A_73, k2_xboole_0(A_73, C_74))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_978])).
% 8.10/3.07  tff(c_1117, plain, (![A_73, C_74]: (k2_xboole_0(k2_xboole_0(A_73, C_74), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_73, C_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_4])).
% 8.10/3.07  tff(c_1174, plain, (![A_73, C_74]: (k2_xboole_0(k2_xboole_0(A_73, C_74), A_73)=k2_xboole_0(A_73, C_74))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_1117])).
% 8.10/3.07  tff(c_6825, plain, (![A_166, B_167, B_168]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_166, B_167), B_168), A_166)=k2_xboole_0(A_166, k3_xboole_0(k3_xboole_0(A_166, B_167), B_168)))), inference(superposition, [status(thm), theory('equality')], [c_6793, c_1174])).
% 8.10/3.07  tff(c_6971, plain, (![A_166, B_167, B_168]: (k2_xboole_0(A_166, k3_xboole_0(k3_xboole_0(A_166, B_167), B_168))=A_166)), inference(demodulation, [status(thm), theory('equality')], [c_6733, c_6825])).
% 8.10/3.07  tff(c_1120, plain, (![A_73, C_74]: (k3_xboole_0(A_73, k2_xboole_0(A_73, C_74))=k4_xboole_0(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_10])).
% 8.10/3.07  tff(c_1291, plain, (![A_77, C_78]: (k3_xboole_0(A_77, k2_xboole_0(A_77, C_78))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1120])).
% 8.10/3.07  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k4_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.10/3.07  tff(c_1306, plain, (![A_77, B_11, C_78]: (k4_xboole_0(A_77, k4_xboole_0(B_11, k2_xboole_0(A_77, C_78)))=k2_xboole_0(k4_xboole_0(A_77, B_11), A_77))), inference(superposition, [status(thm), theory('equality')], [c_1291, c_12])).
% 8.10/3.07  tff(c_7745, plain, (![A_178, B_179, C_180]: (k4_xboole_0(A_178, k4_xboole_0(B_179, k2_xboole_0(A_178, C_180)))=A_178)), inference(demodulation, [status(thm), theory('equality')], [c_712, c_1306])).
% 8.10/3.07  tff(c_8018, plain, (![A_181, B_182]: (k4_xboole_0(A_181, k4_xboole_0(B_182, A_181))=A_181)), inference(superposition, [status(thm), theory('equality')], [c_6971, c_7745])).
% 8.10/3.07  tff(c_8104, plain, (![A_181, B_182]: (k3_xboole_0(A_181, k4_xboole_0(B_182, A_181))=k4_xboole_0(A_181, A_181))), inference(superposition, [status(thm), theory('equality')], [c_8018, c_10])).
% 8.10/3.07  tff(c_8446, plain, (![A_186, B_187]: (k3_xboole_0(A_186, k4_xboole_0(B_187, A_186))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8104])).
% 8.10/3.07  tff(c_413, plain, (![A_48, B_49, C_50]: (k5_xboole_0(k5_xboole_0(A_48, B_49), C_50)=k5_xboole_0(A_48, k5_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.10/3.07  tff(c_22, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.10/3.07  tff(c_426, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k5_xboole_0(B_49, k3_xboole_0(A_48, B_49)))=k2_xboole_0(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_413, c_22])).
% 8.10/3.07  tff(c_8511, plain, (![A_186, B_187]: (k5_xboole_0(A_186, k5_xboole_0(k4_xboole_0(B_187, A_186), k1_xboole_0))=k2_xboole_0(A_186, k4_xboole_0(B_187, A_186)))), inference(superposition, [status(thm), theory('equality')], [c_8446, c_426])).
% 8.10/3.07  tff(c_8656, plain, (![A_186, B_187]: (k5_xboole_0(A_186, k4_xboole_0(B_187, A_186))=k2_xboole_0(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_8511])).
% 8.10/3.07  tff(c_24, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.10/3.07  tff(c_18705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8656, c_24])).
% 8.10/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.10/3.07  
% 8.10/3.07  Inference rules
% 8.10/3.07  ----------------------
% 8.10/3.07  #Ref     : 0
% 8.10/3.07  #Sup     : 4664
% 8.10/3.07  #Fact    : 0
% 8.10/3.07  #Define  : 0
% 8.10/3.07  #Split   : 0
% 8.10/3.07  #Chain   : 0
% 8.10/3.07  #Close   : 0
% 8.10/3.07  
% 8.10/3.07  Ordering : KBO
% 8.10/3.07  
% 8.10/3.07  Simplification rules
% 8.10/3.07  ----------------------
% 8.10/3.07  #Subsume      : 0
% 8.10/3.07  #Demod        : 4803
% 8.10/3.07  #Tautology    : 3357
% 8.10/3.07  #SimpNegUnit  : 0
% 8.10/3.07  #BackRed      : 4
% 8.10/3.07  
% 8.10/3.07  #Partial instantiations: 0
% 8.10/3.07  #Strategies tried      : 1
% 8.10/3.07  
% 8.10/3.07  Timing (in seconds)
% 8.10/3.07  ----------------------
% 8.10/3.07  Preprocessing        : 0.30
% 8.10/3.07  Parsing              : 0.17
% 8.10/3.07  CNF conversion       : 0.02
% 8.10/3.07  Main loop            : 1.95
% 8.10/3.07  Inferencing          : 0.54
% 8.10/3.07  Reduction            : 0.97
% 8.10/3.07  Demodulation         : 0.83
% 8.10/3.07  BG Simplification    : 0.07
% 8.10/3.07  Subsumption          : 0.28
% 8.10/3.07  Abstraction          : 0.11
% 8.10/3.07  MUC search           : 0.00
% 8.10/3.07  Cooper               : 0.00
% 8.10/3.07  Total                : 2.29
% 8.10/3.07  Index Insertion      : 0.00
% 8.10/3.07  Index Deletion       : 0.00
% 8.10/3.07  Index Matching       : 0.00
% 8.10/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:42 EST 2020

% Result     : Theorem 31.72s
% Output     : CNFRefutation 31.72s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 263 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 254 expanded)
%              Number of equality atoms :   57 ( 253 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_119,plain,(
    ! [A_29,B_30] : k2_xboole_0(k5_xboole_0(A_29,B_30),k3_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k5_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k4_xboole_0(A_36,B_37),k3_xboole_0(A_36,C_38)) = k4_xboole_0(A_36,k4_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_419,plain,(
    ! [A_49,C_50,B_51] : k2_xboole_0(k3_xboole_0(A_49,C_50),k4_xboole_0(A_49,B_51)) = k4_xboole_0(A_49,k4_xboole_0(B_51,C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_472,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(B_53,B_53)) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_12])).

tff(c_555,plain,(
    ! [B_54] : k3_xboole_0(B_54,B_54) = B_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_10])).

tff(c_591,plain,(
    ! [B_55] : k2_xboole_0(B_55,k4_xboole_0(B_55,B_55)) = B_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_12])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_597,plain,(
    ! [B_55] : k2_xboole_0(B_55,B_55) = B_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_6])).

tff(c_140,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k4_xboole_0(A_31,B_32),C_33) = k4_xboole_0(A_31,k2_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [C_33,A_31,B_32] : k2_xboole_0(C_33,k4_xboole_0(A_31,k2_xboole_0(B_32,C_33))) = k2_xboole_0(C_33,k4_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_31,B_32,B_11] : k4_xboole_0(A_31,k2_xboole_0(B_32,k4_xboole_0(k4_xboole_0(A_31,B_32),B_11))) = k3_xboole_0(k4_xboole_0(A_31,B_32),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_5592,plain,(
    ! [A_147,B_148,B_149] : k4_xboole_0(A_147,k2_xboole_0(B_148,k4_xboole_0(A_147,k2_xboole_0(B_148,B_149)))) = k3_xboole_0(k4_xboole_0(A_147,B_148),B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_162])).

tff(c_5806,plain,(
    ! [A_147,A_1,B_2] : k4_xboole_0(A_147,k2_xboole_0(A_1,k4_xboole_0(A_147,k2_xboole_0(B_2,A_1)))) = k3_xboole_0(k4_xboole_0(A_147,A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5592])).

tff(c_23558,plain,(
    ! [A_284,A_285,B_286] : k4_xboole_0(A_284,k2_xboole_0(A_285,k4_xboole_0(A_284,B_286))) = k3_xboole_0(k4_xboole_0(A_284,A_285),B_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_5806])).

tff(c_23897,plain,(
    ! [A_284,B_286] : k3_xboole_0(k4_xboole_0(A_284,k4_xboole_0(A_284,B_286)),B_286) = k4_xboole_0(A_284,k4_xboole_0(A_284,B_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_23558])).

tff(c_23996,plain,(
    ! [A_284,B_286] : k3_xboole_0(k3_xboole_0(A_284,B_286),B_286) = k3_xboole_0(A_284,B_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_23897])).

tff(c_430,plain,(
    ! [A_49,B_51] : k4_xboole_0(A_49,k4_xboole_0(B_51,B_51)) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_12])).

tff(c_79,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_2178,plain,(
    ! [A_89,B_90] : k2_xboole_0(k4_xboole_0(A_89,B_90),k3_xboole_0(A_89,B_90)) = k2_xboole_0(A_89,k4_xboole_0(A_89,B_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k4_xboole_0(A_14,B_15),k3_xboole_0(A_14,C_16)) = k4_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2199,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(B_90,B_90)) = k2_xboole_0(A_89,k4_xboole_0(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_14])).

tff(c_2267,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_2199])).

tff(c_576,plain,(
    ! [B_54,B_15] : k4_xboole_0(B_54,k4_xboole_0(B_15,B_54)) = k2_xboole_0(k4_xboole_0(B_54,B_15),B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_14])).

tff(c_587,plain,(
    ! [B_54,B_15] : k4_xboole_0(B_54,k4_xboole_0(B_15,B_54)) = k2_xboole_0(B_54,k4_xboole_0(B_54,B_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_576])).

tff(c_16824,plain,(
    ! [B_54,B_15] : k4_xboole_0(B_54,k4_xboole_0(B_15,B_54)) = B_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_587])).

tff(c_92,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k4_xboole_0(B_28,A_27)) = k5_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [B_28,A_27] : k2_xboole_0(k4_xboole_0(B_28,A_27),k4_xboole_0(A_27,B_28)) = k5_xboole_0(A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_23909,plain,(
    ! [A_27,B_28] : k3_xboole_0(k4_xboole_0(A_27,k4_xboole_0(B_28,A_27)),B_28) = k4_xboole_0(A_27,k5_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_23558])).

tff(c_23998,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k5_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16824,c_23909])).

tff(c_5842,plain,(
    ! [A_147,A_1,B_2] : k4_xboole_0(A_147,k2_xboole_0(A_1,k4_xboole_0(A_147,B_2))) = k3_xboole_0(k4_xboole_0(A_147,A_1),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_5806])).

tff(c_660,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(A_58,k2_xboole_0(k4_xboole_0(A_58,B_59),C_60)) = k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_757,plain,(
    ! [A_58,A_1,B_59] : k4_xboole_0(A_58,k2_xboole_0(A_1,k4_xboole_0(A_58,B_59))) = k4_xboole_0(k3_xboole_0(A_58,B_59),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_660])).

tff(c_29950,plain,(
    ! [A_58,B_59,A_1] : k4_xboole_0(k3_xboole_0(A_58,B_59),A_1) = k3_xboole_0(k4_xboole_0(A_58,A_1),B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5842,c_757])).

tff(c_24003,plain,(
    ! [A_287,B_288] : k4_xboole_0(A_287,k5_xboole_0(A_287,B_288)) = k3_xboole_0(A_287,B_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16824,c_23909])).

tff(c_93314,plain,(
    ! [A_602,B_603] : k4_xboole_0(k5_xboole_0(A_602,B_603),k3_xboole_0(A_602,B_603)) = k5_xboole_0(A_602,B_603) ),
    inference(superposition,[status(thm),theory(equality)],[c_24003,c_16824])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93555,plain,(
    ! [A_602,B_603] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_602,B_603),k5_xboole_0(A_602,B_603)),k5_xboole_0(A_602,B_603)) = k5_xboole_0(k3_xboole_0(A_602,B_603),k5_xboole_0(A_602,B_603)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93314,c_4])).

tff(c_93894,plain,(
    ! [A_602,B_603] : k5_xboole_0(k3_xboole_0(A_602,B_603),k5_xboole_0(A_602,B_603)) = k2_xboole_0(A_602,B_603) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_2,c_23996,c_23998,c_2,c_29950,c_93555])).

tff(c_185,plain,(
    ! [B_34,A_35] : k2_xboole_0(k4_xboole_0(B_34,A_35),k4_xboole_0(A_35,B_34)) = k5_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_191,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,A_35) = k5_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_18,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_259,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_18])).

tff(c_113021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93894,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.72/22.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.72/22.25  
% 31.72/22.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.72/22.25  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 31.72/22.25  
% 31.72/22.25  %Foreground sorts:
% 31.72/22.25  
% 31.72/22.25  
% 31.72/22.25  %Background operators:
% 31.72/22.25  
% 31.72/22.25  
% 31.72/22.25  %Foreground operators:
% 31.72/22.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.72/22.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.72/22.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 31.72/22.25  tff('#skF_2', type, '#skF_2': $i).
% 31.72/22.25  tff('#skF_1', type, '#skF_1': $i).
% 31.72/22.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.72/22.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.72/22.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.72/22.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.72/22.25  
% 31.72/22.27  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 31.72/22.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 31.72/22.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 31.72/22.27  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 31.72/22.27  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 31.72/22.27  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 31.72/22.27  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 31.72/22.27  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 31.72/22.27  tff(f_44, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 31.72/22.27  tff(c_119, plain, (![A_29, B_30]: (k2_xboole_0(k5_xboole_0(A_29, B_30), k3_xboole_0(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.72/22.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 31.72/22.27  tff(c_128, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k5_xboole_0(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 31.72/22.27  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.72/22.27  tff(c_230, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k4_xboole_0(A_36, B_37), k3_xboole_0(A_36, C_38))=k4_xboole_0(A_36, k4_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.72/22.27  tff(c_419, plain, (![A_49, C_50, B_51]: (k2_xboole_0(k3_xboole_0(A_49, C_50), k4_xboole_0(A_49, B_51))=k4_xboole_0(A_49, k4_xboole_0(B_51, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_2])).
% 31.72/22.27  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.72/22.27  tff(c_472, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(B_53, B_53))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_419, c_12])).
% 31.72/22.27  tff(c_555, plain, (![B_54]: (k3_xboole_0(B_54, B_54)=B_54)), inference(superposition, [status(thm), theory('equality')], [c_472, c_10])).
% 31.72/22.27  tff(c_591, plain, (![B_55]: (k2_xboole_0(B_55, k4_xboole_0(B_55, B_55))=B_55)), inference(superposition, [status(thm), theory('equality')], [c_555, c_12])).
% 31.72/22.27  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.72/22.27  tff(c_597, plain, (![B_55]: (k2_xboole_0(B_55, B_55)=B_55)), inference(superposition, [status(thm), theory('equality')], [c_591, c_6])).
% 31.72/22.27  tff(c_140, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k4_xboole_0(A_31, B_32), C_33)=k4_xboole_0(A_31, k2_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.72/22.27  tff(c_155, plain, (![C_33, A_31, B_32]: (k2_xboole_0(C_33, k4_xboole_0(A_31, k2_xboole_0(B_32, C_33)))=k2_xboole_0(C_33, k4_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_6])).
% 31.72/22.27  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.72/22.27  tff(c_162, plain, (![A_31, B_32, B_11]: (k4_xboole_0(A_31, k2_xboole_0(B_32, k4_xboole_0(k4_xboole_0(A_31, B_32), B_11)))=k3_xboole_0(k4_xboole_0(A_31, B_32), B_11))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 31.72/22.27  tff(c_5592, plain, (![A_147, B_148, B_149]: (k4_xboole_0(A_147, k2_xboole_0(B_148, k4_xboole_0(A_147, k2_xboole_0(B_148, B_149))))=k3_xboole_0(k4_xboole_0(A_147, B_148), B_149))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_162])).
% 31.72/22.27  tff(c_5806, plain, (![A_147, A_1, B_2]: (k4_xboole_0(A_147, k2_xboole_0(A_1, k4_xboole_0(A_147, k2_xboole_0(B_2, A_1))))=k3_xboole_0(k4_xboole_0(A_147, A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5592])).
% 31.72/22.27  tff(c_23558, plain, (![A_284, A_285, B_286]: (k4_xboole_0(A_284, k2_xboole_0(A_285, k4_xboole_0(A_284, B_286)))=k3_xboole_0(k4_xboole_0(A_284, A_285), B_286))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_5806])).
% 31.72/22.27  tff(c_23897, plain, (![A_284, B_286]: (k3_xboole_0(k4_xboole_0(A_284, k4_xboole_0(A_284, B_286)), B_286)=k4_xboole_0(A_284, k4_xboole_0(A_284, B_286)))), inference(superposition, [status(thm), theory('equality')], [c_597, c_23558])).
% 31.72/22.27  tff(c_23996, plain, (![A_284, B_286]: (k3_xboole_0(k3_xboole_0(A_284, B_286), B_286)=k3_xboole_0(A_284, B_286))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_23897])).
% 31.72/22.27  tff(c_430, plain, (![A_49, B_51]: (k4_xboole_0(A_49, k4_xboole_0(B_51, B_51))=A_49)), inference(superposition, [status(thm), theory('equality')], [c_419, c_12])).
% 31.72/22.27  tff(c_79, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.72/22.27  tff(c_88, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_79])).
% 31.72/22.27  tff(c_2178, plain, (![A_89, B_90]: (k2_xboole_0(k4_xboole_0(A_89, B_90), k3_xboole_0(A_89, B_90))=k2_xboole_0(A_89, k4_xboole_0(A_89, B_90)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_88])).
% 31.72/22.27  tff(c_14, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k4_xboole_0(A_14, B_15), k3_xboole_0(A_14, C_16))=k4_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.72/22.27  tff(c_2199, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(B_90, B_90))=k2_xboole_0(A_89, k4_xboole_0(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_2178, c_14])).
% 31.72/22.27  tff(c_2267, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k4_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_430, c_2199])).
% 31.72/22.27  tff(c_576, plain, (![B_54, B_15]: (k4_xboole_0(B_54, k4_xboole_0(B_15, B_54))=k2_xboole_0(k4_xboole_0(B_54, B_15), B_54))), inference(superposition, [status(thm), theory('equality')], [c_555, c_14])).
% 31.72/22.27  tff(c_587, plain, (![B_54, B_15]: (k4_xboole_0(B_54, k4_xboole_0(B_15, B_54))=k2_xboole_0(B_54, k4_xboole_0(B_54, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_576])).
% 31.72/22.27  tff(c_16824, plain, (![B_54, B_15]: (k4_xboole_0(B_54, k4_xboole_0(B_15, B_54))=B_54)), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_587])).
% 31.72/22.27  tff(c_92, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k4_xboole_0(B_28, A_27))=k5_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.72/22.27  tff(c_98, plain, (![B_28, A_27]: (k2_xboole_0(k4_xboole_0(B_28, A_27), k4_xboole_0(A_27, B_28))=k5_xboole_0(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 31.72/22.27  tff(c_23909, plain, (![A_27, B_28]: (k3_xboole_0(k4_xboole_0(A_27, k4_xboole_0(B_28, A_27)), B_28)=k4_xboole_0(A_27, k5_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_23558])).
% 31.72/22.27  tff(c_23998, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k5_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_16824, c_23909])).
% 31.72/22.27  tff(c_5842, plain, (![A_147, A_1, B_2]: (k4_xboole_0(A_147, k2_xboole_0(A_1, k4_xboole_0(A_147, B_2)))=k3_xboole_0(k4_xboole_0(A_147, A_1), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_5806])).
% 31.72/22.27  tff(c_660, plain, (![A_58, B_59, C_60]: (k4_xboole_0(A_58, k2_xboole_0(k4_xboole_0(A_58, B_59), C_60))=k4_xboole_0(k3_xboole_0(A_58, B_59), C_60))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 31.72/22.27  tff(c_757, plain, (![A_58, A_1, B_59]: (k4_xboole_0(A_58, k2_xboole_0(A_1, k4_xboole_0(A_58, B_59)))=k4_xboole_0(k3_xboole_0(A_58, B_59), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_660])).
% 31.72/22.27  tff(c_29950, plain, (![A_58, B_59, A_1]: (k4_xboole_0(k3_xboole_0(A_58, B_59), A_1)=k3_xboole_0(k4_xboole_0(A_58, A_1), B_59))), inference(demodulation, [status(thm), theory('equality')], [c_5842, c_757])).
% 31.72/22.27  tff(c_24003, plain, (![A_287, B_288]: (k4_xboole_0(A_287, k5_xboole_0(A_287, B_288))=k3_xboole_0(A_287, B_288))), inference(demodulation, [status(thm), theory('equality')], [c_16824, c_23909])).
% 31.72/22.27  tff(c_93314, plain, (![A_602, B_603]: (k4_xboole_0(k5_xboole_0(A_602, B_603), k3_xboole_0(A_602, B_603))=k5_xboole_0(A_602, B_603))), inference(superposition, [status(thm), theory('equality')], [c_24003, c_16824])).
% 31.72/22.27  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.72/22.27  tff(c_93555, plain, (![A_602, B_603]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_602, B_603), k5_xboole_0(A_602, B_603)), k5_xboole_0(A_602, B_603))=k5_xboole_0(k3_xboole_0(A_602, B_603), k5_xboole_0(A_602, B_603)))), inference(superposition, [status(thm), theory('equality')], [c_93314, c_4])).
% 31.72/22.27  tff(c_93894, plain, (![A_602, B_603]: (k5_xboole_0(k3_xboole_0(A_602, B_603), k5_xboole_0(A_602, B_603))=k2_xboole_0(A_602, B_603))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_2, c_23996, c_23998, c_2, c_29950, c_93555])).
% 31.72/22.27  tff(c_185, plain, (![B_34, A_35]: (k2_xboole_0(k4_xboole_0(B_34, A_35), k4_xboole_0(A_35, B_34))=k5_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 31.72/22.27  tff(c_191, plain, (![B_34, A_35]: (k5_xboole_0(B_34, A_35)=k5_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 31.72/22.27  tff(c_18, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 31.72/22.27  tff(c_259, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_18])).
% 31.72/22.27  tff(c_113021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93894, c_259])).
% 31.72/22.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.72/22.27  
% 31.72/22.27  Inference rules
% 31.72/22.27  ----------------------
% 31.72/22.27  #Ref     : 0
% 31.72/22.27  #Sup     : 28595
% 31.72/22.27  #Fact    : 0
% 31.72/22.27  #Define  : 0
% 31.72/22.27  #Split   : 0
% 31.72/22.27  #Chain   : 0
% 31.72/22.27  #Close   : 0
% 31.72/22.27  
% 31.72/22.27  Ordering : KBO
% 31.72/22.27  
% 31.72/22.27  Simplification rules
% 31.72/22.27  ----------------------
% 31.72/22.27  #Subsume      : 702
% 31.72/22.27  #Demod        : 35724
% 31.72/22.27  #Tautology    : 12814
% 31.72/22.27  #SimpNegUnit  : 0
% 31.72/22.27  #BackRed      : 43
% 31.72/22.27  
% 31.72/22.27  #Partial instantiations: 0
% 31.72/22.27  #Strategies tried      : 1
% 31.72/22.27  
% 31.72/22.27  Timing (in seconds)
% 31.72/22.27  ----------------------
% 31.72/22.27  Preprocessing        : 0.43
% 31.72/22.27  Parsing              : 0.23
% 31.72/22.27  CNF conversion       : 0.03
% 31.72/22.27  Main loop            : 21.03
% 31.72/22.27  Inferencing          : 2.72
% 31.72/22.27  Reduction            : 13.92
% 31.72/22.27  Demodulation         : 13.15
% 31.72/22.27  BG Simplification    : 0.45
% 31.72/22.27  Subsumption          : 3.17
% 31.72/22.27  Abstraction          : 0.87
% 31.72/22.27  MUC search           : 0.00
% 31.72/22.27  Cooper               : 0.00
% 31.72/22.27  Total                : 21.50
% 31.72/22.27  Index Insertion      : 0.00
% 31.72/22.27  Index Deletion       : 0.00
% 31.72/22.27  Index Matching       : 0.00
% 31.72/22.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

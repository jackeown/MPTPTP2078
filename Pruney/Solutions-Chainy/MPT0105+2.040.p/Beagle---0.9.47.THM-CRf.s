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
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 9.96s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 433 expanded)
%              Number of leaves         :   19 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :   52 ( 423 expanded)
%              Number of equality atoms :   51 ( 422 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k3_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_117,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [A_30] : k4_xboole_0(A_30,k3_xboole_0(A_30,k1_xboole_0)) = k3_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_431,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k4_xboole_0(A_45,B_46),C_47) = k4_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_482,plain,(
    ! [A_3,C_47] : k4_xboole_0(k3_xboole_0(A_3,k1_xboole_0),C_47) = k4_xboole_0(A_3,k2_xboole_0(A_3,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_431])).

tff(c_521,plain,(
    ! [A_48,C_49] : k3_xboole_0(A_48,k4_xboole_0(k1_xboole_0,C_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_482])).

tff(c_535,plain,(
    ! [A_48] : k3_xboole_0(A_48,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_521])).

tff(c_554,plain,(
    ! [A_48] : k3_xboole_0(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_535])).

tff(c_305,plain,(
    ! [A_41,B_42] : k5_xboole_0(k5_xboole_0(A_41,B_42),k3_xboole_0(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_342,plain,(
    ! [A_14] : k5_xboole_0(A_14,k3_xboole_0(A_14,k1_xboole_0)) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_305])).

tff(c_623,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_342])).

tff(c_628,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_623])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_30] : k2_xboole_0(A_30,k3_xboole_0(A_30,k1_xboole_0)) = k2_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2])).

tff(c_624,plain,(
    ! [A_30] : k2_xboole_0(A_30,k1_xboole_0) = k2_xboole_0(A_30,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_113])).

tff(c_926,plain,(
    ! [A_30] : k2_xboole_0(A_30,A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_624])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k4_xboole_0(k4_xboole_0(A_4,B_5),C_6) = k4_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_646,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k2_xboole_0(B_53,k1_xboole_0)) = k4_xboole_0(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_431])).

tff(c_708,plain,(
    ! [B_54] : k4_xboole_0(B_54,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_8])).

tff(c_751,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(B_5,k4_xboole_0(A_4,B_5))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_708])).

tff(c_768,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(B_5,A_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_751])).

tff(c_6690,plain,(
    ! [C_163,A_164,B_165] : k2_xboole_0(C_163,k4_xboole_0(A_164,k2_xboole_0(B_165,C_163))) = k2_xboole_0(C_163,k4_xboole_0(A_164,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_2])).

tff(c_6909,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k2_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_6690])).

tff(c_6995,plain,(
    ! [A_166,B_167] : k2_xboole_0(A_166,k4_xboole_0(A_166,B_167)) = A_166 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_6909])).

tff(c_7477,plain,(
    ! [A_170,B_171] : k2_xboole_0(A_170,k3_xboole_0(A_170,B_171)) = A_170 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6995])).

tff(c_868,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(B_59,A_58)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_751])).

tff(c_1505,plain,(
    ! [B_76,A_77] : k4_xboole_0(k4_xboole_0(B_76,A_77),k2_xboole_0(A_77,B_76)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_868])).

tff(c_1520,plain,(
    ! [B_76,A_77] : k4_xboole_0(B_76,k2_xboole_0(A_77,k2_xboole_0(A_77,B_76))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_6])).

tff(c_7585,plain,(
    ! [A_170,B_171] : k4_xboole_0(k3_xboole_0(A_170,B_171),k2_xboole_0(A_170,A_170)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7477,c_1520])).

tff(c_7738,plain,(
    ! [A_170,B_171] : k3_xboole_0(A_170,k4_xboole_0(B_171,A_170)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_926,c_7585])).

tff(c_18,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32371,plain,(
    ! [A_348,B_349] : k5_xboole_0(k2_xboole_0(A_348,B_349),k3_xboole_0(k5_xboole_0(A_348,B_349),k3_xboole_0(A_348,B_349))) = k2_xboole_0(k5_xboole_0(A_348,B_349),k3_xboole_0(A_348,B_349)) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_18])).

tff(c_32611,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)),k3_xboole_0(A_1,k4_xboole_0(B_2,A_1)))) = k2_xboole_0(k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)),k3_xboole_0(A_1,k4_xboole_0(B_2,A_1))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32371])).

tff(c_32680,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_7738,c_14,c_554,c_7738,c_32611])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32680,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.96/4.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.96/4.03  
% 9.96/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.96/4.03  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 9.96/4.03  
% 9.96/4.03  %Foreground sorts:
% 9.96/4.03  
% 9.96/4.03  
% 9.96/4.03  %Background operators:
% 9.96/4.03  
% 9.96/4.03  
% 9.96/4.03  %Foreground operators:
% 9.96/4.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.96/4.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.96/4.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.96/4.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.96/4.03  tff('#skF_2', type, '#skF_2': $i).
% 9.96/4.03  tff('#skF_1', type, '#skF_1': $i).
% 9.96/4.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.96/4.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.96/4.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.96/4.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.96/4.03  
% 10.08/4.04  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.08/4.04  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.08/4.04  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.08/4.04  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.08/4.04  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 10.08/4.04  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.08/4.04  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 10.08/4.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.08/4.04  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.08/4.04  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.08/4.04  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.08/4.04  tff(c_66, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.08/4.04  tff(c_104, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k3_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_66])).
% 10.08/4.04  tff(c_117, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_104, c_4])).
% 10.08/4.05  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.08/4.05  tff(c_110, plain, (![A_30]: (k4_xboole_0(A_30, k3_xboole_0(A_30, k1_xboole_0))=k3_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 10.08/4.05  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.08/4.05  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.08/4.05  tff(c_87, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_66])).
% 10.08/4.05  tff(c_431, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k4_xboole_0(A_45, B_46), C_47)=k4_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/4.05  tff(c_482, plain, (![A_3, C_47]: (k4_xboole_0(k3_xboole_0(A_3, k1_xboole_0), C_47)=k4_xboole_0(A_3, k2_xboole_0(A_3, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_431])).
% 10.08/4.05  tff(c_521, plain, (![A_48, C_49]: (k3_xboole_0(A_48, k4_xboole_0(k1_xboole_0, C_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_482])).
% 10.08/4.05  tff(c_535, plain, (![A_48]: (k3_xboole_0(A_48, k3_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_110, c_521])).
% 10.08/4.05  tff(c_554, plain, (![A_48]: (k3_xboole_0(A_48, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_535])).
% 10.08/4.05  tff(c_305, plain, (![A_41, B_42]: (k5_xboole_0(k5_xboole_0(A_41, B_42), k3_xboole_0(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.08/4.05  tff(c_342, plain, (![A_14]: (k5_xboole_0(A_14, k3_xboole_0(A_14, k1_xboole_0))=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_305])).
% 10.08/4.05  tff(c_623, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_342])).
% 10.08/4.05  tff(c_628, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_623])).
% 10.08/4.05  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.08/4.05  tff(c_113, plain, (![A_30]: (k2_xboole_0(A_30, k3_xboole_0(A_30, k1_xboole_0))=k2_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2])).
% 10.08/4.05  tff(c_624, plain, (![A_30]: (k2_xboole_0(A_30, k1_xboole_0)=k2_xboole_0(A_30, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_113])).
% 10.08/4.05  tff(c_926, plain, (![A_30]: (k2_xboole_0(A_30, A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_628, c_624])).
% 10.08/4.05  tff(c_6, plain, (![A_4, B_5, C_6]: (k4_xboole_0(k4_xboole_0(A_4, B_5), C_6)=k4_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/4.05  tff(c_646, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k2_xboole_0(B_53, k1_xboole_0))=k4_xboole_0(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_4, c_431])).
% 10.08/4.05  tff(c_708, plain, (![B_54]: (k4_xboole_0(B_54, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_646, c_8])).
% 10.08/4.05  tff(c_751, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(B_5, k4_xboole_0(A_4, B_5)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_708])).
% 10.08/4.05  tff(c_768, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(B_5, A_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_751])).
% 10.08/4.05  tff(c_6690, plain, (![C_163, A_164, B_165]: (k2_xboole_0(C_163, k4_xboole_0(A_164, k2_xboole_0(B_165, C_163)))=k2_xboole_0(C_163, k4_xboole_0(A_164, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_431, c_2])).
% 10.08/4.05  tff(c_6909, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k2_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_768, c_6690])).
% 10.08/4.05  tff(c_6995, plain, (![A_166, B_167]: (k2_xboole_0(A_166, k4_xboole_0(A_166, B_167))=A_166)), inference(demodulation, [status(thm), theory('equality')], [c_628, c_6909])).
% 10.08/4.05  tff(c_7477, plain, (![A_170, B_171]: (k2_xboole_0(A_170, k3_xboole_0(A_170, B_171))=A_170)), inference(superposition, [status(thm), theory('equality')], [c_10, c_6995])).
% 10.08/4.05  tff(c_868, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(B_59, A_58))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_751])).
% 10.08/4.05  tff(c_1505, plain, (![B_76, A_77]: (k4_xboole_0(k4_xboole_0(B_76, A_77), k2_xboole_0(A_77, B_76))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_868])).
% 10.08/4.05  tff(c_1520, plain, (![B_76, A_77]: (k4_xboole_0(B_76, k2_xboole_0(A_77, k2_xboole_0(A_77, B_76)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1505, c_6])).
% 10.08/4.05  tff(c_7585, plain, (![A_170, B_171]: (k4_xboole_0(k3_xboole_0(A_170, B_171), k2_xboole_0(A_170, A_170))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7477, c_1520])).
% 10.08/4.05  tff(c_7738, plain, (![A_170, B_171]: (k3_xboole_0(A_170, k4_xboole_0(B_171, A_170))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_926, c_7585])).
% 10.08/4.05  tff(c_18, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.08/4.05  tff(c_32371, plain, (![A_348, B_349]: (k5_xboole_0(k2_xboole_0(A_348, B_349), k3_xboole_0(k5_xboole_0(A_348, B_349), k3_xboole_0(A_348, B_349)))=k2_xboole_0(k5_xboole_0(A_348, B_349), k3_xboole_0(A_348, B_349)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_18])).
% 10.08/4.05  tff(c_32611, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)), k3_xboole_0(A_1, k4_xboole_0(B_2, A_1))))=k2_xboole_0(k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)), k3_xboole_0(A_1, k4_xboole_0(B_2, A_1))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32371])).
% 10.08/4.05  tff(c_32680, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_7738, c_14, c_554, c_7738, c_32611])).
% 10.08/4.05  tff(c_20, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.08/4.05  tff(c_32684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32680, c_20])).
% 10.08/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/4.05  
% 10.08/4.05  Inference rules
% 10.08/4.05  ----------------------
% 10.08/4.05  #Ref     : 0
% 10.08/4.05  #Sup     : 8042
% 10.08/4.05  #Fact    : 0
% 10.08/4.05  #Define  : 0
% 10.08/4.05  #Split   : 0
% 10.08/4.05  #Chain   : 0
% 10.08/4.05  #Close   : 0
% 10.08/4.05  
% 10.08/4.05  Ordering : KBO
% 10.08/4.05  
% 10.08/4.05  Simplification rules
% 10.08/4.05  ----------------------
% 10.08/4.05  #Subsume      : 0
% 10.08/4.05  #Demod        : 9730
% 10.08/4.05  #Tautology    : 5918
% 10.08/4.05  #SimpNegUnit  : 0
% 10.08/4.05  #BackRed      : 9
% 10.08/4.05  
% 10.08/4.05  #Partial instantiations: 0
% 10.08/4.05  #Strategies tried      : 1
% 10.08/4.05  
% 10.08/4.05  Timing (in seconds)
% 10.08/4.05  ----------------------
% 10.08/4.05  Preprocessing        : 0.26
% 10.08/4.05  Parsing              : 0.13
% 10.08/4.05  CNF conversion       : 0.01
% 10.08/4.05  Main loop            : 2.96
% 10.08/4.05  Inferencing          : 0.68
% 10.08/4.05  Reduction            : 1.61
% 10.08/4.05  Demodulation         : 1.43
% 10.08/4.05  BG Simplification    : 0.08
% 10.08/4.05  Subsumption          : 0.44
% 10.08/4.05  Abstraction          : 0.16
% 10.08/4.05  MUC search           : 0.00
% 10.08/4.05  Cooper               : 0.00
% 10.08/4.05  Total                : 3.25
% 10.08/4.05  Index Insertion      : 0.00
% 10.08/4.05  Index Deletion       : 0.00
% 10.08/4.05  Index Matching       : 0.00
% 10.08/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------

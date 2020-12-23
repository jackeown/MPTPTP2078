%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 13.75s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 357 expanded)
%              Number of leaves         :   20 ( 129 expanded)
%              Depth                    :   18
%              Number of atoms          :   84 ( 364 expanded)
%              Number of equality atoms :   72 ( 328 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_43,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_131,plain,(
    ! [A_32] : k4_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_127])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),B_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_142,plain,(
    ! [A_32] : k3_xboole_0(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_65])).

tff(c_246,plain,(
    ! [A_38] : k3_xboole_0(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_65])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_255,plain,(
    ! [A_38,C_11] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_38,C_11)) = k4_xboole_0(k1_xboole_0,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_14])).

tff(c_270,plain,(
    ! [C_11] : k4_xboole_0(k1_xboole_0,C_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_255])).

tff(c_455,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k4_xboole_0(A_47,B_48),k3_xboole_0(A_47,C_49)) = k4_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_491,plain,(
    ! [A_6,C_49] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_49)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_455])).

tff(c_505,plain,(
    ! [A_50,C_51] : k2_xboole_0(A_50,k3_xboole_0(A_50,C_51)) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_270,c_491])).

tff(c_526,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_505])).

tff(c_482,plain,(
    ! [A_15,B_16,B_48] : k4_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(B_48,B_16)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(A_15,B_16),B_48),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_455])).

tff(c_32104,plain,(
    ! [A_15,B_16,B_48] : k4_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(B_48,B_16)) = k4_xboole_0(k4_xboole_0(A_15,B_16),B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_482])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = k3_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_12])).

tff(c_224,plain,(
    ! [A_37] : k3_xboole_0(A_37,A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_230,plain,(
    ! [A_37,C_11] : k3_xboole_0(A_37,k4_xboole_0(A_37,C_11)) = k4_xboole_0(A_37,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_14])).

tff(c_106,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_1211,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_106])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_6618,plain,(
    ! [A_150,B_151,C_152] : k4_xboole_0(A_150,k4_xboole_0(k4_xboole_0(A_150,B_151),C_152)) = k2_xboole_0(k3_xboole_0(A_150,B_151),k3_xboole_0(A_150,C_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_455])).

tff(c_51665,plain,(
    ! [A_492,B_493,C_494] : k4_xboole_0(A_492,k2_xboole_0(k3_xboole_0(A_492,B_493),k3_xboole_0(A_492,C_494))) = k3_xboole_0(A_492,k4_xboole_0(k4_xboole_0(A_492,B_493),C_494)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6618,c_12])).

tff(c_52530,plain,(
    ! [B_493] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1',B_493),k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',k2_xboole_0(k3_xboole_0('#skF_1',B_493),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_51665])).

tff(c_53253,plain,(
    ! [B_501] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1',B_501),k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',B_501) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_526,c_52530])).

tff(c_53568,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32104,c_53253])).

tff(c_130,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_127])).

tff(c_157,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_476,plain,(
    ! [A_6,C_49] : k4_xboole_0(A_6,k4_xboole_0(A_6,C_49)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_6,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_455])).

tff(c_649,plain,(
    ! [A_56,C_57] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_56,C_57)) = k3_xboole_0(A_56,C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_476])).

tff(c_672,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = k2_xboole_0(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_649])).

tff(c_688,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_672])).

tff(c_1212,plain,(
    ! [A_69,C_70] : k3_xboole_0(A_69,k4_xboole_0(A_69,C_70)) = k4_xboole_0(A_69,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_14])).

tff(c_372,plain,(
    ! [A_42,B_43] : r1_xboole_0(k3_xboole_0(A_42,B_43),k4_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_406,plain,(
    ! [A_42,B_43] : k3_xboole_0(k3_xboole_0(A_42,B_43),k4_xboole_0(A_42,B_43)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_1228,plain,(
    ! [A_69,C_70] : k3_xboole_0(k4_xboole_0(A_69,C_70),k4_xboole_0(A_69,k4_xboole_0(A_69,C_70))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_406])).

tff(c_1284,plain,(
    ! [A_69,C_70] : k3_xboole_0(k4_xboole_0(A_69,C_70),k3_xboole_0(A_69,C_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1228])).

tff(c_166,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    ! [A_34,B_35,B_8] : k3_xboole_0(A_34,k4_xboole_0(B_35,k4_xboole_0(k3_xboole_0(A_34,B_35),B_8))) = k3_xboole_0(k3_xboole_0(A_34,B_35),B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_4176,plain,(
    ! [A_116,B_117,B_118] : k3_xboole_0(A_116,k4_xboole_0(B_117,k3_xboole_0(A_116,k4_xboole_0(B_117,B_118)))) = k3_xboole_0(k3_xboole_0(A_116,B_117),B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_204])).

tff(c_4377,plain,(
    ! [B_117,B_118] : k3_xboole_0(k4_xboole_0(B_117,B_118),k4_xboole_0(B_117,k4_xboole_0(B_117,B_118))) = k3_xboole_0(k3_xboole_0(k4_xboole_0(B_117,B_118),B_117),B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4176])).

tff(c_4852,plain,(
    ! [B_127,B_128] : k3_xboole_0(k3_xboole_0(k4_xboole_0(B_127,B_128),B_127),B_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_12,c_4377])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2433,plain,(
    ! [A_91,B_92] : k2_xboole_0(k4_xboole_0(A_91,B_92),k3_xboole_0(A_91,B_92)) = k2_xboole_0(k4_xboole_0(A_91,B_92),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)) = k4_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2439,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(B_92,B_92)) = k2_xboole_0(k4_xboole_0(A_91,B_92),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_16])).

tff(c_2523,plain,(
    ! [A_91,B_92] : k2_xboole_0(k4_xboole_0(A_91,B_92),A_91) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_130,c_2439])).

tff(c_112,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,B_31)) = k2_xboole_0(k4_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_2767,plain,(
    ! [A_99,B_100] : k2_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_112])).

tff(c_2843,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k3_xboole_0(A_7,k4_xboole_0(A_7,B_8))) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2767])).

tff(c_2875,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2843])).

tff(c_4900,plain,(
    ! [B_127,B_128] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(k4_xboole_0(B_127,B_128),B_127),B_128)) = k3_xboole_0(k4_xboole_0(B_127,B_128),B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_4852,c_2875])).

tff(c_5280,plain,(
    ! [B_134,B_135] : k3_xboole_0(k4_xboole_0(B_134,B_135),B_134) = k4_xboole_0(B_134,B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_157,c_14,c_4900])).

tff(c_5356,plain,(
    ! [B_134,B_135] : k4_xboole_0(k4_xboole_0(B_134,B_135),k4_xboole_0(B_134,B_135)) = k4_xboole_0(k4_xboole_0(B_134,B_135),B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_5280,c_1211])).

tff(c_5495,plain,(
    ! [B_136,B_137] : k4_xboole_0(k4_xboole_0(B_136,B_137),B_136) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_5356])).

tff(c_5706,plain,(
    ! [A_138,B_139] : k4_xboole_0(k3_xboole_0(A_138,B_139),A_138) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5495])).

tff(c_5905,plain,(
    ! [A_140,B_141] : k3_xboole_0(A_140,k4_xboole_0(B_141,A_140)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5706,c_14])).

tff(c_6079,plain,(
    ! [C_11,A_9,B_10] : k3_xboole_0(C_11,k3_xboole_0(A_9,k4_xboole_0(B_10,C_11))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5905])).

tff(c_56776,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_53568,c_6079])).

tff(c_56966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_56776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.75/7.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.40  
% 13.75/7.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.41  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.75/7.41  
% 13.75/7.41  %Foreground sorts:
% 13.75/7.41  
% 13.75/7.41  
% 13.75/7.41  %Background operators:
% 13.75/7.41  
% 13.75/7.41  
% 13.75/7.41  %Foreground operators:
% 13.75/7.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.75/7.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.75/7.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.75/7.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.75/7.41  tff('#skF_2', type, '#skF_2': $i).
% 13.75/7.41  tff('#skF_3', type, '#skF_3': $i).
% 13.75/7.41  tff('#skF_1', type, '#skF_1': $i).
% 13.75/7.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.75/7.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.75/7.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.75/7.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.75/7.41  
% 13.75/7.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.75/7.42  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 13.75/7.42  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 13.75/7.42  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.75/7.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.75/7.42  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.75/7.42  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.75/7.42  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 13.75/7.42  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.75/7.42  tff(c_43, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.75/7.42  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.75/7.42  tff(c_47, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_43, c_20])).
% 13.75/7.42  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/7.42  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.75/7.42  tff(c_103, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.75/7.42  tff(c_127, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 13.75/7.42  tff(c_131, plain, (![A_32]: (k4_xboole_0(A_32, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_127])).
% 13.75/7.42  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.75/7.42  tff(c_49, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.75/7.42  tff(c_65, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), B_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_49])).
% 13.75/7.42  tff(c_142, plain, (![A_32]: (k3_xboole_0(k1_xboole_0, A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131, c_65])).
% 13.75/7.42  tff(c_246, plain, (![A_38]: (k3_xboole_0(k1_xboole_0, A_38)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131, c_65])).
% 13.75/7.42  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.75/7.42  tff(c_255, plain, (![A_38, C_11]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_38, C_11))=k4_xboole_0(k1_xboole_0, C_11))), inference(superposition, [status(thm), theory('equality')], [c_246, c_14])).
% 13.75/7.42  tff(c_270, plain, (![C_11]: (k4_xboole_0(k1_xboole_0, C_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_255])).
% 13.75/7.42  tff(c_455, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k4_xboole_0(A_47, B_48), k3_xboole_0(A_47, C_49))=k4_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.75/7.42  tff(c_491, plain, (![A_6, C_49]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_49))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_455])).
% 13.75/7.42  tff(c_505, plain, (![A_50, C_51]: (k2_xboole_0(A_50, k3_xboole_0(A_50, C_51))=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_270, c_491])).
% 13.75/7.42  tff(c_526, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_6, c_505])).
% 13.75/7.42  tff(c_482, plain, (![A_15, B_16, B_48]: (k4_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(B_48, B_16))=k2_xboole_0(k4_xboole_0(k4_xboole_0(A_15, B_16), B_48), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_65, c_455])).
% 13.75/7.42  tff(c_32104, plain, (![A_15, B_16, B_48]: (k4_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(B_48, B_16))=k4_xboole_0(k4_xboole_0(A_15, B_16), B_48))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_482])).
% 13.75/7.42  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.75/7.42  tff(c_136, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k3_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_131, c_12])).
% 13.75/7.42  tff(c_224, plain, (![A_37]: (k3_xboole_0(A_37, A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 13.75/7.42  tff(c_230, plain, (![A_37, C_11]: (k3_xboole_0(A_37, k4_xboole_0(A_37, C_11))=k4_xboole_0(A_37, C_11))), inference(superposition, [status(thm), theory('equality')], [c_224, c_14])).
% 13.75/7.42  tff(c_106, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k3_xboole_0(A_30, k4_xboole_0(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_12])).
% 13.75/7.42  tff(c_1211, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_106])).
% 13.75/7.42  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.75/7.42  tff(c_66, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_49])).
% 13.75/7.42  tff(c_6618, plain, (![A_150, B_151, C_152]: (k4_xboole_0(A_150, k4_xboole_0(k4_xboole_0(A_150, B_151), C_152))=k2_xboole_0(k3_xboole_0(A_150, B_151), k3_xboole_0(A_150, C_152)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_455])).
% 13.75/7.42  tff(c_51665, plain, (![A_492, B_493, C_494]: (k4_xboole_0(A_492, k2_xboole_0(k3_xboole_0(A_492, B_493), k3_xboole_0(A_492, C_494)))=k3_xboole_0(A_492, k4_xboole_0(k4_xboole_0(A_492, B_493), C_494)))), inference(superposition, [status(thm), theory('equality')], [c_6618, c_12])).
% 13.75/7.42  tff(c_52530, plain, (![B_493]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', B_493), k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', k2_xboole_0(k3_xboole_0('#skF_1', B_493), k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_51665])).
% 13.75/7.42  tff(c_53253, plain, (![B_501]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', B_501), k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', B_501))), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_526, c_52530])).
% 13.75/7.42  tff(c_53568, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32104, c_53253])).
% 13.75/7.42  tff(c_130, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_127])).
% 13.75/7.42  tff(c_157, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 13.75/7.42  tff(c_476, plain, (![A_6, C_49]: (k4_xboole_0(A_6, k4_xboole_0(A_6, C_49))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_6, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_455])).
% 13.75/7.42  tff(c_649, plain, (![A_56, C_57]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_56, C_57))=k3_xboole_0(A_56, C_57))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_476])).
% 13.75/7.42  tff(c_672, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=k2_xboole_0(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_157, c_649])).
% 13.75/7.42  tff(c_688, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_672])).
% 13.75/7.42  tff(c_1212, plain, (![A_69, C_70]: (k3_xboole_0(A_69, k4_xboole_0(A_69, C_70))=k4_xboole_0(A_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_224, c_14])).
% 13.75/7.42  tff(c_372, plain, (![A_42, B_43]: (r1_xboole_0(k3_xboole_0(A_42, B_43), k4_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_18])).
% 13.75/7.42  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.75/7.42  tff(c_406, plain, (![A_42, B_43]: (k3_xboole_0(k3_xboole_0(A_42, B_43), k4_xboole_0(A_42, B_43))=k1_xboole_0)), inference(resolution, [status(thm)], [c_372, c_2])).
% 13.75/7.42  tff(c_1228, plain, (![A_69, C_70]: (k3_xboole_0(k4_xboole_0(A_69, C_70), k4_xboole_0(A_69, k4_xboole_0(A_69, C_70)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1212, c_406])).
% 13.75/7.42  tff(c_1284, plain, (![A_69, C_70]: (k3_xboole_0(k4_xboole_0(A_69, C_70), k3_xboole_0(A_69, C_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1228])).
% 13.75/7.42  tff(c_166, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k3_xboole_0(A_34, B_35), C_36)=k3_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.75/7.42  tff(c_204, plain, (![A_34, B_35, B_8]: (k3_xboole_0(A_34, k4_xboole_0(B_35, k4_xboole_0(k3_xboole_0(A_34, B_35), B_8)))=k3_xboole_0(k3_xboole_0(A_34, B_35), B_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 13.75/7.42  tff(c_4176, plain, (![A_116, B_117, B_118]: (k3_xboole_0(A_116, k4_xboole_0(B_117, k3_xboole_0(A_116, k4_xboole_0(B_117, B_118))))=k3_xboole_0(k3_xboole_0(A_116, B_117), B_118))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_204])).
% 13.75/7.42  tff(c_4377, plain, (![B_117, B_118]: (k3_xboole_0(k4_xboole_0(B_117, B_118), k4_xboole_0(B_117, k4_xboole_0(B_117, B_118)))=k3_xboole_0(k3_xboole_0(k4_xboole_0(B_117, B_118), B_117), B_118))), inference(superposition, [status(thm), theory('equality')], [c_157, c_4176])).
% 13.75/7.42  tff(c_4852, plain, (![B_127, B_128]: (k3_xboole_0(k3_xboole_0(k4_xboole_0(B_127, B_128), B_127), B_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_12, c_4377])).
% 13.75/7.42  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.75/7.42  tff(c_2433, plain, (![A_91, B_92]: (k2_xboole_0(k4_xboole_0(A_91, B_92), k3_xboole_0(A_91, B_92))=k2_xboole_0(k4_xboole_0(A_91, B_92), A_91))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8])).
% 13.75/7.42  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14))=k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.75/7.42  tff(c_2439, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(B_92, B_92))=k2_xboole_0(k4_xboole_0(A_91, B_92), A_91))), inference(superposition, [status(thm), theory('equality')], [c_2433, c_16])).
% 13.75/7.42  tff(c_2523, plain, (![A_91, B_92]: (k2_xboole_0(k4_xboole_0(A_91, B_92), A_91)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_130, c_2439])).
% 13.75/7.42  tff(c_112, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, B_31))=k2_xboole_0(k4_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8])).
% 13.75/7.42  tff(c_2767, plain, (![A_99, B_100]: (k2_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_112])).
% 13.75/7.42  tff(c_2843, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2767])).
% 13.75/7.42  tff(c_2875, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_2843])).
% 13.75/7.42  tff(c_4900, plain, (![B_127, B_128]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k3_xboole_0(k4_xboole_0(B_127, B_128), B_127), B_128))=k3_xboole_0(k4_xboole_0(B_127, B_128), B_127))), inference(superposition, [status(thm), theory('equality')], [c_4852, c_2875])).
% 13.75/7.42  tff(c_5280, plain, (![B_134, B_135]: (k3_xboole_0(k4_xboole_0(B_134, B_135), B_134)=k4_xboole_0(B_134, B_135))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_157, c_14, c_4900])).
% 13.75/7.42  tff(c_5356, plain, (![B_134, B_135]: (k4_xboole_0(k4_xboole_0(B_134, B_135), k4_xboole_0(B_134, B_135))=k4_xboole_0(k4_xboole_0(B_134, B_135), B_134))), inference(superposition, [status(thm), theory('equality')], [c_5280, c_1211])).
% 13.75/7.42  tff(c_5495, plain, (![B_136, B_137]: (k4_xboole_0(k4_xboole_0(B_136, B_137), B_136)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_5356])).
% 13.75/7.42  tff(c_5706, plain, (![A_138, B_139]: (k4_xboole_0(k3_xboole_0(A_138, B_139), A_138)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_5495])).
% 13.75/7.42  tff(c_5905, plain, (![A_140, B_141]: (k3_xboole_0(A_140, k4_xboole_0(B_141, A_140))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5706, c_14])).
% 13.75/7.42  tff(c_6079, plain, (![C_11, A_9, B_10]: (k3_xboole_0(C_11, k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_5905])).
% 13.75/7.42  tff(c_56776, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_53568, c_6079])).
% 13.75/7.42  tff(c_56966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_56776])).
% 13.75/7.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.42  
% 13.75/7.42  Inference rules
% 13.75/7.42  ----------------------
% 13.75/7.42  #Ref     : 0
% 13.75/7.42  #Sup     : 14212
% 13.75/7.42  #Fact    : 0
% 13.75/7.42  #Define  : 0
% 13.75/7.42  #Split   : 0
% 13.75/7.42  #Chain   : 0
% 13.75/7.42  #Close   : 0
% 13.75/7.42  
% 13.75/7.42  Ordering : KBO
% 13.75/7.42  
% 13.75/7.42  Simplification rules
% 13.75/7.42  ----------------------
% 13.75/7.42  #Subsume      : 0
% 13.75/7.42  #Demod        : 18180
% 13.75/7.42  #Tautology    : 10522
% 13.75/7.42  #SimpNegUnit  : 1
% 13.75/7.43  #BackRed      : 8
% 13.75/7.43  
% 13.75/7.43  #Partial instantiations: 0
% 13.75/7.43  #Strategies tried      : 1
% 13.75/7.43  
% 13.75/7.43  Timing (in seconds)
% 13.75/7.43  ----------------------
% 13.92/7.43  Preprocessing        : 0.27
% 13.92/7.43  Parsing              : 0.15
% 13.92/7.43  CNF conversion       : 0.02
% 13.92/7.43  Main loop            : 6.38
% 13.92/7.43  Inferencing          : 0.96
% 13.92/7.43  Reduction            : 3.96
% 13.92/7.43  Demodulation         : 3.60
% 13.92/7.43  BG Simplification    : 0.11
% 13.92/7.43  Subsumption          : 1.09
% 13.92/7.43  Abstraction          : 0.20
% 13.92/7.43  MUC search           : 0.00
% 13.92/7.43  Cooper               : 0.00
% 13.92/7.43  Total                : 6.69
% 13.92/7.43  Index Insertion      : 0.00
% 13.92/7.43  Index Deletion       : 0.00
% 13.92/7.43  Index Matching       : 0.00
% 13.92/7.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

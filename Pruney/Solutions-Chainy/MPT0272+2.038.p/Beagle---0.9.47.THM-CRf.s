%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 27.68s
% Output     : CNFRefutation 27.89s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 891 expanded)
%              Number of leaves         :   28 ( 310 expanded)
%              Depth                    :   18
%              Number of atoms          :  157 ( 946 expanded)
%              Number of equality atoms :  149 ( 925 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_167,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_167])).

tff(c_1306,plain,(
    ! [A_96,B_97] : k3_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_176])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1341,plain,(
    ! [A_96,B_97] : k2_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = A_96 ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_10])).

tff(c_136,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1471,plain,(
    ! [A_100,B_101] :
      ( k2_xboole_0(A_100,B_101) = B_101
      | k4_xboole_0(A_100,B_101) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_1489,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17)
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1471])).

tff(c_1934,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = A_112
      | k3_xboole_0(A_112,B_113) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1489])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_194,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_203,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_194])).

tff(c_244,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_244])).

tff(c_260,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_256])).

tff(c_428,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_xboole_0(A_69,B_70),k4_xboole_0(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_750,plain,(
    ! [A_79,B_80] : k4_xboole_0(k3_xboole_0(A_79,B_80),A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_16])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_805,plain,(
    ! [A_81,B_82] : k3_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_22])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_822,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = k5_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_6])).

tff(c_862,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_822])).

tff(c_6697,plain,(
    ! [B_176,A_177] :
      ( k4_xboole_0(B_176,A_177) = B_176
      | k3_xboole_0(A_177,B_176) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1934,c_862])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7001,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6697,c_38])).

tff(c_24,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_188,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_167])).

tff(c_201,plain,(
    ! [A_37] : k3_xboole_0(A_37,A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_253,plain,(
    ! [A_37] : k5_xboole_0(A_37,A_37) = k4_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_244])).

tff(c_259,plain,(
    ! [A_37] : k5_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_253])).

tff(c_470,plain,(
    ! [A_11] : k2_xboole_0(k3_xboole_0(A_11,k1_xboole_0),A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_428])).

tff(c_480,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_470])).

tff(c_956,plain,(
    ! [A_85,B_86,C_87] : k2_xboole_0(k4_xboole_0(A_85,B_86),k3_xboole_0(A_85,C_87)) = k4_xboole_0(A_85,k4_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1007,plain,(
    ! [A_12,B_13,C_87] : k4_xboole_0(A_12,k4_xboole_0(k2_xboole_0(A_12,B_13),C_87)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_12,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_956])).

tff(c_7029,plain,(
    ! [A_178,B_179,C_180] : k4_xboole_0(A_178,k4_xboole_0(k2_xboole_0(A_178,B_179),C_180)) = k3_xboole_0(A_178,C_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1007])).

tff(c_7273,plain,(
    ! [A_178,B_179,B_13] : k3_xboole_0(A_178,k2_xboole_0(k2_xboole_0(A_178,B_179),B_13)) = k4_xboole_0(A_178,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7029])).

tff(c_7319,plain,(
    ! [A_181,B_182,B_183] : k3_xboole_0(A_181,k2_xboole_0(k2_xboole_0(A_181,B_182),B_183)) = A_181 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7273])).

tff(c_7387,plain,(
    ! [A_181,B_182,B_183] : k4_xboole_0(A_181,k2_xboole_0(k2_xboole_0(A_181,B_182),B_183)) = k5_xboole_0(A_181,A_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_7319,c_6])).

tff(c_7468,plain,(
    ! [A_181,B_182,B_183] : k4_xboole_0(A_181,k2_xboole_0(k2_xboole_0(A_181,B_182),B_183)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_7387])).

tff(c_191,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_202,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_191])).

tff(c_1508,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1489])).

tff(c_668,plain,(
    ! [A_76,B_77,C_78] : k4_xboole_0(k3_xboole_0(A_76,B_77),C_78) = k3_xboole_0(A_76,k4_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15457,plain,(
    ! [A_255,B_256,C_257] : k3_xboole_0(A_255,k4_xboole_0(k2_xboole_0(A_255,B_256),C_257)) = k4_xboole_0(A_255,C_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_668])).

tff(c_15723,plain,(
    ! [A_255,B_17,B_256] :
      ( k4_xboole_0(A_255,B_17) = k3_xboole_0(A_255,k2_xboole_0(A_255,B_256))
      | k3_xboole_0(k2_xboole_0(A_255,B_256),B_17) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_15457])).

tff(c_31970,plain,(
    ! [A_364,B_365,B_366] :
      ( k4_xboole_0(A_364,B_365) = A_364
      | k3_xboole_0(k2_xboole_0(A_364,B_366),B_365) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_15723])).

tff(c_32113,plain,(
    ! [A_364,B_366,B_13] :
      ( k4_xboole_0(A_364,k2_xboole_0(k2_xboole_0(A_364,B_366),B_13)) = A_364
      | k2_xboole_0(A_364,B_366) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_31970])).

tff(c_32155,plain,(
    ! [A_367,B_368] :
      ( k1_xboole_0 = A_367
      | k2_xboole_0(A_367,B_368) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7468,c_32113])).

tff(c_32665,plain,(
    ! [A_371,B_372] :
      ( k3_xboole_0(A_371,B_372) = k1_xboole_0
      | k1_xboole_0 != A_371 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_32155])).

tff(c_1023,plain,(
    ! [A_12,B_13,C_87] : k4_xboole_0(A_12,k4_xboole_0(k2_xboole_0(A_12,B_13),C_87)) = k3_xboole_0(A_12,C_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1007])).

tff(c_980,plain,(
    ! [A_18,B_19,C_20,C_87] : k2_xboole_0(k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)),k3_xboole_0(k3_xboole_0(A_18,B_19),C_87)) = k4_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(C_20,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_956])).

tff(c_20412,plain,(
    ! [A_291,B_292,C_293,C_294] : k2_xboole_0(k3_xboole_0(A_291,k4_xboole_0(B_292,C_293)),k3_xboole_0(k3_xboole_0(A_291,B_292),C_294)) = k3_xboole_0(A_291,k4_xboole_0(B_292,k4_xboole_0(C_293,C_294))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_980])).

tff(c_20833,plain,(
    ! [A_291,A_12,B_13,C_294] : k3_xboole_0(A_291,k4_xboole_0(A_12,k4_xboole_0(k2_xboole_0(A_12,B_13),C_294))) = k2_xboole_0(k3_xboole_0(A_291,k1_xboole_0),k3_xboole_0(k3_xboole_0(A_291,A_12),C_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_20412])).

tff(c_21288,plain,(
    ! [A_298,A_299,C_300] : k3_xboole_0(k3_xboole_0(A_298,A_299),C_300) = k3_xboole_0(A_298,k3_xboole_0(A_299,C_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_480,c_203,c_20833])).

tff(c_767,plain,(
    ! [A_79,B_80] : k4_xboole_0(k3_xboole_0(A_79,B_80),k1_xboole_0) = k3_xboole_0(k3_xboole_0(A_79,B_80),A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_20])).

tff(c_797,plain,(
    ! [A_79,B_80] : k3_xboole_0(k3_xboole_0(A_79,B_80),A_79) = k3_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_767])).

tff(c_21733,plain,(
    ! [C_301,A_302] : k3_xboole_0(C_301,k3_xboole_0(A_302,C_301)) = k3_xboole_0(C_301,A_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_21288,c_797])).

tff(c_21878,plain,(
    ! [C_301,A_302] : k5_xboole_0(C_301,k3_xboole_0(C_301,A_302)) = k4_xboole_0(C_301,k3_xboole_0(A_302,C_301)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21733,c_6])).

tff(c_22043,plain,(
    ! [C_301,A_302] : k4_xboole_0(C_301,k3_xboole_0(A_302,C_301)) = k4_xboole_0(C_301,A_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21878])).

tff(c_32789,plain,(
    ! [B_372,A_371] :
      ( k4_xboole_0(B_372,k1_xboole_0) = k4_xboole_0(B_372,A_371)
      | k1_xboole_0 != A_371 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32665,c_22043])).

tff(c_36801,plain,(
    ! [B_372] : k4_xboole_0(B_372,k1_xboole_0) = B_372 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_32789])).

tff(c_992,plain,(
    ! [A_37,B_86] : k4_xboole_0(A_37,k4_xboole_0(B_86,A_37)) = k2_xboole_0(k4_xboole_0(A_37,B_86),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_956])).

tff(c_1019,plain,(
    ! [A_37,B_86] : k2_xboole_0(k4_xboole_0(A_37,B_86),A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_992])).

tff(c_32215,plain,(
    ! [A_37,B_86] :
      ( k4_xboole_0(A_37,B_86) = k1_xboole_0
      | k1_xboole_0 != A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_32155])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,C_25)) = k4_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k3_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_167])).

tff(c_1514,plain,(
    ! [A_102,B_103] : k3_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_182])).

tff(c_1526,plain,(
    ! [A_102,B_24,B_103] : k4_xboole_0(A_102,k4_xboole_0(B_24,k3_xboole_0(A_102,B_103))) = k2_xboole_0(k4_xboole_0(A_102,B_24),k3_xboole_0(A_102,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_26])).

tff(c_38249,plain,(
    ! [A_398,B_399,B_400] : k4_xboole_0(A_398,k4_xboole_0(B_399,k3_xboole_0(A_398,B_400))) = k4_xboole_0(A_398,k4_xboole_0(B_399,B_400)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1526])).

tff(c_38517,plain,(
    ! [A_398,A_37,B_400] :
      ( k4_xboole_0(A_398,k4_xboole_0(A_37,B_400)) = k4_xboole_0(A_398,k1_xboole_0)
      | k1_xboole_0 != A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32215,c_38249])).

tff(c_42297,plain,(
    ! [A_438,A_439,B_440] :
      ( k4_xboole_0(A_438,k4_xboole_0(A_439,B_440)) = A_438
      | k1_xboole_0 != A_439 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36801,c_38517])).

tff(c_1027,plain,(
    ! [A_88,B_89] : k2_xboole_0(k4_xboole_0(A_88,B_89),A_88) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_992])).

tff(c_1040,plain,(
    ! [A_88,B_89] : k4_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_16])).

tff(c_47979,plain,(
    ! [A_465,B_466,B_467] :
      ( k4_xboole_0(k4_xboole_0(A_465,B_466),B_467) = k1_xboole_0
      | k1_xboole_0 != A_465 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42297,c_1040])).

tff(c_33410,plain,(
    ! [A_375,B_376] :
      ( k4_xboole_0(A_375,B_376) = k1_xboole_0
      | k1_xboole_0 != A_375 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_32155])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | k4_xboole_0(B_10,A_9) != k4_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33741,plain,(
    ! [B_376,A_375] :
      ( B_376 = A_375
      | k4_xboole_0(B_376,A_375) != k1_xboole_0
      | k1_xboole_0 != A_375 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33410,c_12])).

tff(c_70433,plain,(
    ! [B_466] : k4_xboole_0(k1_xboole_0,B_466) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47979,c_33741])).

tff(c_755,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_22])).

tff(c_21438,plain,(
    ! [C_300,A_299] : k3_xboole_0(C_300,k3_xboole_0(A_299,C_300)) = k3_xboole_0(C_300,A_299) ),
    inference(superposition,[status(thm),theory(equality)],[c_21288,c_797])).

tff(c_22595,plain,(
    ! [C_306,A_307] : k4_xboole_0(C_306,k3_xboole_0(A_307,C_306)) = k4_xboole_0(C_306,A_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21878])).

tff(c_22797,plain,(
    ! [A_299,C_300] : k4_xboole_0(k3_xboole_0(A_299,C_300),k3_xboole_0(C_300,A_299)) = k4_xboole_0(k3_xboole_0(A_299,C_300),C_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_21438,c_22595])).

tff(c_23367,plain,(
    ! [A_312,C_313] : k4_xboole_0(k3_xboole_0(A_312,C_313),k3_xboole_0(C_313,A_312)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_74,c_22,c_22797])).

tff(c_677,plain,(
    ! [A_76,B_77,C_78] :
      ( k3_xboole_0(A_76,B_77) = C_78
      | k4_xboole_0(C_78,k3_xboole_0(A_76,B_77)) != k3_xboole_0(A_76,k4_xboole_0(B_77,C_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_12])).

tff(c_23393,plain,(
    ! [C_313,A_312] :
      ( k3_xboole_0(C_313,A_312) = k3_xboole_0(A_312,C_313)
      | k3_xboole_0(C_313,k4_xboole_0(A_312,k3_xboole_0(A_312,C_313))) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23367,c_677])).

tff(c_23736,plain,(
    ! [C_313,A_312] : k3_xboole_0(C_313,A_312) = k3_xboole_0(A_312,C_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_18,c_23393])).

tff(c_437,plain,(
    ! [A_69,B_70] : k4_xboole_0(k3_xboole_0(A_69,B_70),A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_579,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5414,plain,(
    ! [B_162,A_163] :
      ( k1_tarski(B_162) = A_163
      | k1_xboole_0 = A_163
      | k4_xboole_0(A_163,k1_tarski(B_162)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_579])).

tff(c_32239,plain,(
    ! [B_369,B_370] :
      ( k3_xboole_0(k1_tarski(B_369),B_370) = k1_tarski(B_369)
      | k3_xboole_0(k1_tarski(B_369),B_370) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_5414])).

tff(c_32496,plain,(
    ! [B_369,B_370] :
      ( k5_xboole_0(k1_tarski(B_369),k1_tarski(B_369)) = k4_xboole_0(k1_tarski(B_369),B_370)
      | k3_xboole_0(k1_tarski(B_369),B_370) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32239,c_6])).

tff(c_117147,plain,(
    ! [B_727,B_728] :
      ( k4_xboole_0(k1_tarski(B_727),B_728) = k1_xboole_0
      | k3_xboole_0(k1_tarski(B_727),B_728) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_32496])).

tff(c_40,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_118076,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_117147,c_40])).

tff(c_873,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_822])).

tff(c_933,plain,(
    ! [A_14,B_15] : k4_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_873])).

tff(c_118204,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski('#skF_1'),'#skF_2')) = k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118076,c_933])).

tff(c_118483,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70433,c_23736,c_118204])).

tff(c_118485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7001,c_118483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.68/19.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.68/19.36  
% 27.68/19.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.68/19.36  %$ r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 27.68/19.36  
% 27.68/19.36  %Foreground sorts:
% 27.68/19.36  
% 27.68/19.36  
% 27.68/19.36  %Background operators:
% 27.68/19.36  
% 27.68/19.36  
% 27.68/19.36  %Foreground operators:
% 27.68/19.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.68/19.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.68/19.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.68/19.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.68/19.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 27.68/19.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.68/19.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.68/19.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.68/19.36  tff('#skF_2', type, '#skF_2': $i).
% 27.68/19.36  tff('#skF_1', type, '#skF_1': $i).
% 27.68/19.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.68/19.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.68/19.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.68/19.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.68/19.36  
% 27.89/19.39  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 27.89/19.39  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.89/19.39  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 27.89/19.39  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 27.89/19.39  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.89/19.39  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 27.89/19.39  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 27.89/19.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 27.89/19.39  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 27.89/19.39  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 27.89/19.39  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 27.89/19.39  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 27.89/19.39  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 27.89/19.39  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 27.89/19.39  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.89/19.39  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.89/19.39  tff(c_167, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.89/19.39  tff(c_176, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_167])).
% 27.89/19.39  tff(c_1306, plain, (![A_96, B_97]: (k3_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_176])).
% 27.89/19.39  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.89/19.39  tff(c_1341, plain, (![A_96, B_97]: (k2_xboole_0(A_96, k4_xboole_0(A_96, B_97))=A_96)), inference(superposition, [status(thm), theory('equality')], [c_1306, c_10])).
% 27.89/19.39  tff(c_136, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | k4_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.89/19.39  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.89/19.39  tff(c_1471, plain, (![A_100, B_101]: (k2_xboole_0(A_100, B_101)=B_101 | k4_xboole_0(A_100, B_101)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_8])).
% 27.89/19.39  tff(c_1489, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17) | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1471])).
% 27.89/19.39  tff(c_1934, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=A_112 | k3_xboole_0(A_112, B_113)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1489])).
% 27.89/19.39  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.89/19.39  tff(c_68, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k3_xboole_0(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.89/19.39  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.89/19.39  tff(c_74, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_16])).
% 27.89/19.39  tff(c_194, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_167])).
% 27.89/19.39  tff(c_203, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_194])).
% 27.89/19.39  tff(c_244, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.89/19.39  tff(c_256, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_244])).
% 27.89/19.39  tff(c_260, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_256])).
% 27.89/19.39  tff(c_428, plain, (![A_69, B_70]: (k2_xboole_0(k3_xboole_0(A_69, B_70), k4_xboole_0(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.89/19.39  tff(c_750, plain, (![A_79, B_80]: (k4_xboole_0(k3_xboole_0(A_79, B_80), A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_428, c_16])).
% 27.89/19.39  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.89/19.39  tff(c_805, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k4_xboole_0(B_82, A_81))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_750, c_22])).
% 27.89/19.39  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.89/19.39  tff(c_822, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(B_82, A_81))=k5_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_805, c_6])).
% 27.89/19.39  tff(c_862, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(B_82, A_81))=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_260, c_822])).
% 27.89/19.39  tff(c_6697, plain, (![B_176, A_177]: (k4_xboole_0(B_176, A_177)=B_176 | k3_xboole_0(A_177, B_176)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1934, c_862])).
% 27.89/19.39  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.89/19.39  tff(c_7001, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6697, c_38])).
% 27.89/19.39  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.89/19.39  tff(c_188, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_74, c_167])).
% 27.89/19.39  tff(c_201, plain, (![A_37]: (k3_xboole_0(A_37, A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 27.89/19.39  tff(c_253, plain, (![A_37]: (k5_xboole_0(A_37, A_37)=k4_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_201, c_244])).
% 27.89/19.39  tff(c_259, plain, (![A_37]: (k5_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_253])).
% 27.89/19.39  tff(c_470, plain, (![A_11]: (k2_xboole_0(k3_xboole_0(A_11, k1_xboole_0), A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_428])).
% 27.89/19.39  tff(c_480, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_470])).
% 27.89/19.39  tff(c_956, plain, (![A_85, B_86, C_87]: (k2_xboole_0(k4_xboole_0(A_85, B_86), k3_xboole_0(A_85, C_87))=k4_xboole_0(A_85, k4_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.89/19.39  tff(c_1007, plain, (![A_12, B_13, C_87]: (k4_xboole_0(A_12, k4_xboole_0(k2_xboole_0(A_12, B_13), C_87))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_12, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_956])).
% 27.89/19.39  tff(c_7029, plain, (![A_178, B_179, C_180]: (k4_xboole_0(A_178, k4_xboole_0(k2_xboole_0(A_178, B_179), C_180))=k3_xboole_0(A_178, C_180))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1007])).
% 27.89/19.39  tff(c_7273, plain, (![A_178, B_179, B_13]: (k3_xboole_0(A_178, k2_xboole_0(k2_xboole_0(A_178, B_179), B_13))=k4_xboole_0(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7029])).
% 27.89/19.39  tff(c_7319, plain, (![A_181, B_182, B_183]: (k3_xboole_0(A_181, k2_xboole_0(k2_xboole_0(A_181, B_182), B_183))=A_181)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7273])).
% 27.89/19.39  tff(c_7387, plain, (![A_181, B_182, B_183]: (k4_xboole_0(A_181, k2_xboole_0(k2_xboole_0(A_181, B_182), B_183))=k5_xboole_0(A_181, A_181))), inference(superposition, [status(thm), theory('equality')], [c_7319, c_6])).
% 27.89/19.39  tff(c_7468, plain, (![A_181, B_182, B_183]: (k4_xboole_0(A_181, k2_xboole_0(k2_xboole_0(A_181, B_182), B_183))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_7387])).
% 27.89/19.39  tff(c_191, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_167])).
% 27.89/19.39  tff(c_202, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_191])).
% 27.89/19.39  tff(c_1508, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1489])).
% 27.89/19.39  tff(c_668, plain, (![A_76, B_77, C_78]: (k4_xboole_0(k3_xboole_0(A_76, B_77), C_78)=k3_xboole_0(A_76, k4_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.89/19.39  tff(c_15457, plain, (![A_255, B_256, C_257]: (k3_xboole_0(A_255, k4_xboole_0(k2_xboole_0(A_255, B_256), C_257))=k4_xboole_0(A_255, C_257))), inference(superposition, [status(thm), theory('equality')], [c_202, c_668])).
% 27.89/19.39  tff(c_15723, plain, (![A_255, B_17, B_256]: (k4_xboole_0(A_255, B_17)=k3_xboole_0(A_255, k2_xboole_0(A_255, B_256)) | k3_xboole_0(k2_xboole_0(A_255, B_256), B_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1508, c_15457])).
% 27.89/19.39  tff(c_31970, plain, (![A_364, B_365, B_366]: (k4_xboole_0(A_364, B_365)=A_364 | k3_xboole_0(k2_xboole_0(A_364, B_366), B_365)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_15723])).
% 27.89/19.39  tff(c_32113, plain, (![A_364, B_366, B_13]: (k4_xboole_0(A_364, k2_xboole_0(k2_xboole_0(A_364, B_366), B_13))=A_364 | k2_xboole_0(A_364, B_366)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_31970])).
% 27.89/19.39  tff(c_32155, plain, (![A_367, B_368]: (k1_xboole_0=A_367 | k2_xboole_0(A_367, B_368)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7468, c_32113])).
% 27.89/19.39  tff(c_32665, plain, (![A_371, B_372]: (k3_xboole_0(A_371, B_372)=k1_xboole_0 | k1_xboole_0!=A_371)), inference(superposition, [status(thm), theory('equality')], [c_24, c_32155])).
% 27.89/19.39  tff(c_1023, plain, (![A_12, B_13, C_87]: (k4_xboole_0(A_12, k4_xboole_0(k2_xboole_0(A_12, B_13), C_87))=k3_xboole_0(A_12, C_87))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1007])).
% 27.89/19.39  tff(c_980, plain, (![A_18, B_19, C_20, C_87]: (k2_xboole_0(k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)), k3_xboole_0(k3_xboole_0(A_18, B_19), C_87))=k4_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(C_20, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_956])).
% 27.89/19.39  tff(c_20412, plain, (![A_291, B_292, C_293, C_294]: (k2_xboole_0(k3_xboole_0(A_291, k4_xboole_0(B_292, C_293)), k3_xboole_0(k3_xboole_0(A_291, B_292), C_294))=k3_xboole_0(A_291, k4_xboole_0(B_292, k4_xboole_0(C_293, C_294))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_980])).
% 27.89/19.39  tff(c_20833, plain, (![A_291, A_12, B_13, C_294]: (k3_xboole_0(A_291, k4_xboole_0(A_12, k4_xboole_0(k2_xboole_0(A_12, B_13), C_294)))=k2_xboole_0(k3_xboole_0(A_291, k1_xboole_0), k3_xboole_0(k3_xboole_0(A_291, A_12), C_294)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_20412])).
% 27.89/19.39  tff(c_21288, plain, (![A_298, A_299, C_300]: (k3_xboole_0(k3_xboole_0(A_298, A_299), C_300)=k3_xboole_0(A_298, k3_xboole_0(A_299, C_300)))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_480, c_203, c_20833])).
% 27.89/19.39  tff(c_767, plain, (![A_79, B_80]: (k4_xboole_0(k3_xboole_0(A_79, B_80), k1_xboole_0)=k3_xboole_0(k3_xboole_0(A_79, B_80), A_79))), inference(superposition, [status(thm), theory('equality')], [c_750, c_20])).
% 27.89/19.39  tff(c_797, plain, (![A_79, B_80]: (k3_xboole_0(k3_xboole_0(A_79, B_80), A_79)=k3_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_767])).
% 27.89/19.39  tff(c_21733, plain, (![C_301, A_302]: (k3_xboole_0(C_301, k3_xboole_0(A_302, C_301))=k3_xboole_0(C_301, A_302))), inference(superposition, [status(thm), theory('equality')], [c_21288, c_797])).
% 27.89/19.39  tff(c_21878, plain, (![C_301, A_302]: (k5_xboole_0(C_301, k3_xboole_0(C_301, A_302))=k4_xboole_0(C_301, k3_xboole_0(A_302, C_301)))), inference(superposition, [status(thm), theory('equality')], [c_21733, c_6])).
% 27.89/19.39  tff(c_22043, plain, (![C_301, A_302]: (k4_xboole_0(C_301, k3_xboole_0(A_302, C_301))=k4_xboole_0(C_301, A_302))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_21878])).
% 27.89/19.39  tff(c_32789, plain, (![B_372, A_371]: (k4_xboole_0(B_372, k1_xboole_0)=k4_xboole_0(B_372, A_371) | k1_xboole_0!=A_371)), inference(superposition, [status(thm), theory('equality')], [c_32665, c_22043])).
% 27.89/19.39  tff(c_36801, plain, (![B_372]: (k4_xboole_0(B_372, k1_xboole_0)=B_372)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_32789])).
% 27.89/19.39  tff(c_992, plain, (![A_37, B_86]: (k4_xboole_0(A_37, k4_xboole_0(B_86, A_37))=k2_xboole_0(k4_xboole_0(A_37, B_86), A_37))), inference(superposition, [status(thm), theory('equality')], [c_201, c_956])).
% 27.89/19.39  tff(c_1019, plain, (![A_37, B_86]: (k2_xboole_0(k4_xboole_0(A_37, B_86), A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_862, c_992])).
% 27.89/19.39  tff(c_32215, plain, (![A_37, B_86]: (k4_xboole_0(A_37, B_86)=k1_xboole_0 | k1_xboole_0!=A_37)), inference(superposition, [status(thm), theory('equality')], [c_1019, c_32155])).
% 27.89/19.39  tff(c_26, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, C_25))=k4_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.89/19.39  tff(c_182, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_167])).
% 27.89/19.39  tff(c_1514, plain, (![A_102, B_103]: (k3_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_182])).
% 27.89/19.39  tff(c_1526, plain, (![A_102, B_24, B_103]: (k4_xboole_0(A_102, k4_xboole_0(B_24, k3_xboole_0(A_102, B_103)))=k2_xboole_0(k4_xboole_0(A_102, B_24), k3_xboole_0(A_102, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_1514, c_26])).
% 27.89/19.39  tff(c_38249, plain, (![A_398, B_399, B_400]: (k4_xboole_0(A_398, k4_xboole_0(B_399, k3_xboole_0(A_398, B_400)))=k4_xboole_0(A_398, k4_xboole_0(B_399, B_400)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1526])).
% 27.89/19.39  tff(c_38517, plain, (![A_398, A_37, B_400]: (k4_xboole_0(A_398, k4_xboole_0(A_37, B_400))=k4_xboole_0(A_398, k1_xboole_0) | k1_xboole_0!=A_37)), inference(superposition, [status(thm), theory('equality')], [c_32215, c_38249])).
% 27.89/19.39  tff(c_42297, plain, (![A_438, A_439, B_440]: (k4_xboole_0(A_438, k4_xboole_0(A_439, B_440))=A_438 | k1_xboole_0!=A_439)), inference(demodulation, [status(thm), theory('equality')], [c_36801, c_38517])).
% 27.89/19.39  tff(c_1027, plain, (![A_88, B_89]: (k2_xboole_0(k4_xboole_0(A_88, B_89), A_88)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_862, c_992])).
% 27.89/19.39  tff(c_1040, plain, (![A_88, B_89]: (k4_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1027, c_16])).
% 27.89/19.39  tff(c_47979, plain, (![A_465, B_466, B_467]: (k4_xboole_0(k4_xboole_0(A_465, B_466), B_467)=k1_xboole_0 | k1_xboole_0!=A_465)), inference(superposition, [status(thm), theory('equality')], [c_42297, c_1040])).
% 27.89/19.39  tff(c_33410, plain, (![A_375, B_376]: (k4_xboole_0(A_375, B_376)=k1_xboole_0 | k1_xboole_0!=A_375)), inference(superposition, [status(thm), theory('equality')], [c_1019, c_32155])).
% 27.89/19.39  tff(c_12, plain, (![B_10, A_9]: (B_10=A_9 | k4_xboole_0(B_10, A_9)!=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.89/19.39  tff(c_33741, plain, (![B_376, A_375]: (B_376=A_375 | k4_xboole_0(B_376, A_375)!=k1_xboole_0 | k1_xboole_0!=A_375)), inference(superposition, [status(thm), theory('equality')], [c_33410, c_12])).
% 27.89/19.39  tff(c_70433, plain, (![B_466]: (k4_xboole_0(k1_xboole_0, B_466)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47979, c_33741])).
% 27.89/19.39  tff(c_755, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_750, c_22])).
% 27.89/19.39  tff(c_21438, plain, (![C_300, A_299]: (k3_xboole_0(C_300, k3_xboole_0(A_299, C_300))=k3_xboole_0(C_300, A_299))), inference(superposition, [status(thm), theory('equality')], [c_21288, c_797])).
% 27.89/19.39  tff(c_22595, plain, (![C_306, A_307]: (k4_xboole_0(C_306, k3_xboole_0(A_307, C_306))=k4_xboole_0(C_306, A_307))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_21878])).
% 27.89/19.39  tff(c_22797, plain, (![A_299, C_300]: (k4_xboole_0(k3_xboole_0(A_299, C_300), k3_xboole_0(C_300, A_299))=k4_xboole_0(k3_xboole_0(A_299, C_300), C_300))), inference(superposition, [status(thm), theory('equality')], [c_21438, c_22595])).
% 27.89/19.39  tff(c_23367, plain, (![A_312, C_313]: (k4_xboole_0(k3_xboole_0(A_312, C_313), k3_xboole_0(C_313, A_312))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_74, c_22, c_22797])).
% 27.89/19.39  tff(c_677, plain, (![A_76, B_77, C_78]: (k3_xboole_0(A_76, B_77)=C_78 | k4_xboole_0(C_78, k3_xboole_0(A_76, B_77))!=k3_xboole_0(A_76, k4_xboole_0(B_77, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_668, c_12])).
% 27.89/19.39  tff(c_23393, plain, (![C_313, A_312]: (k3_xboole_0(C_313, A_312)=k3_xboole_0(A_312, C_313) | k3_xboole_0(C_313, k4_xboole_0(A_312, k3_xboole_0(A_312, C_313)))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23367, c_677])).
% 27.89/19.39  tff(c_23736, plain, (![C_313, A_312]: (k3_xboole_0(C_313, A_312)=k3_xboole_0(A_312, C_313))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_18, c_23393])).
% 27.89/19.39  tff(c_437, plain, (![A_69, B_70]: (k4_xboole_0(k3_xboole_0(A_69, B_70), A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_428, c_16])).
% 27.89/19.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.89/19.39  tff(c_579, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.89/19.39  tff(c_5414, plain, (![B_162, A_163]: (k1_tarski(B_162)=A_163 | k1_xboole_0=A_163 | k4_xboole_0(A_163, k1_tarski(B_162))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_579])).
% 27.89/19.39  tff(c_32239, plain, (![B_369, B_370]: (k3_xboole_0(k1_tarski(B_369), B_370)=k1_tarski(B_369) | k3_xboole_0(k1_tarski(B_369), B_370)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_5414])).
% 27.89/19.39  tff(c_32496, plain, (![B_369, B_370]: (k5_xboole_0(k1_tarski(B_369), k1_tarski(B_369))=k4_xboole_0(k1_tarski(B_369), B_370) | k3_xboole_0(k1_tarski(B_369), B_370)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32239, c_6])).
% 27.89/19.39  tff(c_117147, plain, (![B_727, B_728]: (k4_xboole_0(k1_tarski(B_727), B_728)=k1_xboole_0 | k3_xboole_0(k1_tarski(B_727), B_728)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_32496])).
% 27.89/19.39  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.89/19.39  tff(c_118076, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_117147, c_40])).
% 27.89/19.39  tff(c_873, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(B_84, A_83))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_260, c_822])).
% 27.89/19.39  tff(c_933, plain, (![A_14, B_15]: (k4_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_873])).
% 27.89/19.39  tff(c_118204, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_tarski('#skF_1'), '#skF_2'))=k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118076, c_933])).
% 27.89/19.39  tff(c_118483, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70433, c_23736, c_118204])).
% 27.89/19.39  tff(c_118485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7001, c_118483])).
% 27.89/19.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.89/19.39  
% 27.89/19.39  Inference rules
% 27.89/19.39  ----------------------
% 27.89/19.39  #Ref     : 5
% 27.89/19.39  #Sup     : 30170
% 27.89/19.39  #Fact    : 1
% 27.89/19.39  #Define  : 0
% 27.89/19.39  #Split   : 0
% 27.89/19.39  #Chain   : 0
% 27.89/19.39  #Close   : 0
% 27.89/19.39  
% 27.89/19.39  Ordering : KBO
% 27.89/19.39  
% 27.89/19.39  Simplification rules
% 27.89/19.39  ----------------------
% 27.89/19.39  #Subsume      : 3603
% 27.89/19.39  #Demod        : 37111
% 27.89/19.39  #Tautology    : 17341
% 27.89/19.39  #SimpNegUnit  : 2
% 27.89/19.39  #BackRed      : 15
% 27.89/19.39  
% 27.89/19.39  #Partial instantiations: 0
% 27.89/19.39  #Strategies tried      : 1
% 27.89/19.39  
% 27.89/19.39  Timing (in seconds)
% 27.89/19.39  ----------------------
% 27.89/19.39  Preprocessing        : 0.39
% 27.89/19.39  Parsing              : 0.21
% 27.89/19.39  CNF conversion       : 0.02
% 27.89/19.39  Main loop            : 18.17
% 27.89/19.39  Inferencing          : 1.93
% 27.89/19.39  Reduction            : 12.84
% 27.89/19.39  Demodulation         : 12.05
% 27.89/19.39  BG Simplification    : 0.26
% 27.89/19.39  Subsumption          : 2.60
% 27.89/19.39  Abstraction          : 0.53
% 27.89/19.39  MUC search           : 0.00
% 27.89/19.39  Cooper               : 0.00
% 27.89/19.39  Total                : 18.62
% 27.89/19.39  Index Insertion      : 0.00
% 27.89/19.39  Index Deletion       : 0.00
% 27.89/19.39  Index Matching       : 0.00
% 27.89/19.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

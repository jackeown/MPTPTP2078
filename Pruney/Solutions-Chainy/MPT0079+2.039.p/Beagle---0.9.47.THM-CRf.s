%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 332 expanded)
%              Number of leaves         :   27 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          :  104 ( 374 expanded)
%              Number of equality atoms :   78 ( 303 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_327,plain,(
    ! [A_54,B_55] : k4_xboole_0(k2_xboole_0(A_54,B_55),B_55) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_346,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = k2_xboole_0(A_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_12])).

tff(c_407,plain,(
    ! [A_57] : k2_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_346])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_424,plain,(
    ! [A_57] : k2_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_2])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_182,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_1947,plain,(
    ! [A_99,B_100,C_101] : k2_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,C_101)) = k4_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2052,plain,(
    ! [B_100] : k4_xboole_0('#skF_4',k4_xboole_0(B_100,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_4',B_100),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1947])).

tff(c_2088,plain,(
    ! [B_100] : k4_xboole_0('#skF_4',k4_xboole_0(B_100,'#skF_2')) = k4_xboole_0('#skF_4',B_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2,c_2052])).

tff(c_26,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_455,plain,(
    ! [A_58] : k2_xboole_0(k1_xboole_0,A_58) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_465,plain,(
    ! [A_58] : k4_xboole_0(k1_xboole_0,A_58) = k4_xboole_0(A_58,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_14])).

tff(c_505,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_465])).

tff(c_1282,plain,(
    ! [A_86,B_87,C_88] : k4_xboole_0(k4_xboole_0(A_86,B_87),C_88) = k4_xboole_0(A_86,k2_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1340,plain,(
    ! [A_58,C_88] : k4_xboole_0(A_58,k2_xboole_0(A_58,C_88)) = k4_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_1282])).

tff(c_1390,plain,(
    ! [A_58,C_88] : k4_xboole_0(A_58,k2_xboole_0(A_58,C_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1340])).

tff(c_38,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_361,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_327])).

tff(c_3046,plain,(
    ! [B_113] : k4_xboole_0('#skF_4',k4_xboole_0(B_113,'#skF_2')) = k4_xboole_0('#skF_4',B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2,c_2052])).

tff(c_3119,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_3046])).

tff(c_3151,plain,(
    k4_xboole_0('#skF_4','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_1390,c_3119])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_194,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_2049,plain,(
    ! [B_100] : k4_xboole_0('#skF_3',k4_xboole_0(B_100,'#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_3',B_100),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_1947])).

tff(c_3437,plain,(
    ! [B_117] : k4_xboole_0('#skF_3',k4_xboole_0(B_117,'#skF_1')) = k4_xboole_0('#skF_3',B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2,c_2049])).

tff(c_3490,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3151,c_3437])).

tff(c_3538,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3490])).

tff(c_364,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_327])).

tff(c_203,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_203])).

tff(c_240,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_228])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_42,B_43] : k2_xboole_0(k4_xboole_0(A_42,B_43),A_42) = A_42 ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_136,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_2])).

tff(c_549,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_465])).

tff(c_24,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_557,plain,(
    ! [A_62] : k4_xboole_0(A_62,k1_xboole_0) = k3_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_24])).

tff(c_584,plain,(
    ! [A_62] : k3_xboole_0(A_62,A_62) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_557])).

tff(c_2022,plain,(
    ! [A_62,B_100] : k4_xboole_0(A_62,k4_xboole_0(B_100,A_62)) = k2_xboole_0(k4_xboole_0(A_62,B_100),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_1947])).

tff(c_2570,plain,(
    ! [A_109,B_110] : k4_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2,c_2022])).

tff(c_2712,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2570])).

tff(c_274,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_627,plain,(
    ! [A_65,B_66] : r1_tarski(k3_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_822,plain,(
    ! [A_75,B_76] : k2_xboole_0(k3_xboole_0(A_75,B_76),A_75) = A_75 ),
    inference(resolution,[status(thm)],[c_627,c_8])).

tff(c_874,plain,(
    ! [A_1,B_76] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_76)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_822])).

tff(c_566,plain,(
    ! [A_62] : r1_tarski(k1_xboole_0,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_10])).

tff(c_2087,plain,(
    ! [B_100] : k4_xboole_0('#skF_3',k4_xboole_0(B_100,'#skF_1')) = k4_xboole_0('#skF_3',B_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2,c_2049])).

tff(c_1399,plain,(
    ! [A_89,C_90] : k4_xboole_0(A_89,k2_xboole_0(A_89,C_90)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1340])).

tff(c_1474,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1399])).

tff(c_4007,plain,(
    ! [B_121,A_122] : k4_xboole_0(k2_xboole_0(B_121,A_122),B_121) = k4_xboole_0(A_122,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_327])).

tff(c_4108,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4007])).

tff(c_4363,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4108,c_2087])).

tff(c_4403,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_1474,c_4363])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k2_xboole_0(B_19,C_20))
      | ~ r1_tarski(k4_xboole_0(A_18,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4433,plain,(
    ! [C_20] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_2',C_20))
      | ~ r1_tarski(k1_xboole_0,C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4403,c_20])).

tff(c_4498,plain,(
    ! [C_125] : r1_tarski('#skF_3',k2_xboole_0('#skF_2',C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_4433])).

tff(c_4507,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_4498])).

tff(c_4533,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4507,c_8])).

tff(c_939,plain,(
    ! [A_79,B_80,C_81] : k2_xboole_0(k2_xboole_0(A_79,B_80),C_81) = k2_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1036,plain,(
    ! [A_79,B_80,A_1] : k2_xboole_0(A_79,k2_xboole_0(B_80,A_1)) = k2_xboole_0(A_1,k2_xboole_0(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_939])).

tff(c_7063,plain,(
    ! [A_152,A_150,B_151] : k2_xboole_0(A_152,k2_xboole_0(A_150,B_151)) = k2_xboole_0(A_150,k2_xboole_0(B_151,A_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_939])).

tff(c_682,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(A_68,k2_xboole_0(B_69,C_70))
      | ~ r1_tarski(k4_xboole_0(A_68,B_69),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_732,plain,(
    ! [A_71,B_72] : r1_tarski(A_71,k2_xboole_0(B_72,A_71)) ),
    inference(resolution,[status(thm)],[c_10,c_682])).

tff(c_757,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_732])).

tff(c_774,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_757,c_8])).

tff(c_7183,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7063,c_774])).

tff(c_7453,plain,(
    k2_xboole_0('#skF_4','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_2,c_1036,c_2,c_7183])).

tff(c_8123,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7453,c_364])).

tff(c_8156,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3538,c_364,c_2712,c_8123])).

tff(c_8158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.41  
% 6.33/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.41  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.33/2.41  
% 6.33/2.41  %Foreground sorts:
% 6.33/2.41  
% 6.33/2.41  
% 6.33/2.41  %Background operators:
% 6.33/2.41  
% 6.33/2.41  
% 6.33/2.41  %Foreground operators:
% 6.33/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.33/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.33/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.33/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.33/2.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.33/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.33/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.33/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.33/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.33/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.33/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.33/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.33/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.33/2.41  
% 6.33/2.43  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.33/2.43  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.33/2.43  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.33/2.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.33/2.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.33/2.43  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.33/2.43  tff(f_57, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 6.33/2.43  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.33/2.43  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.33/2.43  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.33/2.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.33/2.43  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.33/2.43  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.33/2.43  tff(f_59, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.33/2.43  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.33/2.43  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.33/2.43  tff(c_327, plain, (![A_54, B_55]: (k4_xboole_0(k2_xboole_0(A_54, B_55), B_55)=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.33/2.43  tff(c_346, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=k2_xboole_0(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_327, c_12])).
% 6.33/2.43  tff(c_407, plain, (![A_57]: (k2_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_346])).
% 6.33/2.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.33/2.43  tff(c_424, plain, (![A_57]: (k2_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_407, c_2])).
% 6.33/2.43  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.33/2.43  tff(c_182, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.33/2.43  tff(c_193, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_182])).
% 6.33/2.43  tff(c_1947, plain, (![A_99, B_100, C_101]: (k2_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, C_101))=k4_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.33/2.43  tff(c_2052, plain, (![B_100]: (k4_xboole_0('#skF_4', k4_xboole_0(B_100, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_4', B_100), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1947])).
% 6.33/2.43  tff(c_2088, plain, (![B_100]: (k4_xboole_0('#skF_4', k4_xboole_0(B_100, '#skF_2'))=k4_xboole_0('#skF_4', B_100))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_2, c_2052])).
% 6.33/2.43  tff(c_26, plain, (![A_25]: (k4_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.33/2.43  tff(c_455, plain, (![A_58]: (k2_xboole_0(k1_xboole_0, A_58)=A_58)), inference(superposition, [status(thm), theory('equality')], [c_407, c_2])).
% 6.33/2.43  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.33/2.43  tff(c_465, plain, (![A_58]: (k4_xboole_0(k1_xboole_0, A_58)=k4_xboole_0(A_58, A_58))), inference(superposition, [status(thm), theory('equality')], [c_455, c_14])).
% 6.33/2.43  tff(c_505, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_465])).
% 6.33/2.43  tff(c_1282, plain, (![A_86, B_87, C_88]: (k4_xboole_0(k4_xboole_0(A_86, B_87), C_88)=k4_xboole_0(A_86, k2_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.33/2.43  tff(c_1340, plain, (![A_58, C_88]: (k4_xboole_0(A_58, k2_xboole_0(A_58, C_88))=k4_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_505, c_1282])).
% 6.33/2.43  tff(c_1390, plain, (![A_58, C_88]: (k4_xboole_0(A_58, k2_xboole_0(A_58, C_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1340])).
% 6.33/2.43  tff(c_38, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.33/2.43  tff(c_39, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 6.33/2.43  tff(c_361, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_39, c_327])).
% 6.33/2.43  tff(c_3046, plain, (![B_113]: (k4_xboole_0('#skF_4', k4_xboole_0(B_113, '#skF_2'))=k4_xboole_0('#skF_4', B_113))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_2, c_2052])).
% 6.33/2.43  tff(c_3119, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_3046])).
% 6.33/2.43  tff(c_3151, plain, (k4_xboole_0('#skF_4', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_1390, c_3119])).
% 6.33/2.43  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.33/2.43  tff(c_194, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_182])).
% 6.33/2.43  tff(c_2049, plain, (![B_100]: (k4_xboole_0('#skF_3', k4_xboole_0(B_100, '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_3', B_100), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_1947])).
% 6.33/2.43  tff(c_3437, plain, (![B_117]: (k4_xboole_0('#skF_3', k4_xboole_0(B_117, '#skF_1'))=k4_xboole_0('#skF_3', B_117))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_2, c_2049])).
% 6.33/2.43  tff(c_3490, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3151, c_3437])).
% 6.33/2.43  tff(c_3538, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3490])).
% 6.33/2.43  tff(c_364, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_327])).
% 6.33/2.43  tff(c_203, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.33/2.43  tff(c_228, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_203])).
% 6.33/2.43  tff(c_240, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_228])).
% 6.33/2.43  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.33/2.43  tff(c_112, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.33/2.43  tff(c_130, plain, (![A_42, B_43]: (k2_xboole_0(k4_xboole_0(A_42, B_43), A_42)=A_42)), inference(resolution, [status(thm)], [c_10, c_112])).
% 6.33/2.43  tff(c_136, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k4_xboole_0(A_42, B_43))=A_42)), inference(superposition, [status(thm), theory('equality')], [c_130, c_2])).
% 6.33/2.43  tff(c_549, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_465])).
% 6.33/2.43  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.33/2.43  tff(c_557, plain, (![A_62]: (k4_xboole_0(A_62, k1_xboole_0)=k3_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_549, c_24])).
% 6.33/2.43  tff(c_584, plain, (![A_62]: (k3_xboole_0(A_62, A_62)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_557])).
% 6.33/2.43  tff(c_2022, plain, (![A_62, B_100]: (k4_xboole_0(A_62, k4_xboole_0(B_100, A_62))=k2_xboole_0(k4_xboole_0(A_62, B_100), A_62))), inference(superposition, [status(thm), theory('equality')], [c_584, c_1947])).
% 6.33/2.43  tff(c_2570, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k4_xboole_0(B_110, A_109))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2, c_2022])).
% 6.33/2.43  tff(c_2712, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_240, c_2570])).
% 6.33/2.43  tff(c_274, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.33/2.43  tff(c_627, plain, (![A_65, B_66]: (r1_tarski(k3_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_274, c_10])).
% 6.33/2.43  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.33/2.43  tff(c_822, plain, (![A_75, B_76]: (k2_xboole_0(k3_xboole_0(A_75, B_76), A_75)=A_75)), inference(resolution, [status(thm)], [c_627, c_8])).
% 6.33/2.43  tff(c_874, plain, (![A_1, B_76]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_76))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_822])).
% 6.33/2.43  tff(c_566, plain, (![A_62]: (r1_tarski(k1_xboole_0, A_62))), inference(superposition, [status(thm), theory('equality')], [c_549, c_10])).
% 6.33/2.43  tff(c_2087, plain, (![B_100]: (k4_xboole_0('#skF_3', k4_xboole_0(B_100, '#skF_1'))=k4_xboole_0('#skF_3', B_100))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_2, c_2049])).
% 6.33/2.43  tff(c_1399, plain, (![A_89, C_90]: (k4_xboole_0(A_89, k2_xboole_0(A_89, C_90))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1340])).
% 6.33/2.43  tff(c_1474, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1399])).
% 6.33/2.43  tff(c_4007, plain, (![B_121, A_122]: (k4_xboole_0(k2_xboole_0(B_121, A_122), B_121)=k4_xboole_0(A_122, B_121))), inference(superposition, [status(thm), theory('equality')], [c_2, c_327])).
% 6.33/2.43  tff(c_4108, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39, c_4007])).
% 6.33/2.43  tff(c_4363, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4108, c_2087])).
% 6.33/2.43  tff(c_4403, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2087, c_1474, c_4363])).
% 6.33/2.43  tff(c_20, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k2_xboole_0(B_19, C_20)) | ~r1_tarski(k4_xboole_0(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.33/2.43  tff(c_4433, plain, (![C_20]: (r1_tarski('#skF_3', k2_xboole_0('#skF_2', C_20)) | ~r1_tarski(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_4403, c_20])).
% 6.33/2.43  tff(c_4498, plain, (![C_125]: (r1_tarski('#skF_3', k2_xboole_0('#skF_2', C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_4433])).
% 6.33/2.43  tff(c_4507, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_874, c_4498])).
% 6.33/2.43  tff(c_4533, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_4507, c_8])).
% 6.33/2.43  tff(c_939, plain, (![A_79, B_80, C_81]: (k2_xboole_0(k2_xboole_0(A_79, B_80), C_81)=k2_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.33/2.43  tff(c_1036, plain, (![A_79, B_80, A_1]: (k2_xboole_0(A_79, k2_xboole_0(B_80, A_1))=k2_xboole_0(A_1, k2_xboole_0(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_939])).
% 6.33/2.43  tff(c_7063, plain, (![A_152, A_150, B_151]: (k2_xboole_0(A_152, k2_xboole_0(A_150, B_151))=k2_xboole_0(A_150, k2_xboole_0(B_151, A_152)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_939])).
% 6.33/2.43  tff(c_682, plain, (![A_68, B_69, C_70]: (r1_tarski(A_68, k2_xboole_0(B_69, C_70)) | ~r1_tarski(k4_xboole_0(A_68, B_69), C_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.33/2.43  tff(c_732, plain, (![A_71, B_72]: (r1_tarski(A_71, k2_xboole_0(B_72, A_71)))), inference(resolution, [status(thm)], [c_10, c_682])).
% 6.33/2.43  tff(c_757, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_732])).
% 6.33/2.43  tff(c_774, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_757, c_8])).
% 6.33/2.43  tff(c_7183, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7063, c_774])).
% 6.33/2.43  tff(c_7453, plain, (k2_xboole_0('#skF_4', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_2, c_1036, c_2, c_7183])).
% 6.33/2.43  tff(c_8123, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7453, c_364])).
% 6.33/2.43  tff(c_8156, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3538, c_364, c_2712, c_8123])).
% 6.33/2.43  tff(c_8158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_8156])).
% 6.33/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.43  
% 6.33/2.43  Inference rules
% 6.33/2.43  ----------------------
% 6.33/2.43  #Ref     : 0
% 6.33/2.43  #Sup     : 2089
% 6.33/2.43  #Fact    : 0
% 6.33/2.43  #Define  : 0
% 6.33/2.43  #Split   : 0
% 6.33/2.43  #Chain   : 0
% 6.33/2.43  #Close   : 0
% 6.33/2.43  
% 6.33/2.43  Ordering : KBO
% 6.33/2.43  
% 6.33/2.43  Simplification rules
% 6.33/2.43  ----------------------
% 6.33/2.43  #Subsume      : 8
% 6.33/2.43  #Demod        : 1688
% 6.33/2.43  #Tautology    : 1442
% 6.33/2.43  #SimpNegUnit  : 1
% 6.33/2.43  #BackRed      : 0
% 6.33/2.43  
% 6.33/2.43  #Partial instantiations: 0
% 6.33/2.43  #Strategies tried      : 1
% 6.33/2.43  
% 6.33/2.43  Timing (in seconds)
% 6.33/2.43  ----------------------
% 6.33/2.44  Preprocessing        : 0.35
% 6.33/2.44  Parsing              : 0.19
% 6.33/2.44  CNF conversion       : 0.02
% 6.33/2.44  Main loop            : 1.29
% 6.33/2.44  Inferencing          : 0.35
% 6.33/2.44  Reduction            : 0.63
% 6.33/2.44  Demodulation         : 0.53
% 6.33/2.44  BG Simplification    : 0.04
% 6.33/2.44  Subsumption          : 0.20
% 6.33/2.44  Abstraction          : 0.05
% 6.33/2.44  MUC search           : 0.00
% 6.33/2.44  Cooper               : 0.00
% 6.33/2.44  Total                : 1.69
% 6.33/2.44  Index Insertion      : 0.00
% 6.33/2.44  Index Deletion       : 0.00
% 6.33/2.44  Index Matching       : 0.00
% 6.33/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

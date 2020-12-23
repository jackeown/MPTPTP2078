%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 134 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :   80 ( 143 expanded)
%              Number of equality atoms :   66 ( 125 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_327,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k3_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_337,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,k4_xboole_0(A_12,B_13))) = k3_xboole_0(k4_xboole_0(A_12,B_13),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_16])).

tff(c_368,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,A_12)) = k3_xboole_0(k4_xboole_0(A_12,B_13),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_337])).

tff(c_225,plain,(
    ! [A_50,B_51,C_52] : k4_xboole_0(k4_xboole_0(A_50,B_51),C_52) = k4_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8140,plain,(
    ! [A_182,B_183,C_184] : k4_xboole_0(A_182,k2_xboole_0(k4_xboole_0(A_182,B_183),C_184)) = k4_xboole_0(k3_xboole_0(A_182,B_183),C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_225])).

tff(c_8307,plain,(
    ! [A_12,B_183] : k3_xboole_0(k4_xboole_0(A_12,k4_xboole_0(A_12,B_183)),k1_xboole_0) = k4_xboole_0(k3_xboole_0(A_12,B_183),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_8140])).

tff(c_8398,plain,(
    ! [A_12,B_183] : k4_xboole_0(k3_xboole_0(A_12,B_183),A_12) = k3_xboole_0(k3_xboole_0(A_12,B_183),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8307])).

tff(c_673,plain,(
    ! [C_69,B_70,A_71] :
      ( k4_xboole_0(k2_xboole_0(C_69,B_70),A_71) = k2_xboole_0(k4_xboole_0(C_69,A_71),B_70)
      | ~ r1_xboole_0(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_748,plain,(
    ! [A_1,A_71] :
      ( k2_xboole_0(k4_xboole_0(A_1,A_71),A_1) = k4_xboole_0(A_1,A_71)
      | ~ r1_xboole_0(A_71,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_673])).

tff(c_8270,plain,(
    ! [A_1,A_71] :
      ( k4_xboole_0(k3_xboole_0(A_1,A_71),A_1) = k4_xboole_0(A_1,k4_xboole_0(A_1,A_71))
      | ~ r1_xboole_0(A_71,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_8140])).

tff(c_8388,plain,(
    ! [A_1,A_71] :
      ( k4_xboole_0(k3_xboole_0(A_1,A_71),A_1) = k3_xboole_0(A_1,A_71)
      | ~ r1_xboole_0(A_71,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8270])).

tff(c_50785,plain,(
    ! [A_461,A_462] :
      ( k3_xboole_0(k3_xboole_0(A_461,A_462),k1_xboole_0) = k3_xboole_0(A_461,A_462)
      | ~ r1_xboole_0(A_462,A_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8398,c_8388])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_214,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_1402,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k2_xboole_0(B_88,A_87)) = k3_xboole_0(k4_xboole_0(A_87,B_88),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_337])).

tff(c_1466,plain,(
    ! [A_1] : k3_xboole_0(k4_xboole_0(A_1,A_1),k1_xboole_0) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1402])).

tff(c_1482,plain,(
    ! [A_1] : k3_xboole_0(k3_xboole_0(A_1,k1_xboole_0),k1_xboole_0) = k3_xboole_0(A_1,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_214,c_1466])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1969,plain,(
    ! [C_96,A_97] :
      ( k2_xboole_0(k4_xboole_0(C_96,A_97),A_97) = k4_xboole_0(C_96,A_97)
      | ~ r1_xboole_0(A_97,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_14])).

tff(c_2038,plain,(
    ! [A_17] :
      ( k4_xboole_0(k1_xboole_0,A_17) = k2_xboole_0(k1_xboole_0,A_17)
      | ~ r1_xboole_0(A_17,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1969])).

tff(c_2059,plain,(
    ! [A_98] :
      ( k2_xboole_0(k1_xboole_0,A_98) = k1_xboole_0
      | ~ r1_xboole_0(A_98,A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2038])).

tff(c_2063,plain,(
    ! [B_20] :
      ( k2_xboole_0(k1_xboole_0,B_20) = k1_xboole_0
      | k4_xboole_0(B_20,B_20) != B_20 ) ),
    inference(resolution,[status(thm)],[c_26,c_2059])).

tff(c_2256,plain,(
    ! [B_101] :
      ( k2_xboole_0(k1_xboole_0,B_101) = k1_xboole_0
      | k3_xboole_0(B_101,k1_xboole_0) != B_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2063])).

tff(c_2275,plain,(
    ! [A_102] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_102,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_2256])).

tff(c_202,plain,(
    ! [B_49] : k3_xboole_0(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_20])).

tff(c_556,plain,(
    ! [A_65,B_66] : k5_xboole_0(k5_xboole_0(A_65,B_66),k3_xboole_0(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_851,plain,(
    ! [B_74] : k5_xboole_0(k5_xboole_0(k1_xboole_0,B_74),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_556])).

tff(c_30,plain,(
    ! [A_24,B_25,C_26] : k5_xboole_0(k5_xboole_0(A_24,B_25),C_26) = k5_xboole_0(A_24,k5_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_863,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_74,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_30])).

tff(c_895,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,B_74) = k2_xboole_0(k1_xboole_0,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_863])).

tff(c_297,plain,(
    ! [A_54,B_55,C_56] : k5_xboole_0(k5_xboole_0(A_54,B_55),C_56) = k5_xboole_0(A_54,k5_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_316,plain,(
    ! [A_18,C_56] : k5_xboole_0(A_18,k5_xboole_0(k1_xboole_0,C_56)) = k5_xboole_0(A_18,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_297])).

tff(c_903,plain,(
    ! [A_18,C_56] : k5_xboole_0(A_18,k2_xboole_0(k1_xboole_0,C_56)) = k5_xboole_0(A_18,C_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_316])).

tff(c_2295,plain,(
    ! [A_18,A_102] : k5_xboole_0(A_18,k3_xboole_0(A_102,k1_xboole_0)) = k5_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2275,c_903])).

tff(c_2336,plain,(
    ! [A_18,A_102] : k5_xboole_0(A_18,k3_xboole_0(A_102,k1_xboole_0)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2295])).

tff(c_51530,plain,(
    ! [A_469,A_470,A_471] :
      ( k5_xboole_0(A_469,k3_xboole_0(A_470,A_471)) = A_469
      | ~ r1_xboole_0(A_471,A_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50785,c_2336])).

tff(c_32,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52338,plain,(
    ! [A_475,A_476] :
      ( k5_xboole_0(A_475,A_476) = k2_xboole_0(A_475,A_476)
      | ~ r1_xboole_0(A_476,A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51530,c_32])).

tff(c_53652,plain,(
    ! [B_493,A_494] :
      ( k5_xboole_0(B_493,A_494) = k2_xboole_0(B_493,A_494)
      | k4_xboole_0(A_494,B_493) != A_494 ) ),
    inference(resolution,[status(thm)],[c_26,c_52338])).

tff(c_34,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53850,plain,
    ( k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_1') != k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53652,c_34])).

tff(c_53988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_10,c_53850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.95/8.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/8.19  
% 15.95/8.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/8.20  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 15.95/8.20  
% 15.95/8.20  %Foreground sorts:
% 15.95/8.20  
% 15.95/8.20  
% 15.95/8.20  %Background operators:
% 15.95/8.20  
% 15.95/8.20  
% 15.95/8.20  %Foreground operators:
% 15.95/8.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/8.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.95/8.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.95/8.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.95/8.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.95/8.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.95/8.20  tff('#skF_2', type, '#skF_2': $i).
% 15.95/8.20  tff('#skF_1', type, '#skF_1': $i).
% 15.95/8.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/8.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/8.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.95/8.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.95/8.20  
% 15.95/8.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 15.95/8.21  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 15.95/8.21  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 15.95/8.21  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.95/8.21  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.95/8.21  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 15.95/8.21  tff(f_57, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 15.95/8.21  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 15.95/8.21  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 15.95/8.21  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 15.95/8.21  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 15.95/8.21  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.95/8.21  tff(f_64, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.95/8.21  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.95/8.21  tff(c_16, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.95/8.21  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.95/8.21  tff(c_26, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.95/8.21  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.95/8.21  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.95/8.21  tff(c_189, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.95/8.21  tff(c_327, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k3_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_189])).
% 15.95/8.21  tff(c_337, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, k4_xboole_0(A_12, B_13)))=k3_xboole_0(k4_xboole_0(A_12, B_13), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_327, c_16])).
% 15.95/8.21  tff(c_368, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, A_12))=k3_xboole_0(k4_xboole_0(A_12, B_13), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_337])).
% 15.95/8.21  tff(c_225, plain, (![A_50, B_51, C_52]: (k4_xboole_0(k4_xboole_0(A_50, B_51), C_52)=k4_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.95/8.21  tff(c_8140, plain, (![A_182, B_183, C_184]: (k4_xboole_0(A_182, k2_xboole_0(k4_xboole_0(A_182, B_183), C_184))=k4_xboole_0(k3_xboole_0(A_182, B_183), C_184))), inference(superposition, [status(thm), theory('equality')], [c_18, c_225])).
% 15.95/8.21  tff(c_8307, plain, (![A_12, B_183]: (k3_xboole_0(k4_xboole_0(A_12, k4_xboole_0(A_12, B_183)), k1_xboole_0)=k4_xboole_0(k3_xboole_0(A_12, B_183), A_12))), inference(superposition, [status(thm), theory('equality')], [c_368, c_8140])).
% 15.95/8.21  tff(c_8398, plain, (![A_12, B_183]: (k4_xboole_0(k3_xboole_0(A_12, B_183), A_12)=k3_xboole_0(k3_xboole_0(A_12, B_183), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8307])).
% 15.95/8.21  tff(c_673, plain, (![C_69, B_70, A_71]: (k4_xboole_0(k2_xboole_0(C_69, B_70), A_71)=k2_xboole_0(k4_xboole_0(C_69, A_71), B_70) | ~r1_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.95/8.21  tff(c_748, plain, (![A_1, A_71]: (k2_xboole_0(k4_xboole_0(A_1, A_71), A_1)=k4_xboole_0(A_1, A_71) | ~r1_xboole_0(A_71, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_673])).
% 15.95/8.21  tff(c_8270, plain, (![A_1, A_71]: (k4_xboole_0(k3_xboole_0(A_1, A_71), A_1)=k4_xboole_0(A_1, k4_xboole_0(A_1, A_71)) | ~r1_xboole_0(A_71, A_1))), inference(superposition, [status(thm), theory('equality')], [c_748, c_8140])).
% 15.95/8.21  tff(c_8388, plain, (![A_1, A_71]: (k4_xboole_0(k3_xboole_0(A_1, A_71), A_1)=k3_xboole_0(A_1, A_71) | ~r1_xboole_0(A_71, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8270])).
% 15.95/8.21  tff(c_50785, plain, (![A_461, A_462]: (k3_xboole_0(k3_xboole_0(A_461, A_462), k1_xboole_0)=k3_xboole_0(A_461, A_462) | ~r1_xboole_0(A_462, A_461))), inference(demodulation, [status(thm), theory('equality')], [c_8398, c_8388])).
% 15.95/8.21  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.95/8.21  tff(c_214, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_189])).
% 15.95/8.21  tff(c_1402, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k2_xboole_0(B_88, A_87))=k3_xboole_0(k4_xboole_0(A_87, B_88), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_337])).
% 15.95/8.21  tff(c_1466, plain, (![A_1]: (k3_xboole_0(k4_xboole_0(A_1, A_1), k1_xboole_0)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1402])).
% 15.95/8.21  tff(c_1482, plain, (![A_1]: (k3_xboole_0(k3_xboole_0(A_1, k1_xboole_0), k1_xboole_0)=k3_xboole_0(A_1, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_214, c_1466])).
% 15.95/8.21  tff(c_20, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.95/8.21  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.95/8.21  tff(c_1969, plain, (![C_96, A_97]: (k2_xboole_0(k4_xboole_0(C_96, A_97), A_97)=k4_xboole_0(C_96, A_97) | ~r1_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_673, c_14])).
% 15.95/8.21  tff(c_2038, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k2_xboole_0(k1_xboole_0, A_17) | ~r1_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1969])).
% 15.95/8.21  tff(c_2059, plain, (![A_98]: (k2_xboole_0(k1_xboole_0, A_98)=k1_xboole_0 | ~r1_xboole_0(A_98, A_98))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2038])).
% 15.95/8.21  tff(c_2063, plain, (![B_20]: (k2_xboole_0(k1_xboole_0, B_20)=k1_xboole_0 | k4_xboole_0(B_20, B_20)!=B_20)), inference(resolution, [status(thm)], [c_26, c_2059])).
% 15.95/8.21  tff(c_2256, plain, (![B_101]: (k2_xboole_0(k1_xboole_0, B_101)=k1_xboole_0 | k3_xboole_0(B_101, k1_xboole_0)!=B_101)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2063])).
% 15.95/8.21  tff(c_2275, plain, (![A_102]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_102, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1482, c_2256])).
% 15.95/8.21  tff(c_202, plain, (![B_49]: (k3_xboole_0(k1_xboole_0, B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_20])).
% 15.95/8.21  tff(c_556, plain, (![A_65, B_66]: (k5_xboole_0(k5_xboole_0(A_65, B_66), k3_xboole_0(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.95/8.21  tff(c_851, plain, (![B_74]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, B_74), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_202, c_556])).
% 15.95/8.21  tff(c_30, plain, (![A_24, B_25, C_26]: (k5_xboole_0(k5_xboole_0(A_24, B_25), C_26)=k5_xboole_0(A_24, k5_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.95/8.21  tff(c_863, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_74, k1_xboole_0))=k2_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_851, c_30])).
% 15.95/8.21  tff(c_895, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, B_74)=k2_xboole_0(k1_xboole_0, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_863])).
% 15.95/8.21  tff(c_297, plain, (![A_54, B_55, C_56]: (k5_xboole_0(k5_xboole_0(A_54, B_55), C_56)=k5_xboole_0(A_54, k5_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.95/8.21  tff(c_316, plain, (![A_18, C_56]: (k5_xboole_0(A_18, k5_xboole_0(k1_xboole_0, C_56))=k5_xboole_0(A_18, C_56))), inference(superposition, [status(thm), theory('equality')], [c_22, c_297])).
% 15.95/8.21  tff(c_903, plain, (![A_18, C_56]: (k5_xboole_0(A_18, k2_xboole_0(k1_xboole_0, C_56))=k5_xboole_0(A_18, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_316])).
% 15.95/8.21  tff(c_2295, plain, (![A_18, A_102]: (k5_xboole_0(A_18, k3_xboole_0(A_102, k1_xboole_0))=k5_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2275, c_903])).
% 15.95/8.21  tff(c_2336, plain, (![A_18, A_102]: (k5_xboole_0(A_18, k3_xboole_0(A_102, k1_xboole_0))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2295])).
% 15.95/8.21  tff(c_51530, plain, (![A_469, A_470, A_471]: (k5_xboole_0(A_469, k3_xboole_0(A_470, A_471))=A_469 | ~r1_xboole_0(A_471, A_470))), inference(superposition, [status(thm), theory('equality')], [c_50785, c_2336])).
% 15.95/8.21  tff(c_32, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.95/8.21  tff(c_52338, plain, (![A_475, A_476]: (k5_xboole_0(A_475, A_476)=k2_xboole_0(A_475, A_476) | ~r1_xboole_0(A_476, A_475))), inference(superposition, [status(thm), theory('equality')], [c_51530, c_32])).
% 15.95/8.21  tff(c_53652, plain, (![B_493, A_494]: (k5_xboole_0(B_493, A_494)=k2_xboole_0(B_493, A_494) | k4_xboole_0(A_494, B_493)!=A_494)), inference(resolution, [status(thm)], [c_26, c_52338])).
% 15.95/8.21  tff(c_34, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.95/8.21  tff(c_53850, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2') | k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_1')!=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53652, c_34])).
% 15.95/8.21  tff(c_53988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_16, c_10, c_53850])).
% 15.95/8.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/8.21  
% 15.95/8.21  Inference rules
% 15.95/8.21  ----------------------
% 15.95/8.21  #Ref     : 1
% 15.95/8.21  #Sup     : 12938
% 15.95/8.21  #Fact    : 0
% 15.95/8.21  #Define  : 0
% 15.95/8.21  #Split   : 4
% 15.95/8.21  #Chain   : 0
% 15.95/8.21  #Close   : 0
% 15.95/8.21  
% 16.11/8.21  Ordering : KBO
% 16.11/8.21  
% 16.11/8.21  Simplification rules
% 16.11/8.21  ----------------------
% 16.11/8.21  #Subsume      : 606
% 16.11/8.21  #Demod        : 19098
% 16.11/8.21  #Tautology    : 7698
% 16.11/8.21  #SimpNegUnit  : 0
% 16.11/8.21  #BackRed      : 14
% 16.11/8.21  
% 16.11/8.21  #Partial instantiations: 0
% 16.11/8.21  #Strategies tried      : 1
% 16.11/8.21  
% 16.11/8.21  Timing (in seconds)
% 16.11/8.21  ----------------------
% 16.11/8.21  Preprocessing        : 0.30
% 16.11/8.21  Parsing              : 0.17
% 16.11/8.21  CNF conversion       : 0.02
% 16.11/8.22  Main loop            : 7.14
% 16.11/8.22  Inferencing          : 1.37
% 16.11/8.22  Reduction            : 4.16
% 16.11/8.22  Demodulation         : 3.79
% 16.11/8.22  BG Simplification    : 0.18
% 16.11/8.22  Subsumption          : 1.16
% 16.11/8.22  Abstraction          : 0.38
% 16.11/8.22  MUC search           : 0.00
% 16.11/8.22  Cooper               : 0.00
% 16.11/8.22  Total                : 7.48
% 16.11/8.22  Index Insertion      : 0.00
% 16.11/8.22  Index Deletion       : 0.00
% 16.11/8.22  Index Matching       : 0.00
% 16.11/8.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

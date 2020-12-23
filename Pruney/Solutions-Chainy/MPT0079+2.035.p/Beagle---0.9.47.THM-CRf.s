%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 8.75s
% Output     : CNFRefutation 8.75s
% Verified   : 
% Statistics : Number of formulae       :  131 (1478 expanded)
%              Number of leaves         :   25 ( 508 expanded)
%              Depth                    :   20
%              Number of atoms          :  131 (1620 expanded)
%              Number of equality atoms :  113 (1468 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_265,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_286,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_290,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_1469,plain,(
    ! [A_73,C_74,B_75] : k2_xboole_0(k4_xboole_0(A_73,C_74),k4_xboole_0(B_75,C_74)) = k4_xboole_0(k2_xboole_0(A_73,B_75),C_74) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1564,plain,(
    ! [A_11,B_75] : k4_xboole_0(k2_xboole_0(A_11,B_75),A_11) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_75,A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_1469])).

tff(c_1611,plain,(
    ! [A_11,B_75] : k4_xboole_0(k2_xboole_0(A_11,B_75),A_11) = k4_xboole_0(B_75,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1564])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_171,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_216,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_216])).

tff(c_369,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_96])).

tff(c_1567,plain,(
    ! [A_73,A_11] : k4_xboole_0(k2_xboole_0(A_73,A_11),A_11) = k2_xboole_0(k4_xboole_0(A_73,A_11),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_1469])).

tff(c_1612,plain,(
    ! [A_73,A_11] : k4_xboole_0(k2_xboole_0(A_73,A_11),A_11) = k4_xboole_0(A_73,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1567])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_61])).

tff(c_188,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_171])).

tff(c_225,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_216])).

tff(c_466,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_584,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k2_xboole_0(A_52,B_53),C_54) = k2_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1979,plain,(
    ! [C_82,A_83,B_84] : k2_xboole_0(C_82,k2_xboole_0(A_83,B_84)) = k2_xboole_0(A_83,k2_xboole_0(B_84,C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_2])).

tff(c_2769,plain,(
    ! [A_90,C_91] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_90,C_91)) = k2_xboole_0(C_91,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1979])).

tff(c_2897,plain,(
    ! [B_10,A_9] : k2_xboole_0(k4_xboole_0(B_10,A_9),A_9) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2769])).

tff(c_2954,plain,(
    ! [B_10,A_9] : k2_xboole_0(k4_xboole_0(B_10,A_9),A_9) = k2_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2897])).

tff(c_4316,plain,(
    ! [B_106,A_107,C_108] : k2_xboole_0(k2_xboole_0(B_106,A_107),C_108) = k2_xboole_0(A_107,k2_xboole_0(B_106,C_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_584])).

tff(c_994,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k4_xboole_0(A_62,B_63),C_64) = k4_xboole_0(A_62,k2_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1007,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,k4_xboole_0(A_62,B_63))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_290])).

tff(c_1066,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1007])).

tff(c_5759,plain,(
    ! [C_116,A_117,B_118] : k4_xboole_0(C_116,k2_xboole_0(A_117,k2_xboole_0(B_118,C_116))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4316,c_1066])).

tff(c_5847,plain,(
    ! [A_9,A_117,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_117,k2_xboole_0(A_9,B_10))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_5759])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_2281,plain,(
    ! [A_83] : k2_xboole_0(A_83,k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2',k2_xboole_0(A_83,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_1979])).

tff(c_190,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_171])).

tff(c_234,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_216])).

tff(c_342,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_96])).

tff(c_9743,plain,(
    ! [C_143] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_143)) = k4_xboole_0('#skF_4',C_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_994])).

tff(c_9811,plain,(
    ! [A_83] : k4_xboole_0('#skF_4',k2_xboole_0(A_83,k2_xboole_0('#skF_4','#skF_3'))) = k4_xboole_0('#skF_4',k2_xboole_0(A_83,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2281,c_9743])).

tff(c_9903,plain,(
    ! [A_144] : k4_xboole_0('#skF_4',k2_xboole_0(A_144,'#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_9811])).

tff(c_1039,plain,(
    ! [C_64] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_64)) = k4_xboole_0('#skF_4',C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_994])).

tff(c_9909,plain,(
    k4_xboole_0('#skF_4','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9903,c_1039])).

tff(c_10038,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_1') = k2_xboole_0('#skF_1','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9909,c_2954])).

tff(c_10070,plain,(
    k2_xboole_0('#skF_4','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2,c_10038])).

tff(c_376,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_392,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_376])).

tff(c_410,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_392])).

tff(c_4609,plain,(
    ! [A_109,C_110] : k2_xboole_0(A_109,k2_xboole_0(A_109,C_110)) = k2_xboole_0(C_110,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_1979])).

tff(c_2236,plain,(
    ! [A_31,C_82] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_31,C_82)) = k2_xboole_0(C_82,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1979])).

tff(c_4635,plain,(
    ! [A_109,C_110] : k2_xboole_0(k2_xboole_0(A_109,C_110),A_109) = k2_xboole_0(k1_xboole_0,k2_xboole_0(C_110,A_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4609,c_2236])).

tff(c_8660,plain,(
    ! [A_135,C_136] : k2_xboole_0(k2_xboole_0(A_135,C_136),A_135) = k2_xboole_0(C_136,A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_4635])).

tff(c_8943,plain,(
    k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_8660])).

tff(c_9030,plain,(
    k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2,c_8943])).

tff(c_640,plain,(
    ! [B_2,A_1,C_54] : k2_xboole_0(k2_xboole_0(B_2,A_1),C_54) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_584])).

tff(c_14053,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_1')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9030,c_640])).

tff(c_14134,plain,(
    k2_xboole_0('#skF_1','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10070,c_14053])).

tff(c_14212,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14134,c_1612])).

tff(c_14263,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_466,c_14212])).

tff(c_26,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1077,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1007])).

tff(c_1260,plain,(
    ! [A_69,B_70] : k4_xboole_0(k4_xboole_0(A_69,B_70),A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1077])).

tff(c_1274,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k2_xboole_0(A_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_14])).

tff(c_1335,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1274])).

tff(c_2862,plain,(
    ! [A_69,B_70] : k2_xboole_0(k4_xboole_0(A_69,B_70),A_69) = k2_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_2769])).

tff(c_2944,plain,(
    ! [A_69,B_70] : k2_xboole_0(k4_xboole_0(A_69,B_70),A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2862])).

tff(c_14303,plain,(
    k2_xboole_0('#skF_1','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14263,c_2944])).

tff(c_9890,plain,(
    ! [A_83] : k4_xboole_0('#skF_4',k2_xboole_0(A_83,'#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5847,c_9811])).

tff(c_10080,plain,(
    ! [A_145,B_146] : k2_xboole_0(k3_xboole_0(A_145,k4_xboole_0(A_145,B_146)),k3_xboole_0(A_145,B_146)) = A_145 ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_26])).

tff(c_10176,plain,(
    ! [A_83] : k2_xboole_0(k3_xboole_0('#skF_4',k1_xboole_0),k3_xboole_0('#skF_4',k2_xboole_0(A_83,'#skF_1'))) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9890,c_10080])).

tff(c_11095,plain,(
    ! [A_152] : k3_xboole_0('#skF_4',k2_xboole_0(A_152,'#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_12,c_10176])).

tff(c_11186,plain,(
    ! [B_2] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_1',B_2)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11095])).

tff(c_11360,plain,(
    ! [A_154,B_155,C_156] : k2_xboole_0(k3_xboole_0(A_154,B_155),k2_xboole_0(k4_xboole_0(A_154,B_155),C_156)) = k2_xboole_0(A_154,C_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_584])).

tff(c_1143,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1077])).

tff(c_13142,plain,(
    ! [A_166,B_167,C_168] : k4_xboole_0(k3_xboole_0(A_166,B_167),k2_xboole_0(A_166,C_168)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11360,c_1143])).

tff(c_13493,plain,(
    ! [B_169] : k4_xboole_0(k3_xboole_0('#skF_4',B_169),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10070,c_13142])).

tff(c_13522,plain,(
    ! [B_169] : k2_xboole_0('#skF_1',k3_xboole_0('#skF_4',B_169)) = k2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13493,c_2954])).

tff(c_13722,plain,(
    ! [B_171] : k2_xboole_0('#skF_1',k3_xboole_0('#skF_4',B_171)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_13522])).

tff(c_13813,plain,(
    k2_xboole_0('#skF_1','#skF_4') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11186,c_13722])).

tff(c_14394,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14303,c_13813])).

tff(c_2521,plain,(
    ! [A_86,B_87] : k4_xboole_0(k2_xboole_0(A_86,B_87),A_86) = k4_xboole_0(B_87,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1564])).

tff(c_2612,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_2521])).

tff(c_14543,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14394,c_14394,c_2612])).

tff(c_14574,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_369,c_14543])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14324,plain,(
    k4_xboole_0('#skF_4','#skF_1') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14263,c_22])).

tff(c_14338,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9909,c_14324])).

tff(c_167,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | k3_xboole_0(A_38,B_37) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(B_37,A_38) = k1_xboole_0
      | k3_xboole_0(A_38,B_37) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_208,c_4])).

tff(c_14645,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14338,c_214])).

tff(c_2900,plain,(
    ! [A_23,B_24] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(k1_xboole_0,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2769])).

tff(c_2955,plain,(
    ! [A_23,B_24] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2900])).

tff(c_15079,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14645,c_2955])).

tff(c_15104,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14574,c_15079])).

tff(c_15106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_15104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.75/3.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/3.36  
% 8.75/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/3.36  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.75/3.36  
% 8.75/3.36  %Foreground sorts:
% 8.75/3.36  
% 8.75/3.36  
% 8.75/3.36  %Background operators:
% 8.75/3.36  
% 8.75/3.36  
% 8.75/3.36  %Foreground operators:
% 8.75/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.75/3.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.75/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.75/3.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.75/3.36  tff('#skF_2', type, '#skF_2': $i).
% 8.75/3.36  tff('#skF_3', type, '#skF_3': $i).
% 8.75/3.36  tff('#skF_1', type, '#skF_1': $i).
% 8.75/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.75/3.36  tff('#skF_4', type, '#skF_4': $i).
% 8.75/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.75/3.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.75/3.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.75/3.36  
% 8.75/3.39  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.75/3.39  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.75/3.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.75/3.39  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.75/3.39  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.75/3.39  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.75/3.39  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 8.75/3.39  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.75/3.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.75/3.39  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.75/3.39  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.75/3.39  tff(f_51, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.75/3.39  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.75/3.39  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.75/3.39  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.75/3.39  tff(c_80, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.75/3.39  tff(c_96, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_80, c_10])).
% 8.75/3.39  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.75/3.39  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.75/3.39  tff(c_265, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.75/3.39  tff(c_286, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_265])).
% 8.75/3.39  tff(c_290, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_286])).
% 8.75/3.39  tff(c_1469, plain, (![A_73, C_74, B_75]: (k2_xboole_0(k4_xboole_0(A_73, C_74), k4_xboole_0(B_75, C_74))=k4_xboole_0(k2_xboole_0(A_73, B_75), C_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.75/3.39  tff(c_1564, plain, (![A_11, B_75]: (k4_xboole_0(k2_xboole_0(A_11, B_75), A_11)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_75, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_1469])).
% 8.75/3.39  tff(c_1611, plain, (![A_11, B_75]: (k4_xboole_0(k2_xboole_0(A_11, B_75), A_11)=k4_xboole_0(B_75, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1564])).
% 8.75/3.39  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.75/3.39  tff(c_61, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.75/3.39  tff(c_66, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_61])).
% 8.75/3.39  tff(c_171, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.75/3.39  tff(c_189, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_171])).
% 8.75/3.39  tff(c_216, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.75/3.39  tff(c_228, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_189, c_216])).
% 8.75/3.39  tff(c_369, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_228, c_96])).
% 8.75/3.39  tff(c_1567, plain, (![A_73, A_11]: (k4_xboole_0(k2_xboole_0(A_73, A_11), A_11)=k2_xboole_0(k4_xboole_0(A_73, A_11), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_290, c_1469])).
% 8.75/3.39  tff(c_1612, plain, (![A_73, A_11]: (k4_xboole_0(k2_xboole_0(A_73, A_11), A_11)=k4_xboole_0(A_73, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1567])).
% 8.75/3.39  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.75/3.39  tff(c_67, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_61])).
% 8.75/3.39  tff(c_188, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_67, c_171])).
% 8.75/3.39  tff(c_225, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_188, c_216])).
% 8.75/3.39  tff(c_466, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_225, c_96])).
% 8.75/3.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.75/3.39  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.75/3.39  tff(c_584, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k2_xboole_0(A_52, B_53), C_54)=k2_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.75/3.39  tff(c_1979, plain, (![C_82, A_83, B_84]: (k2_xboole_0(C_82, k2_xboole_0(A_83, B_84))=k2_xboole_0(A_83, k2_xboole_0(B_84, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_584, c_2])).
% 8.75/3.39  tff(c_2769, plain, (![A_90, C_91]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_90, C_91))=k2_xboole_0(C_91, A_90))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1979])).
% 8.75/3.39  tff(c_2897, plain, (![B_10, A_9]: (k2_xboole_0(k4_xboole_0(B_10, A_9), A_9)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2769])).
% 8.75/3.39  tff(c_2954, plain, (![B_10, A_9]: (k2_xboole_0(k4_xboole_0(B_10, A_9), A_9)=k2_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2897])).
% 8.75/3.39  tff(c_4316, plain, (![B_106, A_107, C_108]: (k2_xboole_0(k2_xboole_0(B_106, A_107), C_108)=k2_xboole_0(A_107, k2_xboole_0(B_106, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_584])).
% 8.75/3.39  tff(c_994, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k4_xboole_0(A_62, B_63), C_64)=k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.75/3.39  tff(c_1007, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, k4_xboole_0(A_62, B_63)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_994, c_290])).
% 8.75/3.39  tff(c_1066, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, A_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1007])).
% 8.75/3.39  tff(c_5759, plain, (![C_116, A_117, B_118]: (k4_xboole_0(C_116, k2_xboole_0(A_117, k2_xboole_0(B_118, C_116)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4316, c_1066])).
% 8.75/3.39  tff(c_5847, plain, (![A_9, A_117, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_117, k2_xboole_0(A_9, B_10)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2954, c_5759])).
% 8.75/3.39  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.75/3.39  tff(c_35, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 8.75/3.39  tff(c_2281, plain, (![A_83]: (k2_xboole_0(A_83, k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', k2_xboole_0(A_83, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35, c_1979])).
% 8.75/3.39  tff(c_190, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_171])).
% 8.75/3.39  tff(c_234, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_2'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_190, c_216])).
% 8.75/3.39  tff(c_342, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_234, c_96])).
% 8.75/3.39  tff(c_9743, plain, (![C_143]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_143))=k4_xboole_0('#skF_4', C_143))), inference(superposition, [status(thm), theory('equality')], [c_342, c_994])).
% 8.75/3.39  tff(c_9811, plain, (![A_83]: (k4_xboole_0('#skF_4', k2_xboole_0(A_83, k2_xboole_0('#skF_4', '#skF_3')))=k4_xboole_0('#skF_4', k2_xboole_0(A_83, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2281, c_9743])).
% 8.75/3.39  tff(c_9903, plain, (![A_144]: (k4_xboole_0('#skF_4', k2_xboole_0(A_144, '#skF_1'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5847, c_9811])).
% 8.75/3.39  tff(c_1039, plain, (![C_64]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_64))=k4_xboole_0('#skF_4', C_64))), inference(superposition, [status(thm), theory('equality')], [c_342, c_994])).
% 8.75/3.39  tff(c_9909, plain, (k4_xboole_0('#skF_4', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9903, c_1039])).
% 8.75/3.39  tff(c_10038, plain, (k2_xboole_0(k1_xboole_0, '#skF_1')=k2_xboole_0('#skF_1', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9909, c_2954])).
% 8.75/3.39  tff(c_10070, plain, (k2_xboole_0('#skF_4', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2, c_10038])).
% 8.75/3.39  tff(c_376, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.75/3.39  tff(c_392, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_290, c_376])).
% 8.75/3.39  tff(c_410, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_392])).
% 8.75/3.39  tff(c_4609, plain, (![A_109, C_110]: (k2_xboole_0(A_109, k2_xboole_0(A_109, C_110))=k2_xboole_0(C_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_410, c_1979])).
% 8.75/3.39  tff(c_2236, plain, (![A_31, C_82]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_31, C_82))=k2_xboole_0(C_82, A_31))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1979])).
% 8.75/3.39  tff(c_4635, plain, (![A_109, C_110]: (k2_xboole_0(k2_xboole_0(A_109, C_110), A_109)=k2_xboole_0(k1_xboole_0, k2_xboole_0(C_110, A_109)))), inference(superposition, [status(thm), theory('equality')], [c_4609, c_2236])).
% 8.75/3.39  tff(c_8660, plain, (![A_135, C_136]: (k2_xboole_0(k2_xboole_0(A_135, C_136), A_135)=k2_xboole_0(C_136, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_4635])).
% 8.75/3.39  tff(c_8943, plain, (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_8660])).
% 8.75/3.39  tff(c_9030, plain, (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2, c_8943])).
% 8.75/3.39  tff(c_640, plain, (![B_2, A_1, C_54]: (k2_xboole_0(k2_xboole_0(B_2, A_1), C_54)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_584])).
% 8.75/3.39  tff(c_14053, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_1'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9030, c_640])).
% 8.75/3.39  tff(c_14134, plain, (k2_xboole_0('#skF_1', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10070, c_14053])).
% 8.75/3.39  tff(c_14212, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14134, c_1612])).
% 8.75/3.39  tff(c_14263, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_466, c_14212])).
% 8.75/3.39  tff(c_26, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.75/3.39  tff(c_1077, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, A_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1007])).
% 8.75/3.39  tff(c_1260, plain, (![A_69, B_70]: (k4_xboole_0(k4_xboole_0(A_69, B_70), A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1077])).
% 8.75/3.39  tff(c_1274, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k2_xboole_0(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1260, c_14])).
% 8.75/3.39  tff(c_1335, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(A_69, B_70))=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1274])).
% 8.75/3.39  tff(c_2862, plain, (![A_69, B_70]: (k2_xboole_0(k4_xboole_0(A_69, B_70), A_69)=k2_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_2769])).
% 8.75/3.39  tff(c_2944, plain, (![A_69, B_70]: (k2_xboole_0(k4_xboole_0(A_69, B_70), A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2862])).
% 8.75/3.39  tff(c_14303, plain, (k2_xboole_0('#skF_1', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14263, c_2944])).
% 8.75/3.39  tff(c_9890, plain, (![A_83]: (k4_xboole_0('#skF_4', k2_xboole_0(A_83, '#skF_1'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5847, c_9811])).
% 8.75/3.39  tff(c_10080, plain, (![A_145, B_146]: (k2_xboole_0(k3_xboole_0(A_145, k4_xboole_0(A_145, B_146)), k3_xboole_0(A_145, B_146))=A_145)), inference(superposition, [status(thm), theory('equality')], [c_265, c_26])).
% 8.75/3.39  tff(c_10176, plain, (![A_83]: (k2_xboole_0(k3_xboole_0('#skF_4', k1_xboole_0), k3_xboole_0('#skF_4', k2_xboole_0(A_83, '#skF_1')))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9890, c_10080])).
% 8.75/3.39  tff(c_11095, plain, (![A_152]: (k3_xboole_0('#skF_4', k2_xboole_0(A_152, '#skF_1'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_12, c_10176])).
% 8.75/3.39  tff(c_11186, plain, (![B_2]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_1', B_2))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_11095])).
% 8.75/3.39  tff(c_11360, plain, (![A_154, B_155, C_156]: (k2_xboole_0(k3_xboole_0(A_154, B_155), k2_xboole_0(k4_xboole_0(A_154, B_155), C_156))=k2_xboole_0(A_154, C_156))), inference(superposition, [status(thm), theory('equality')], [c_26, c_584])).
% 8.75/3.39  tff(c_1143, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1077])).
% 8.75/3.39  tff(c_13142, plain, (![A_166, B_167, C_168]: (k4_xboole_0(k3_xboole_0(A_166, B_167), k2_xboole_0(A_166, C_168))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11360, c_1143])).
% 8.75/3.39  tff(c_13493, plain, (![B_169]: (k4_xboole_0(k3_xboole_0('#skF_4', B_169), '#skF_1')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10070, c_13142])).
% 8.75/3.39  tff(c_13522, plain, (![B_169]: (k2_xboole_0('#skF_1', k3_xboole_0('#skF_4', B_169))=k2_xboole_0(k1_xboole_0, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13493, c_2954])).
% 8.75/3.39  tff(c_13722, plain, (![B_171]: (k2_xboole_0('#skF_1', k3_xboole_0('#skF_4', B_171))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_13522])).
% 8.75/3.39  tff(c_13813, plain, (k2_xboole_0('#skF_1', '#skF_4')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11186, c_13722])).
% 8.75/3.39  tff(c_14394, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14303, c_13813])).
% 8.75/3.39  tff(c_2521, plain, (![A_86, B_87]: (k4_xboole_0(k2_xboole_0(A_86, B_87), A_86)=k4_xboole_0(B_87, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1564])).
% 8.75/3.39  tff(c_2612, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_2521])).
% 8.75/3.39  tff(c_14543, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14394, c_14394, c_2612])).
% 8.75/3.39  tff(c_14574, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_369, c_14543])).
% 8.75/3.39  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.75/3.39  tff(c_14324, plain, (k4_xboole_0('#skF_4', '#skF_1')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14263, c_22])).
% 8.75/3.39  tff(c_14338, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9909, c_14324])).
% 8.75/3.39  tff(c_167, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.75/3.39  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.75/3.39  tff(c_208, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | k3_xboole_0(A_38, B_37)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_8])).
% 8.75/3.39  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.75/3.39  tff(c_214, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k1_xboole_0 | k3_xboole_0(A_38, B_37)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_208, c_4])).
% 8.75/3.39  tff(c_14645, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14338, c_214])).
% 8.75/3.39  tff(c_2900, plain, (![A_23, B_24]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(k1_xboole_0, A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2769])).
% 8.75/3.39  tff(c_2955, plain, (![A_23, B_24]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2900])).
% 8.75/3.39  tff(c_15079, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_14645, c_2955])).
% 8.75/3.39  tff(c_15104, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14574, c_15079])).
% 8.75/3.39  tff(c_15106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_15104])).
% 8.75/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/3.39  
% 8.75/3.39  Inference rules
% 8.75/3.39  ----------------------
% 8.75/3.39  #Ref     : 0
% 8.75/3.39  #Sup     : 3839
% 8.75/3.39  #Fact    : 0
% 8.75/3.39  #Define  : 0
% 8.75/3.39  #Split   : 2
% 8.75/3.39  #Chain   : 0
% 8.75/3.39  #Close   : 0
% 8.75/3.39  
% 8.75/3.39  Ordering : KBO
% 8.75/3.39  
% 8.75/3.39  Simplification rules
% 8.75/3.39  ----------------------
% 8.75/3.39  #Subsume      : 71
% 8.75/3.39  #Demod        : 4336
% 8.75/3.39  #Tautology    : 2301
% 8.75/3.39  #SimpNegUnit  : 2
% 8.75/3.39  #BackRed      : 44
% 8.75/3.39  
% 8.75/3.39  #Partial instantiations: 0
% 8.75/3.39  #Strategies tried      : 1
% 8.75/3.39  
% 8.75/3.39  Timing (in seconds)
% 8.75/3.39  ----------------------
% 8.75/3.39  Preprocessing        : 0.28
% 8.75/3.39  Parsing              : 0.15
% 8.75/3.39  CNF conversion       : 0.02
% 8.75/3.39  Main loop            : 2.25
% 8.75/3.39  Inferencing          : 0.45
% 8.75/3.39  Reduction            : 1.32
% 8.75/3.39  Demodulation         : 1.18
% 8.75/3.39  BG Simplification    : 0.06
% 8.75/3.39  Subsumption          : 0.31
% 8.75/3.39  Abstraction          : 0.09
% 8.75/3.39  MUC search           : 0.00
% 8.75/3.39  Cooper               : 0.00
% 8.75/3.39  Total                : 2.58
% 8.75/3.39  Index Insertion      : 0.00
% 8.75/3.39  Index Deletion       : 0.00
% 8.75/3.39  Index Matching       : 0.00
% 8.75/3.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

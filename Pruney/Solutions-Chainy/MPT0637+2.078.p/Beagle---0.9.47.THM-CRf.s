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
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 27.18s
% Output     : CNFRefutation 27.34s
% Verified   : 
% Statistics : Number of formulae       :  140 (1173 expanded)
%              Number of leaves         :   35 ( 435 expanded)
%              Depth                    :   22
%              Number of atoms          :  242 (1890 expanded)
%              Number of equality atoms :   93 ( 761 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_84,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = k8_relat_1(A_17,B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_178,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_203,plain,(
    ! [A_17,A_65] :
      ( k8_relat_1(A_17,k6_relat_1(A_65)) = k7_relat_1(k6_relat_1(A_17),A_65)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_222,plain,(
    ! [A_17,A_65] : k8_relat_1(A_17,k6_relat_1(A_65)) = k7_relat_1(k6_relat_1(A_17),A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_203])).

tff(c_303,plain,(
    ! [B_73,A_74] :
      ( k3_xboole_0(B_73,k2_zfmisc_1(k1_relat_1(B_73),A_74)) = k8_relat_1(A_74,B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_363,plain,(
    ! [A_82,B_83] :
      ( v1_relat_1(k8_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_12])).

tff(c_369,plain,(
    ! [A_17,A_65] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_17),A_65))
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_363])).

tff(c_374,plain,(
    ! [A_17,A_65] : v1_relat_1(k7_relat_1(k6_relat_1(A_17),A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_369])).

tff(c_26,plain,(
    ! [A_34] : k1_relat_1(k6_relat_1(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_73,plain,(
    ! [A_52] :
      ( k7_relat_1(A_52,k1_relat_1(A_52)) = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_82,plain,(
    ! [A_34] :
      ( k7_relat_1(k6_relat_1(A_34),A_34) = k6_relat_1(A_34)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_73])).

tff(c_86,plain,(
    ! [A_34] : k7_relat_1(k6_relat_1(A_34),A_34) = k6_relat_1(A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_283,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(k1_relat_1(B_71),A_72) = k1_relat_1(k7_relat_1(B_71,A_72))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_298,plain,(
    ! [A_34,A_72] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_34),A_72)) = k3_xboole_0(A_34,A_72)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_283])).

tff(c_387,plain,(
    ! [A_86,A_87] : k1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) = k3_xboole_0(A_86,A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_298])).

tff(c_405,plain,(
    ! [A_34] : k3_xboole_0(A_34,A_34) = k1_relat_1(k6_relat_1(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_387])).

tff(c_418,plain,(
    ! [A_34] : k3_xboole_0(A_34,A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_405])).

tff(c_302,plain,(
    ! [A_34,A_72] : k1_relat_1(k7_relat_1(k6_relat_1(A_34),A_72)) = k3_xboole_0(A_34,A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_298])).

tff(c_30,plain,(
    ! [A_35] : k4_relat_1(k6_relat_1(A_35)) = k6_relat_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_518,plain,(
    ! [B_96,A_97] :
      ( k5_relat_1(k4_relat_1(B_96),k4_relat_1(A_97)) = k4_relat_1(k5_relat_1(A_97,B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_533,plain,(
    ! [B_96,A_35] :
      ( k5_relat_1(k4_relat_1(B_96),k6_relat_1(A_35)) = k4_relat_1(k5_relat_1(k6_relat_1(A_35),B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_518])).

tff(c_1686,plain,(
    ! [B_155,A_156] :
      ( k5_relat_1(k4_relat_1(B_155),k6_relat_1(A_156)) = k4_relat_1(k5_relat_1(k6_relat_1(A_156),B_155))
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_533])).

tff(c_1728,plain,(
    ! [A_156,A_35] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_156),k6_relat_1(A_35))) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_156))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1686])).

tff(c_1868,plain,(
    ! [A_164,A_165] : k4_relat_1(k5_relat_1(k6_relat_1(A_164),k6_relat_1(A_165))) = k5_relat_1(k6_relat_1(A_165),k6_relat_1(A_164)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1728])).

tff(c_1894,plain,(
    ! [A_17,A_164] :
      ( k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_164)) = k4_relat_1(k8_relat_1(A_17,k6_relat_1(A_164)))
      | ~ v1_relat_1(k6_relat_1(A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1868])).

tff(c_2690,plain,(
    ! [A_190,A_191] : k5_relat_1(k6_relat_1(A_190),k6_relat_1(A_191)) = k4_relat_1(k7_relat_1(k6_relat_1(A_190),A_191)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_1894])).

tff(c_38,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(k6_relat_1(A_41),B_42) = k7_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2714,plain,(
    ! [A_190,A_191] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_190),A_191)) = k7_relat_1(k6_relat_1(A_191),A_190)
      | ~ v1_relat_1(k6_relat_1(A_191)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2690,c_38])).

tff(c_2758,plain,(
    ! [A_190,A_191] : k4_relat_1(k7_relat_1(k6_relat_1(A_190),A_191)) = k7_relat_1(k6_relat_1(A_191),A_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2714])).

tff(c_1908,plain,(
    ! [A_17,A_164] : k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_164)) = k4_relat_1(k7_relat_1(k6_relat_1(A_17),A_164)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_1894])).

tff(c_2818,plain,(
    ! [A_17,A_164] : k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_164)) = k7_relat_1(k6_relat_1(A_164),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_1908])).

tff(c_665,plain,(
    ! [B_105,C_106,A_107] :
      ( k7_relat_1(k5_relat_1(B_105,C_106),A_107) = k5_relat_1(k7_relat_1(B_105,A_107),C_106)
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_694,plain,(
    ! [B_18,A_107,A_17] :
      ( k5_relat_1(k7_relat_1(B_18,A_107),k6_relat_1(A_17)) = k7_relat_1(k8_relat_1(A_17,B_18),A_107)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_665])).

tff(c_2867,plain,(
    ! [B_196,A_197,A_198] :
      ( k5_relat_1(k7_relat_1(B_196,A_197),k6_relat_1(A_198)) = k7_relat_1(k8_relat_1(A_198,B_196),A_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_694])).

tff(c_2940,plain,(
    ! [A_198,A_34] :
      ( k7_relat_1(k8_relat_1(A_198,k6_relat_1(A_34)),A_34) = k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_198))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2867])).

tff(c_2967,plain,(
    ! [A_198,A_34] : k7_relat_1(k7_relat_1(k6_relat_1(A_198),A_34),A_34) = k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_198)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_2940])).

tff(c_14946,plain,(
    ! [A_552,A_553] : k7_relat_1(k7_relat_1(k6_relat_1(A_552),A_553),A_553) = k7_relat_1(k6_relat_1(A_552),A_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_2967])).

tff(c_36,plain,(
    ! [B_40,A_39] :
      ( k3_xboole_0(k1_relat_1(B_40),A_39) = k1_relat_1(k7_relat_1(B_40,A_39))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_34] : k2_relat_1(k6_relat_1(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,(
    ! [B_80,A_81] :
      ( k5_relat_1(B_80,k6_relat_1(A_81)) = B_80
      | ~ r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_360,plain,(
    ! [A_34,A_81] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_81)) = k6_relat_1(A_34)
      | ~ r1_tarski(A_34,A_81)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_357])).

tff(c_733,plain,(
    ! [A_110,A_111] :
      ( k5_relat_1(k6_relat_1(A_110),k6_relat_1(A_111)) = k6_relat_1(A_110)
      | ~ r1_tarski(A_110,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_360])).

tff(c_773,plain,(
    ! [A_17,A_110] :
      ( k8_relat_1(A_17,k6_relat_1(A_110)) = k6_relat_1(A_110)
      | ~ r1_tarski(A_110,A_17)
      | ~ v1_relat_1(k6_relat_1(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_733])).

tff(c_810,plain,(
    ! [A_112,A_113] :
      ( k7_relat_1(k6_relat_1(A_112),A_113) = k6_relat_1(A_113)
      | ~ r1_tarski(A_113,A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_773])).

tff(c_829,plain,(
    ! [A_112,A_113] :
      ( k3_xboole_0(A_112,A_113) = k1_relat_1(k6_relat_1(A_113))
      | ~ r1_tarski(A_113,A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_302])).

tff(c_878,plain,(
    ! [A_114,A_115] :
      ( k3_xboole_0(A_114,A_115) = A_115
      | ~ r1_tarski(A_115,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_829])).

tff(c_920,plain,(
    ! [A_116,B_117] : k3_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(resolution,[status(thm)],[c_2,c_878])).

tff(c_954,plain,(
    ! [B_40,A_39] :
      ( k3_xboole_0(k1_relat_1(B_40),k1_relat_1(k7_relat_1(B_40,A_39))) = k3_xboole_0(k1_relat_1(B_40),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_920])).

tff(c_15011,plain,(
    ! [A_552,A_553] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_552),A_553)),k1_relat_1(k7_relat_1(k6_relat_1(A_552),A_553))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_552),A_553)),A_553)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_552),A_553)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14946,c_954])).

tff(c_15076,plain,(
    ! [A_552,A_553] : k3_xboole_0(k3_xboole_0(A_552,A_553),A_553) = k3_xboole_0(A_552,A_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_418,c_302,c_302,c_302,c_15011])).

tff(c_362,plain,(
    ! [A_34,A_81] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_81)) = k6_relat_1(A_34)
      | ~ r1_tarski(A_34,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_360])).

tff(c_1886,plain,(
    ! [A_81,A_34] :
      ( k5_relat_1(k6_relat_1(A_81),k6_relat_1(A_34)) = k4_relat_1(k6_relat_1(A_34))
      | ~ r1_tarski(A_34,A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_1868])).

tff(c_1912,plain,(
    ! [A_166,A_167] :
      ( k5_relat_1(k6_relat_1(A_166),k6_relat_1(A_167)) = k6_relat_1(A_167)
      | ~ r1_tarski(A_167,A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1886])).

tff(c_1942,plain,(
    ! [A_167,A_166] :
      ( k7_relat_1(k6_relat_1(A_167),A_166) = k6_relat_1(A_167)
      | ~ v1_relat_1(k6_relat_1(A_167))
      | ~ r1_tarski(A_167,A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1912,c_38])).

tff(c_2011,plain,(
    ! [A_168,A_169] :
      ( k7_relat_1(k6_relat_1(A_168),A_169) = k6_relat_1(A_168)
      | ~ r1_tarski(A_168,A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1942])).

tff(c_2057,plain,(
    ! [A_168,A_169] :
      ( k3_xboole_0(A_168,A_169) = k1_relat_1(k6_relat_1(A_168))
      | ~ r1_tarski(A_168,A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_302])).

tff(c_2122,plain,(
    ! [A_170,A_171] :
      ( k3_xboole_0(A_170,A_171) = A_170
      | ~ r1_tarski(A_170,A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2057])).

tff(c_2179,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_2122])).

tff(c_40,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_399,plain,(
    ! [A_86,A_87] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_86),A_87),k3_xboole_0(A_86,A_87)) = k7_relat_1(k6_relat_1(A_86),A_87)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_40])).

tff(c_416,plain,(
    ! [A_86,A_87] : k7_relat_1(k7_relat_1(k6_relat_1(A_86),A_87),k3_xboole_0(A_86,A_87)) = k7_relat_1(k6_relat_1(A_86),A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_399])).

tff(c_20,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_21,B_23)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7798,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_377,B_378))),k2_relat_1(k4_relat_1(A_377)))
      | ~ v1_relat_1(k4_relat_1(A_377))
      | ~ v1_relat_1(k4_relat_1(B_378))
      | ~ v1_relat_1(B_378)
      | ~ v1_relat_1(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_20])).

tff(c_7870,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(B_42,A_41))),k2_relat_1(k4_relat_1(k6_relat_1(A_41))))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_41)))
      | ~ v1_relat_1(k4_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_7798])).

tff(c_21374,plain,(
    ! [B_652,A_653] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(B_652,A_653))),A_653)
      | ~ v1_relat_1(k4_relat_1(B_652))
      | ~ v1_relat_1(B_652) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_30,c_28,c_30,c_7870])).

tff(c_21503,plain,(
    ! [A_86,A_87] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_86),A_87))),k3_xboole_0(A_86,A_87))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_21374])).

tff(c_21581,plain,(
    ! [A_654,A_655] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_654),A_655)),k3_xboole_0(A_655,A_654)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_2758,c_2758,c_21503])).

tff(c_802,plain,(
    ! [A_17,A_110] :
      ( k7_relat_1(k6_relat_1(A_17),A_110) = k6_relat_1(A_110)
      | ~ r1_tarski(A_110,A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_773])).

tff(c_691,plain,(
    ! [A_41,A_107,B_42] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_41),A_107),B_42) = k7_relat_1(k7_relat_1(B_42,A_41),A_107)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_665])).

tff(c_2435,plain,(
    ! [A_180,A_181,B_182] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_180),A_181),B_182) = k7_relat_1(k7_relat_1(B_182,A_180),A_181)
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_691])).

tff(c_451,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_90,B_91)),k2_relat_1(B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_469,plain,(
    ! [A_90,A_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_90,k6_relat_1(A_34))),A_34)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_451])).

tff(c_480,plain,(
    ! [A_90,A_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_90,k6_relat_1(A_34))),A_34)
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_469])).

tff(c_2463,plain,(
    ! [A_34,A_180,A_181] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_34),A_180),A_181)),A_34)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_180),A_181))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_480])).

tff(c_2538,plain,(
    ! [A_183,A_184,A_185] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_183),A_184),A_185)),A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_374,c_2463])).

tff(c_3287,plain,(
    ! [A_204,A_205,A_206] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_204),A_205)),A_206)
      | ~ r1_tarski(A_204,A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_2538])).

tff(c_3309,plain,(
    ! [A_110,A_206,A_17] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_110)),A_206)
      | ~ r1_tarski(A_17,A_206)
      | ~ r1_tarski(A_110,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_3287])).

tff(c_3453,plain,(
    ! [A_209,A_210,A_211] :
      ( r1_tarski(A_209,A_210)
      | ~ r1_tarski(A_211,A_210)
      | ~ r1_tarski(A_209,A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3309])).

tff(c_3507,plain,(
    ! [A_209,A_1,B_2] :
      ( r1_tarski(A_209,A_1)
      | ~ r1_tarski(A_209,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_3453])).

tff(c_21743,plain,(
    ! [A_656,A_657] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_656),A_657)),A_657) ),
    inference(resolution,[status(thm)],[c_21581,c_3507])).

tff(c_32,plain,(
    ! [B_37,A_36] :
      ( k5_relat_1(B_37,k6_relat_1(A_36)) = B_37
      | ~ r1_tarski(k2_relat_1(B_37),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_21869,plain,(
    ! [A_656,A_657] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_656),A_657),k6_relat_1(A_657)) = k7_relat_1(k6_relat_1(A_656),A_657)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_656),A_657)) ) ),
    inference(resolution,[status(thm)],[c_21743,c_32])).

tff(c_30587,plain,(
    ! [A_801,A_802] : k5_relat_1(k7_relat_1(k6_relat_1(A_801),A_802),k6_relat_1(A_802)) = k7_relat_1(k6_relat_1(A_801),A_802) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_21869])).

tff(c_710,plain,(
    ! [B_18,A_107,A_17] :
      ( k5_relat_1(k7_relat_1(B_18,A_107),k6_relat_1(A_17)) = k7_relat_1(k8_relat_1(A_17,B_18),A_107)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_694])).

tff(c_30632,plain,(
    ! [A_802,A_801] :
      ( k7_relat_1(k8_relat_1(A_802,k6_relat_1(A_801)),A_802) = k7_relat_1(k6_relat_1(A_801),A_802)
      | ~ v1_relat_1(k6_relat_1(A_801)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30587,c_710])).

tff(c_30782,plain,(
    ! [A_803,A_804] : k7_relat_1(k7_relat_1(k6_relat_1(A_803),A_804),A_803) = k7_relat_1(k6_relat_1(A_804),A_803) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_222,c_30632])).

tff(c_15093,plain,(
    ! [A_554,A_555] : k3_xboole_0(k3_xboole_0(A_554,A_555),A_555) = k3_xboole_0(A_554,A_555) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_418,c_302,c_302,c_302,c_15011])).

tff(c_15305,plain,(
    ! [B_40,A_39] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_40,A_39)),A_39) = k3_xboole_0(k1_relat_1(B_40),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15093])).

tff(c_30828,plain,(
    ! [A_804,A_803] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_804),A_803)),A_803) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_803),A_804)),A_803)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_803),A_804)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30782,c_15305])).

tff(c_31003,plain,(
    ! [A_806,A_805] : k3_xboole_0(A_806,A_805) = k3_xboole_0(A_805,A_806) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_15076,c_2179,c_302,c_302,c_30828])).

tff(c_31917,plain,(
    ! [A_805,A_806] : r1_tarski(k3_xboole_0(A_805,A_806),A_806) ),
    inference(superposition,[status(thm),theory(equality)],[c_31003,c_2])).

tff(c_6837,plain,(
    ! [B_345,C_346] :
      ( k5_relat_1(k7_relat_1(B_345,k1_relat_1(k5_relat_1(B_345,C_346))),C_346) = k5_relat_1(B_345,C_346)
      | ~ v1_relat_1(C_346)
      | ~ v1_relat_1(B_345)
      | ~ v1_relat_1(k5_relat_1(B_345,C_346)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_665])).

tff(c_6998,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(k7_relat_1(B_18,k1_relat_1(k8_relat_1(A_17,B_18))),k6_relat_1(A_17)) = k5_relat_1(B_18,k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(k5_relat_1(B_18,k6_relat_1(A_17)))
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6837])).

tff(c_84675,plain,(
    ! [B_1371,A_1372] :
      ( k5_relat_1(k7_relat_1(B_1371,k1_relat_1(k8_relat_1(A_1372,B_1371))),k6_relat_1(A_1372)) = k5_relat_1(B_1371,k6_relat_1(A_1372))
      | ~ v1_relat_1(k5_relat_1(B_1371,k6_relat_1(A_1372)))
      | ~ v1_relat_1(B_1371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6998])).

tff(c_84915,plain,(
    ! [A_1372,A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(A_1372,k6_relat_1(A_17)))),k6_relat_1(A_1372)) = k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_1372))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_17),k6_relat_1(A_1372)))
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ r1_tarski(k1_relat_1(k8_relat_1(A_1372,k6_relat_1(A_17))),A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_84675])).

tff(c_100783,plain,(
    ! [A_1495,A_1496] : k7_relat_1(k6_relat_1(A_1495),k3_xboole_0(A_1495,A_1496)) = k7_relat_1(k6_relat_1(A_1495),A_1496) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31917,c_302,c_222,c_10,c_374,c_2818,c_2818,c_2818,c_302,c_222,c_84915])).

tff(c_101392,plain,(
    ! [A_1495,A_1496] :
      ( k7_relat_1(k6_relat_1(A_1495),A_1496) = k6_relat_1(k3_xboole_0(A_1495,A_1496))
      | ~ r1_tarski(k3_xboole_0(A_1495,A_1496),A_1495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100783,c_802])).

tff(c_101737,plain,(
    ! [A_1495,A_1496] : k7_relat_1(k6_relat_1(A_1495),A_1496) = k6_relat_1(k3_xboole_0(A_1495,A_1496)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101392])).

tff(c_42,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_196,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_42])).

tff(c_219,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_196])).

tff(c_102029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101737,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.18/17.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.18/17.91  
% 27.18/17.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.18/17.91  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 27.18/17.91  
% 27.18/17.91  %Foreground sorts:
% 27.18/17.91  
% 27.18/17.91  
% 27.18/17.91  %Background operators:
% 27.18/17.91  
% 27.18/17.91  
% 27.18/17.91  %Foreground operators:
% 27.18/17.91  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 27.18/17.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.18/17.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.18/17.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 27.18/17.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.18/17.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.18/17.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.18/17.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.18/17.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.18/17.91  tff('#skF_2', type, '#skF_2': $i).
% 27.18/17.91  tff('#skF_1', type, '#skF_1': $i).
% 27.18/17.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.18/17.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.18/17.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.18/17.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 27.18/17.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.18/17.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.18/17.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.18/17.91  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 27.18/17.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.18/17.91  
% 27.34/17.94  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.34/17.94  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 27.34/17.94  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 27.34/17.94  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 27.34/17.94  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 27.34/17.94  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 27.34/17.94  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 27.34/17.94  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 27.34/17.94  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 27.34/17.94  tff(f_84, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 27.34/17.94  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 27.34/17.94  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 27.34/17.94  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 27.34/17.94  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 27.34/17.94  tff(f_109, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 27.34/17.94  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.34/17.94  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.34/17.94  tff(c_16, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=k8_relat_1(A_17, B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.34/17.94  tff(c_178, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.34/17.94  tff(c_203, plain, (![A_17, A_65]: (k8_relat_1(A_17, k6_relat_1(A_65))=k7_relat_1(k6_relat_1(A_17), A_65) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_178])).
% 27.34/17.94  tff(c_222, plain, (![A_17, A_65]: (k8_relat_1(A_17, k6_relat_1(A_65))=k7_relat_1(k6_relat_1(A_17), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_203])).
% 27.34/17.94  tff(c_303, plain, (![B_73, A_74]: (k3_xboole_0(B_73, k2_zfmisc_1(k1_relat_1(B_73), A_74))=k8_relat_1(A_74, B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.34/17.94  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k3_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.34/17.94  tff(c_363, plain, (![A_82, B_83]: (v1_relat_1(k8_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_303, c_12])).
% 27.34/17.94  tff(c_369, plain, (![A_17, A_65]: (v1_relat_1(k7_relat_1(k6_relat_1(A_17), A_65)) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_363])).
% 27.34/17.94  tff(c_374, plain, (![A_17, A_65]: (v1_relat_1(k7_relat_1(k6_relat_1(A_17), A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_369])).
% 27.34/17.94  tff(c_26, plain, (![A_34]: (k1_relat_1(k6_relat_1(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.34/17.94  tff(c_73, plain, (![A_52]: (k7_relat_1(A_52, k1_relat_1(A_52))=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.34/17.94  tff(c_82, plain, (![A_34]: (k7_relat_1(k6_relat_1(A_34), A_34)=k6_relat_1(A_34) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_73])).
% 27.34/17.94  tff(c_86, plain, (![A_34]: (k7_relat_1(k6_relat_1(A_34), A_34)=k6_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_82])).
% 27.34/17.94  tff(c_283, plain, (![B_71, A_72]: (k3_xboole_0(k1_relat_1(B_71), A_72)=k1_relat_1(k7_relat_1(B_71, A_72)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/17.94  tff(c_298, plain, (![A_34, A_72]: (k1_relat_1(k7_relat_1(k6_relat_1(A_34), A_72))=k3_xboole_0(A_34, A_72) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_283])).
% 27.34/17.94  tff(c_387, plain, (![A_86, A_87]: (k1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87))=k3_xboole_0(A_86, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_298])).
% 27.34/17.94  tff(c_405, plain, (![A_34]: (k3_xboole_0(A_34, A_34)=k1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_387])).
% 27.34/17.94  tff(c_418, plain, (![A_34]: (k3_xboole_0(A_34, A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_405])).
% 27.34/17.94  tff(c_302, plain, (![A_34, A_72]: (k1_relat_1(k7_relat_1(k6_relat_1(A_34), A_72))=k3_xboole_0(A_34, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_298])).
% 27.34/17.94  tff(c_30, plain, (![A_35]: (k4_relat_1(k6_relat_1(A_35))=k6_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.34/17.94  tff(c_518, plain, (![B_96, A_97]: (k5_relat_1(k4_relat_1(B_96), k4_relat_1(A_97))=k4_relat_1(k5_relat_1(A_97, B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.34/17.94  tff(c_533, plain, (![B_96, A_35]: (k5_relat_1(k4_relat_1(B_96), k6_relat_1(A_35))=k4_relat_1(k5_relat_1(k6_relat_1(A_35), B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_518])).
% 27.34/17.94  tff(c_1686, plain, (![B_155, A_156]: (k5_relat_1(k4_relat_1(B_155), k6_relat_1(A_156))=k4_relat_1(k5_relat_1(k6_relat_1(A_156), B_155)) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_533])).
% 27.34/17.94  tff(c_1728, plain, (![A_156, A_35]: (k4_relat_1(k5_relat_1(k6_relat_1(A_156), k6_relat_1(A_35)))=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_156)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1686])).
% 27.34/17.94  tff(c_1868, plain, (![A_164, A_165]: (k4_relat_1(k5_relat_1(k6_relat_1(A_164), k6_relat_1(A_165)))=k5_relat_1(k6_relat_1(A_165), k6_relat_1(A_164)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1728])).
% 27.34/17.94  tff(c_1894, plain, (![A_17, A_164]: (k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_164))=k4_relat_1(k8_relat_1(A_17, k6_relat_1(A_164))) | ~v1_relat_1(k6_relat_1(A_164)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1868])).
% 27.34/17.94  tff(c_2690, plain, (![A_190, A_191]: (k5_relat_1(k6_relat_1(A_190), k6_relat_1(A_191))=k4_relat_1(k7_relat_1(k6_relat_1(A_190), A_191)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_1894])).
% 27.34/17.94  tff(c_38, plain, (![A_41, B_42]: (k5_relat_1(k6_relat_1(A_41), B_42)=k7_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.34/17.94  tff(c_2714, plain, (![A_190, A_191]: (k4_relat_1(k7_relat_1(k6_relat_1(A_190), A_191))=k7_relat_1(k6_relat_1(A_191), A_190) | ~v1_relat_1(k6_relat_1(A_191)))), inference(superposition, [status(thm), theory('equality')], [c_2690, c_38])).
% 27.34/17.94  tff(c_2758, plain, (![A_190, A_191]: (k4_relat_1(k7_relat_1(k6_relat_1(A_190), A_191))=k7_relat_1(k6_relat_1(A_191), A_190))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2714])).
% 27.34/17.94  tff(c_1908, plain, (![A_17, A_164]: (k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_164))=k4_relat_1(k7_relat_1(k6_relat_1(A_17), A_164)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_1894])).
% 27.34/17.94  tff(c_2818, plain, (![A_17, A_164]: (k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_164))=k7_relat_1(k6_relat_1(A_164), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_2758, c_1908])).
% 27.34/17.94  tff(c_665, plain, (![B_105, C_106, A_107]: (k7_relat_1(k5_relat_1(B_105, C_106), A_107)=k5_relat_1(k7_relat_1(B_105, A_107), C_106) | ~v1_relat_1(C_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.34/17.94  tff(c_694, plain, (![B_18, A_107, A_17]: (k5_relat_1(k7_relat_1(B_18, A_107), k6_relat_1(A_17))=k7_relat_1(k8_relat_1(A_17, B_18), A_107) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_665])).
% 27.34/17.94  tff(c_2867, plain, (![B_196, A_197, A_198]: (k5_relat_1(k7_relat_1(B_196, A_197), k6_relat_1(A_198))=k7_relat_1(k8_relat_1(A_198, B_196), A_197) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_694])).
% 27.34/17.94  tff(c_2940, plain, (![A_198, A_34]: (k7_relat_1(k8_relat_1(A_198, k6_relat_1(A_34)), A_34)=k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_198)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_2867])).
% 27.34/17.94  tff(c_2967, plain, (![A_198, A_34]: (k7_relat_1(k7_relat_1(k6_relat_1(A_198), A_34), A_34)=k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_198)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_2940])).
% 27.34/17.94  tff(c_14946, plain, (![A_552, A_553]: (k7_relat_1(k7_relat_1(k6_relat_1(A_552), A_553), A_553)=k7_relat_1(k6_relat_1(A_552), A_553))), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_2967])).
% 27.34/17.94  tff(c_36, plain, (![B_40, A_39]: (k3_xboole_0(k1_relat_1(B_40), A_39)=k1_relat_1(k7_relat_1(B_40, A_39)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.34/17.94  tff(c_28, plain, (![A_34]: (k2_relat_1(k6_relat_1(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.34/17.94  tff(c_357, plain, (![B_80, A_81]: (k5_relat_1(B_80, k6_relat_1(A_81))=B_80 | ~r1_tarski(k2_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_90])).
% 27.34/17.94  tff(c_360, plain, (![A_34, A_81]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_81))=k6_relat_1(A_34) | ~r1_tarski(A_34, A_81) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_357])).
% 27.34/17.94  tff(c_733, plain, (![A_110, A_111]: (k5_relat_1(k6_relat_1(A_110), k6_relat_1(A_111))=k6_relat_1(A_110) | ~r1_tarski(A_110, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_360])).
% 27.34/17.94  tff(c_773, plain, (![A_17, A_110]: (k8_relat_1(A_17, k6_relat_1(A_110))=k6_relat_1(A_110) | ~r1_tarski(A_110, A_17) | ~v1_relat_1(k6_relat_1(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_733])).
% 27.34/17.94  tff(c_810, plain, (![A_112, A_113]: (k7_relat_1(k6_relat_1(A_112), A_113)=k6_relat_1(A_113) | ~r1_tarski(A_113, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_773])).
% 27.34/17.94  tff(c_829, plain, (![A_112, A_113]: (k3_xboole_0(A_112, A_113)=k1_relat_1(k6_relat_1(A_113)) | ~r1_tarski(A_113, A_112))), inference(superposition, [status(thm), theory('equality')], [c_810, c_302])).
% 27.34/17.94  tff(c_878, plain, (![A_114, A_115]: (k3_xboole_0(A_114, A_115)=A_115 | ~r1_tarski(A_115, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_829])).
% 27.34/17.94  tff(c_920, plain, (![A_116, B_117]: (k3_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(resolution, [status(thm)], [c_2, c_878])).
% 27.34/17.94  tff(c_954, plain, (![B_40, A_39]: (k3_xboole_0(k1_relat_1(B_40), k1_relat_1(k7_relat_1(B_40, A_39)))=k3_xboole_0(k1_relat_1(B_40), A_39) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_36, c_920])).
% 27.34/17.94  tff(c_15011, plain, (![A_552, A_553]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_552), A_553)), k1_relat_1(k7_relat_1(k6_relat_1(A_552), A_553)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_552), A_553)), A_553) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_552), A_553)))), inference(superposition, [status(thm), theory('equality')], [c_14946, c_954])).
% 27.34/17.94  tff(c_15076, plain, (![A_552, A_553]: (k3_xboole_0(k3_xboole_0(A_552, A_553), A_553)=k3_xboole_0(A_552, A_553))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_418, c_302, c_302, c_302, c_15011])).
% 27.34/17.94  tff(c_362, plain, (![A_34, A_81]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_81))=k6_relat_1(A_34) | ~r1_tarski(A_34, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_360])).
% 27.34/17.94  tff(c_1886, plain, (![A_81, A_34]: (k5_relat_1(k6_relat_1(A_81), k6_relat_1(A_34))=k4_relat_1(k6_relat_1(A_34)) | ~r1_tarski(A_34, A_81))), inference(superposition, [status(thm), theory('equality')], [c_362, c_1868])).
% 27.34/17.94  tff(c_1912, plain, (![A_166, A_167]: (k5_relat_1(k6_relat_1(A_166), k6_relat_1(A_167))=k6_relat_1(A_167) | ~r1_tarski(A_167, A_166))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1886])).
% 27.34/17.94  tff(c_1942, plain, (![A_167, A_166]: (k7_relat_1(k6_relat_1(A_167), A_166)=k6_relat_1(A_167) | ~v1_relat_1(k6_relat_1(A_167)) | ~r1_tarski(A_167, A_166))), inference(superposition, [status(thm), theory('equality')], [c_1912, c_38])).
% 27.34/17.94  tff(c_2011, plain, (![A_168, A_169]: (k7_relat_1(k6_relat_1(A_168), A_169)=k6_relat_1(A_168) | ~r1_tarski(A_168, A_169))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1942])).
% 27.34/17.94  tff(c_2057, plain, (![A_168, A_169]: (k3_xboole_0(A_168, A_169)=k1_relat_1(k6_relat_1(A_168)) | ~r1_tarski(A_168, A_169))), inference(superposition, [status(thm), theory('equality')], [c_2011, c_302])).
% 27.34/17.94  tff(c_2122, plain, (![A_170, A_171]: (k3_xboole_0(A_170, A_171)=A_170 | ~r1_tarski(A_170, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2057])).
% 27.34/17.94  tff(c_2179, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_2122])).
% 27.34/17.94  tff(c_40, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.34/17.94  tff(c_399, plain, (![A_86, A_87]: (k7_relat_1(k7_relat_1(k6_relat_1(A_86), A_87), k3_xboole_0(A_86, A_87))=k7_relat_1(k6_relat_1(A_86), A_87) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)))), inference(superposition, [status(thm), theory('equality')], [c_387, c_40])).
% 27.34/17.94  tff(c_416, plain, (![A_86, A_87]: (k7_relat_1(k7_relat_1(k6_relat_1(A_86), A_87), k3_xboole_0(A_86, A_87))=k7_relat_1(k6_relat_1(A_86), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_399])).
% 27.34/17.94  tff(c_20, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(k5_relat_1(A_21, B_23)), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.34/17.94  tff(c_7798, plain, (![A_377, B_378]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_377, B_378))), k2_relat_1(k4_relat_1(A_377))) | ~v1_relat_1(k4_relat_1(A_377)) | ~v1_relat_1(k4_relat_1(B_378)) | ~v1_relat_1(B_378) | ~v1_relat_1(A_377))), inference(superposition, [status(thm), theory('equality')], [c_518, c_20])).
% 27.34/17.94  tff(c_7870, plain, (![B_42, A_41]: (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(B_42, A_41))), k2_relat_1(k4_relat_1(k6_relat_1(A_41)))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_41))) | ~v1_relat_1(k4_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_38, c_7798])).
% 27.34/17.94  tff(c_21374, plain, (![B_652, A_653]: (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(B_652, A_653))), A_653) | ~v1_relat_1(k4_relat_1(B_652)) | ~v1_relat_1(B_652))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_30, c_28, c_30, c_7870])).
% 27.34/17.94  tff(c_21503, plain, (![A_86, A_87]: (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_86), A_87))), k3_xboole_0(A_86, A_87)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_86), A_87))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)))), inference(superposition, [status(thm), theory('equality')], [c_416, c_21374])).
% 27.34/17.94  tff(c_21581, plain, (![A_654, A_655]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_654), A_655)), k3_xboole_0(A_655, A_654)))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_374, c_2758, c_2758, c_21503])).
% 27.34/17.94  tff(c_802, plain, (![A_17, A_110]: (k7_relat_1(k6_relat_1(A_17), A_110)=k6_relat_1(A_110) | ~r1_tarski(A_110, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_773])).
% 27.34/17.94  tff(c_691, plain, (![A_41, A_107, B_42]: (k5_relat_1(k7_relat_1(k6_relat_1(A_41), A_107), B_42)=k7_relat_1(k7_relat_1(B_42, A_41), A_107) | ~v1_relat_1(B_42) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_38, c_665])).
% 27.34/17.94  tff(c_2435, plain, (![A_180, A_181, B_182]: (k5_relat_1(k7_relat_1(k6_relat_1(A_180), A_181), B_182)=k7_relat_1(k7_relat_1(B_182, A_180), A_181) | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_691])).
% 27.34/17.94  tff(c_451, plain, (![A_90, B_91]: (r1_tarski(k2_relat_1(k5_relat_1(A_90, B_91)), k2_relat_1(B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.34/17.94  tff(c_469, plain, (![A_90, A_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_90, k6_relat_1(A_34))), A_34) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_28, c_451])).
% 27.34/17.94  tff(c_480, plain, (![A_90, A_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_90, k6_relat_1(A_34))), A_34) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_469])).
% 27.34/17.94  tff(c_2463, plain, (![A_34, A_180, A_181]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_34), A_180), A_181)), A_34) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_180), A_181)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_2435, c_480])).
% 27.34/17.94  tff(c_2538, plain, (![A_183, A_184, A_185]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_183), A_184), A_185)), A_183))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_374, c_2463])).
% 27.34/17.94  tff(c_3287, plain, (![A_204, A_205, A_206]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_204), A_205)), A_206) | ~r1_tarski(A_204, A_206))), inference(superposition, [status(thm), theory('equality')], [c_802, c_2538])).
% 27.34/17.94  tff(c_3309, plain, (![A_110, A_206, A_17]: (r1_tarski(k2_relat_1(k6_relat_1(A_110)), A_206) | ~r1_tarski(A_17, A_206) | ~r1_tarski(A_110, A_17))), inference(superposition, [status(thm), theory('equality')], [c_802, c_3287])).
% 27.34/17.94  tff(c_3453, plain, (![A_209, A_210, A_211]: (r1_tarski(A_209, A_210) | ~r1_tarski(A_211, A_210) | ~r1_tarski(A_209, A_211))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3309])).
% 27.34/17.94  tff(c_3507, plain, (![A_209, A_1, B_2]: (r1_tarski(A_209, A_1) | ~r1_tarski(A_209, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_3453])).
% 27.34/17.94  tff(c_21743, plain, (![A_656, A_657]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_656), A_657)), A_657))), inference(resolution, [status(thm)], [c_21581, c_3507])).
% 27.34/17.94  tff(c_32, plain, (![B_37, A_36]: (k5_relat_1(B_37, k6_relat_1(A_36))=B_37 | ~r1_tarski(k2_relat_1(B_37), A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 27.34/17.94  tff(c_21869, plain, (![A_656, A_657]: (k5_relat_1(k7_relat_1(k6_relat_1(A_656), A_657), k6_relat_1(A_657))=k7_relat_1(k6_relat_1(A_656), A_657) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_656), A_657)))), inference(resolution, [status(thm)], [c_21743, c_32])).
% 27.34/17.94  tff(c_30587, plain, (![A_801, A_802]: (k5_relat_1(k7_relat_1(k6_relat_1(A_801), A_802), k6_relat_1(A_802))=k7_relat_1(k6_relat_1(A_801), A_802))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_21869])).
% 27.34/17.94  tff(c_710, plain, (![B_18, A_107, A_17]: (k5_relat_1(k7_relat_1(B_18, A_107), k6_relat_1(A_17))=k7_relat_1(k8_relat_1(A_17, B_18), A_107) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_694])).
% 27.34/17.94  tff(c_30632, plain, (![A_802, A_801]: (k7_relat_1(k8_relat_1(A_802, k6_relat_1(A_801)), A_802)=k7_relat_1(k6_relat_1(A_801), A_802) | ~v1_relat_1(k6_relat_1(A_801)))), inference(superposition, [status(thm), theory('equality')], [c_30587, c_710])).
% 27.34/17.94  tff(c_30782, plain, (![A_803, A_804]: (k7_relat_1(k7_relat_1(k6_relat_1(A_803), A_804), A_803)=k7_relat_1(k6_relat_1(A_804), A_803))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_222, c_30632])).
% 27.34/17.94  tff(c_15093, plain, (![A_554, A_555]: (k3_xboole_0(k3_xboole_0(A_554, A_555), A_555)=k3_xboole_0(A_554, A_555))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_418, c_302, c_302, c_302, c_15011])).
% 27.34/17.94  tff(c_15305, plain, (![B_40, A_39]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_40, A_39)), A_39)=k3_xboole_0(k1_relat_1(B_40), A_39) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_36, c_15093])).
% 27.34/17.94  tff(c_30828, plain, (![A_804, A_803]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_804), A_803)), A_803)=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_803), A_804)), A_803) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_803), A_804)))), inference(superposition, [status(thm), theory('equality')], [c_30782, c_15305])).
% 27.34/17.94  tff(c_31003, plain, (![A_806, A_805]: (k3_xboole_0(A_806, A_805)=k3_xboole_0(A_805, A_806))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_15076, c_2179, c_302, c_302, c_30828])).
% 27.34/17.94  tff(c_31917, plain, (![A_805, A_806]: (r1_tarski(k3_xboole_0(A_805, A_806), A_806))), inference(superposition, [status(thm), theory('equality')], [c_31003, c_2])).
% 27.34/17.94  tff(c_6837, plain, (![B_345, C_346]: (k5_relat_1(k7_relat_1(B_345, k1_relat_1(k5_relat_1(B_345, C_346))), C_346)=k5_relat_1(B_345, C_346) | ~v1_relat_1(C_346) | ~v1_relat_1(B_345) | ~v1_relat_1(k5_relat_1(B_345, C_346)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_665])).
% 27.34/17.94  tff(c_6998, plain, (![B_18, A_17]: (k5_relat_1(k7_relat_1(B_18, k1_relat_1(k8_relat_1(A_17, B_18))), k6_relat_1(A_17))=k5_relat_1(B_18, k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(k5_relat_1(B_18, k6_relat_1(A_17))) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6837])).
% 27.34/17.94  tff(c_84675, plain, (![B_1371, A_1372]: (k5_relat_1(k7_relat_1(B_1371, k1_relat_1(k8_relat_1(A_1372, B_1371))), k6_relat_1(A_1372))=k5_relat_1(B_1371, k6_relat_1(A_1372)) | ~v1_relat_1(k5_relat_1(B_1371, k6_relat_1(A_1372))) | ~v1_relat_1(B_1371))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6998])).
% 27.34/17.94  tff(c_84915, plain, (![A_1372, A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(A_1372, k6_relat_1(A_17)))), k6_relat_1(A_1372))=k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_1372)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_17), k6_relat_1(A_1372))) | ~v1_relat_1(k6_relat_1(A_17)) | ~r1_tarski(k1_relat_1(k8_relat_1(A_1372, k6_relat_1(A_17))), A_17))), inference(superposition, [status(thm), theory('equality')], [c_802, c_84675])).
% 27.34/17.94  tff(c_100783, plain, (![A_1495, A_1496]: (k7_relat_1(k6_relat_1(A_1495), k3_xboole_0(A_1495, A_1496))=k7_relat_1(k6_relat_1(A_1495), A_1496))), inference(demodulation, [status(thm), theory('equality')], [c_31917, c_302, c_222, c_10, c_374, c_2818, c_2818, c_2818, c_302, c_222, c_84915])).
% 27.34/17.94  tff(c_101392, plain, (![A_1495, A_1496]: (k7_relat_1(k6_relat_1(A_1495), A_1496)=k6_relat_1(k3_xboole_0(A_1495, A_1496)) | ~r1_tarski(k3_xboole_0(A_1495, A_1496), A_1495))), inference(superposition, [status(thm), theory('equality')], [c_100783, c_802])).
% 27.34/17.94  tff(c_101737, plain, (![A_1495, A_1496]: (k7_relat_1(k6_relat_1(A_1495), A_1496)=k6_relat_1(k3_xboole_0(A_1495, A_1496)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_101392])).
% 27.34/17.94  tff(c_42, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 27.34/17.94  tff(c_196, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_42])).
% 27.34/17.94  tff(c_219, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_196])).
% 27.34/17.94  tff(c_102029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101737, c_219])).
% 27.34/17.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.34/17.94  
% 27.34/17.94  Inference rules
% 27.34/17.94  ----------------------
% 27.34/17.94  #Ref     : 0
% 27.34/17.94  #Sup     : 24525
% 27.34/17.94  #Fact    : 0
% 27.34/17.94  #Define  : 0
% 27.34/17.94  #Split   : 2
% 27.34/17.94  #Chain   : 0
% 27.34/17.94  #Close   : 0
% 27.34/17.94  
% 27.34/17.94  Ordering : KBO
% 27.34/17.94  
% 27.34/17.94  Simplification rules
% 27.34/17.94  ----------------------
% 27.34/17.94  #Subsume      : 4383
% 27.34/17.94  #Demod        : 18438
% 27.34/17.94  #Tautology    : 7344
% 27.34/17.94  #SimpNegUnit  : 0
% 27.34/17.94  #BackRed      : 188
% 27.34/17.94  
% 27.34/17.94  #Partial instantiations: 0
% 27.34/17.94  #Strategies tried      : 1
% 27.34/17.94  
% 27.34/17.94  Timing (in seconds)
% 27.34/17.94  ----------------------
% 27.34/17.94  Preprocessing        : 0.31
% 27.34/17.94  Parsing              : 0.16
% 27.34/17.94  CNF conversion       : 0.02
% 27.34/17.94  Main loop            : 16.85
% 27.34/17.94  Inferencing          : 2.29
% 27.34/17.94  Reduction            : 8.07
% 27.34/17.94  Demodulation         : 7.11
% 27.34/17.94  BG Simplification    : 0.30
% 27.34/17.94  Subsumption          : 5.20
% 27.34/17.94  Abstraction          : 0.45
% 27.34/17.94  MUC search           : 0.00
% 27.34/17.94  Cooper               : 0.00
% 27.34/17.94  Total                : 17.21
% 27.34/17.94  Index Insertion      : 0.00
% 27.34/17.94  Index Deletion       : 0.00
% 27.34/17.94  Index Matching       : 0.00
% 27.34/17.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------

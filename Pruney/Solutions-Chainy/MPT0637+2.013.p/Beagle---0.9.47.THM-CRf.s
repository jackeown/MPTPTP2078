%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 9.11s
% Output     : CNFRefutation 9.30s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 699 expanded)
%              Number of leaves         :   32 ( 260 expanded)
%              Depth                    :   25
%              Number of atoms          :  173 (1054 expanded)
%              Number of equality atoms :   93 ( 482 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_83,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_35] : k1_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    ! [A_50] :
      ( k7_relat_1(A_50,k1_relat_1(A_50)) = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_131,plain,(
    ! [A_35] :
      ( k7_relat_1(k6_relat_1(A_35),A_35) = k6_relat_1(A_35)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_122])).

tff(c_135,plain,(
    ! [A_35] : k7_relat_1(k6_relat_1(A_35),A_35) = k6_relat_1(A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_347,plain,(
    ! [C_78,A_79,B_80] :
      ( k7_relat_1(k7_relat_1(C_78,A_79),B_80) = k7_relat_1(C_78,k3_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_382,plain,(
    ! [A_35,B_80] :
      ( k7_relat_1(k6_relat_1(A_35),k3_xboole_0(A_35,B_80)) = k7_relat_1(k6_relat_1(A_35),B_80)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_347])).

tff(c_399,plain,(
    ! [A_35,B_80] : k7_relat_1(k6_relat_1(A_35),k3_xboole_0(A_35,B_80)) = k7_relat_1(k6_relat_1(A_35),B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_382])).

tff(c_32,plain,(
    ! [A_37,B_38] :
      ( k5_relat_1(k6_relat_1(A_37),B_38) = k7_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    ! [B_65,A_66] :
      ( k5_relat_1(B_65,k6_relat_1(A_66)) = k8_relat_1(A_66,B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_260,plain,(
    ! [A_66,A_37] :
      ( k8_relat_1(A_66,k6_relat_1(A_37)) = k7_relat_1(k6_relat_1(A_66),A_37)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_270,plain,(
    ! [A_66,A_37] : k8_relat_1(A_66,k6_relat_1(A_37)) = k7_relat_1(k6_relat_1(A_66),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_260])).

tff(c_298,plain,(
    ! [A_73,C_74,B_75] :
      ( k8_relat_1(A_73,k7_relat_1(C_74,B_75)) = k7_relat_1(k8_relat_1(A_73,C_74),B_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_310,plain,(
    ! [A_73,A_35] :
      ( k7_relat_1(k8_relat_1(A_73,k6_relat_1(A_35)),A_35) = k8_relat_1(A_73,k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_298])).

tff(c_317,plain,(
    ! [A_73,A_35] : k7_relat_1(k7_relat_1(k6_relat_1(A_73),A_35),A_35) = k7_relat_1(k6_relat_1(A_73),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_270,c_270,c_310])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( k5_relat_1(B_21,k6_relat_1(A_20)) = k8_relat_1(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_608,plain,(
    ! [B_90,C_91,A_92] :
      ( k7_relat_1(k5_relat_1(B_90,C_91),A_92) = k5_relat_1(k7_relat_1(B_90,A_92),C_91)
      | ~ v1_relat_1(C_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_633,plain,(
    ! [B_21,A_92,A_20] :
      ( k5_relat_1(k7_relat_1(B_21,A_92),k6_relat_1(A_20)) = k7_relat_1(k8_relat_1(A_20,B_21),A_92)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_608])).

tff(c_1122,plain,(
    ! [B_118,A_119,A_120] :
      ( k5_relat_1(k7_relat_1(B_118,A_119),k6_relat_1(A_120)) = k7_relat_1(k8_relat_1(A_120,B_118),A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_633])).

tff(c_1165,plain,(
    ! [A_120,A_35] :
      ( k7_relat_1(k8_relat_1(A_120,k6_relat_1(A_35)),A_35) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_120))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1122])).

tff(c_1184,plain,(
    ! [A_35,A_120] : k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_120)) = k7_relat_1(k6_relat_1(A_120),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_317,c_270,c_1165])).

tff(c_34,plain,(
    ! [A_39] :
      ( k7_relat_1(A_39,k1_relat_1(A_39)) = A_39
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_636,plain,(
    ! [A_37,A_92,B_38] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_37),A_92),B_38) = k7_relat_1(k7_relat_1(B_38,A_37),A_92)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_608])).

tff(c_1321,plain,(
    ! [A_127,A_128,B_129] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_127),A_128),B_129) = k7_relat_1(k7_relat_1(B_129,A_127),A_128)
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_636])).

tff(c_1376,plain,(
    ! [B_129,A_127] :
      ( k7_relat_1(k7_relat_1(B_129,A_127),k1_relat_1(k6_relat_1(A_127))) = k5_relat_1(k6_relat_1(A_127),B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(k6_relat_1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1321])).

tff(c_1606,plain,(
    ! [B_144,A_145] :
      ( k7_relat_1(k7_relat_1(B_144,A_145),A_145) = k5_relat_1(k6_relat_1(A_145),B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_1376])).

tff(c_1666,plain,(
    ! [A_35,B_80] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_35),B_80),k3_xboole_0(A_35,B_80)) = k5_relat_1(k6_relat_1(k3_xboole_0(A_35,B_80)),k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1606])).

tff(c_2677,plain,(
    ! [A_181,B_182] : k7_relat_1(k7_relat_1(k6_relat_1(A_181),B_182),k3_xboole_0(A_181,B_182)) = k7_relat_1(k6_relat_1(A_181),B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_399,c_1184,c_1666])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k7_relat_1(C_15,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2707,plain,(
    ! [A_181,B_182] :
      ( k7_relat_1(k6_relat_1(A_181),k3_xboole_0(B_182,k3_xboole_0(A_181,B_182))) = k7_relat_1(k6_relat_1(A_181),B_182)
      | ~ v1_relat_1(k6_relat_1(A_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2677,c_14])).

tff(c_2770,plain,(
    ! [A_181,B_182] : k7_relat_1(k6_relat_1(A_181),k3_xboole_0(B_182,k3_xboole_0(A_181,B_182))) = k7_relat_1(k6_relat_1(A_181),B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2707])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [B_52,A_53] : k1_setfam_1(k2_tarski(B_52,A_53)) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8])).

tff(c_400,plain,(
    ! [A_81,B_82] : k7_relat_1(k6_relat_1(A_81),k3_xboole_0(A_81,B_82)) = k7_relat_1(k6_relat_1(A_81),B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_382])).

tff(c_426,plain,(
    ! [B_52,A_53] : k7_relat_1(k6_relat_1(B_52),k3_xboole_0(A_53,B_52)) = k7_relat_1(k6_relat_1(B_52),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_400])).

tff(c_30,plain,(
    ! [A_36] : k4_relat_1(k6_relat_1(A_36)) = k6_relat_1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_437,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(k4_relat_1(B_83),k4_relat_1(A_84)) = k4_relat_1(k5_relat_1(A_84,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_449,plain,(
    ! [A_36,A_84] :
      ( k5_relat_1(k6_relat_1(A_36),k4_relat_1(A_84)) = k4_relat_1(k5_relat_1(A_84,k6_relat_1(A_36)))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_437])).

tff(c_648,plain,(
    ! [A_93,A_94] :
      ( k5_relat_1(k6_relat_1(A_93),k4_relat_1(A_94)) = k4_relat_1(k5_relat_1(A_94,k6_relat_1(A_93)))
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_449])).

tff(c_670,plain,(
    ! [A_36,A_93] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_93))) = k5_relat_1(k6_relat_1(A_93),k6_relat_1(A_36))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_648])).

tff(c_768,plain,(
    ! [A_102,A_103] : k4_relat_1(k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_103))) = k5_relat_1(k6_relat_1(A_103),k6_relat_1(A_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_670])).

tff(c_790,plain,(
    ! [A_20,A_102] :
      ( k5_relat_1(k6_relat_1(A_20),k6_relat_1(A_102)) = k4_relat_1(k8_relat_1(A_20,k6_relat_1(A_102)))
      | ~ v1_relat_1(k6_relat_1(A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_768])).

tff(c_820,plain,(
    ! [A_106,A_107] : k5_relat_1(k6_relat_1(A_106),k6_relat_1(A_107)) = k4_relat_1(k7_relat_1(k6_relat_1(A_106),A_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_270,c_790])).

tff(c_852,plain,(
    ! [A_37,A_107] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_37),A_107)) = k7_relat_1(k6_relat_1(A_107),A_37)
      | ~ v1_relat_1(k6_relat_1(A_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_820])).

tff(c_870,plain,(
    ! [A_37,A_107] : k4_relat_1(k7_relat_1(k6_relat_1(A_37),A_107)) = k7_relat_1(k6_relat_1(A_107),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_852])).

tff(c_938,plain,(
    ! [A_112,A_113] : k4_relat_1(k7_relat_1(k6_relat_1(A_112),A_113)) = k7_relat_1(k6_relat_1(A_113),A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_852])).

tff(c_968,plain,(
    ! [A_35,B_80] : k7_relat_1(k6_relat_1(k3_xboole_0(A_35,B_80)),A_35) = k4_relat_1(k7_relat_1(k6_relat_1(A_35),B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_938])).

tff(c_989,plain,(
    ! [A_35,B_80] : k7_relat_1(k6_relat_1(k3_xboole_0(A_35,B_80)),A_35) = k7_relat_1(k6_relat_1(B_80),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_968])).

tff(c_962,plain,(
    ! [A_53,B_52] : k7_relat_1(k6_relat_1(k3_xboole_0(A_53,B_52)),B_52) = k4_relat_1(k7_relat_1(k6_relat_1(B_52),A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_938])).

tff(c_987,plain,(
    ! [A_53,B_52] : k7_relat_1(k6_relat_1(k3_xboole_0(A_53,B_52)),B_52) = k7_relat_1(k6_relat_1(A_53),B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_962])).

tff(c_273,plain,(
    ! [A_69,A_70] : k8_relat_1(A_69,k6_relat_1(A_70)) = k7_relat_1(k6_relat_1(A_69),A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_260])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    ! [A_66,B_65] :
      ( v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_10])).

tff(c_265,plain,(
    ! [A_66,B_65] :
      ( v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_250])).

tff(c_279,plain,(
    ! [A_69,A_70] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_69),A_70))
      | ~ v1_relat_1(k6_relat_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_265])).

tff(c_285,plain,(
    ! [A_69,A_70] : v1_relat_1(k7_relat_1(k6_relat_1(A_69),A_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_279])).

tff(c_1676,plain,(
    ! [A_35,A_73] :
      ( k5_relat_1(k6_relat_1(A_35),k7_relat_1(k6_relat_1(A_73),A_35)) = k7_relat_1(k7_relat_1(k6_relat_1(A_73),A_35),A_35)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_73),A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_1606])).

tff(c_1904,plain,(
    ! [A_156,A_157] : k5_relat_1(k6_relat_1(A_156),k7_relat_1(k6_relat_1(A_157),A_156)) = k7_relat_1(k6_relat_1(A_157),A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_317,c_1676])).

tff(c_1954,plain,(
    ! [A_35] : k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_35)) = k7_relat_1(k6_relat_1(A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1904])).

tff(c_1986,plain,(
    ! [A_158] : k5_relat_1(k6_relat_1(A_158),k6_relat_1(A_158)) = k6_relat_1(A_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1954])).

tff(c_16,plain,(
    ! [B_17,C_19,A_16] :
      ( k7_relat_1(k5_relat_1(B_17,C_19),A_16) = k5_relat_1(k7_relat_1(B_17,A_16),C_19)
      | ~ v1_relat_1(C_19)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2013,plain,(
    ! [A_158,A_16] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_158),A_16),k6_relat_1(A_158)) = k7_relat_1(k6_relat_1(A_158),A_16)
      | ~ v1_relat_1(k6_relat_1(A_158))
      | ~ v1_relat_1(k6_relat_1(A_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1986,c_16])).

tff(c_2109,plain,(
    ! [A_161,A_162] : k5_relat_1(k7_relat_1(k6_relat_1(A_161),A_162),k6_relat_1(A_161)) = k7_relat_1(k6_relat_1(A_161),A_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_2013])).

tff(c_2133,plain,(
    ! [A_161,A_162] :
      ( k8_relat_1(A_161,k7_relat_1(k6_relat_1(A_161),A_162)) = k7_relat_1(k6_relat_1(A_161),A_162)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_161),A_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_18])).

tff(c_2208,plain,(
    ! [A_163,A_164] : k8_relat_1(A_163,k7_relat_1(k6_relat_1(A_163),A_164)) = k7_relat_1(k6_relat_1(A_163),A_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_2133])).

tff(c_2236,plain,(
    ! [A_53,B_52] : k8_relat_1(k3_xboole_0(A_53,B_52),k7_relat_1(k6_relat_1(A_53),B_52)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_53,B_52)),B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_2208])).

tff(c_4366,plain,(
    ! [A_215,B_216] : k8_relat_1(k3_xboole_0(A_215,B_216),k7_relat_1(k6_relat_1(A_215),B_216)) = k7_relat_1(k6_relat_1(A_215),B_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_2236])).

tff(c_20,plain,(
    ! [A_22,C_24,B_23] :
      ( k8_relat_1(A_22,k7_relat_1(C_24,B_23)) = k7_relat_1(k8_relat_1(A_22,C_24),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4390,plain,(
    ! [A_215,B_216] :
      ( k7_relat_1(k8_relat_1(k3_xboole_0(A_215,B_216),k6_relat_1(A_215)),B_216) = k7_relat_1(k6_relat_1(A_215),B_216)
      | ~ v1_relat_1(k6_relat_1(A_215)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4366,c_20])).

tff(c_4573,plain,(
    ! [B_219,A_220] : k7_relat_1(k7_relat_1(k6_relat_1(B_219),A_220),B_219) = k7_relat_1(k6_relat_1(A_220),B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_989,c_270,c_4390])).

tff(c_4616,plain,(
    ! [B_219,A_220] :
      ( k7_relat_1(k6_relat_1(B_219),k3_xboole_0(A_220,B_219)) = k7_relat_1(k6_relat_1(A_220),B_219)
      | ~ v1_relat_1(k6_relat_1(B_219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4573,c_14])).

tff(c_4733,plain,(
    ! [B_221,A_222] : k7_relat_1(k6_relat_1(B_221),A_222) = k7_relat_1(k6_relat_1(A_222),B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_426,c_4616])).

tff(c_4895,plain,(
    ! [A_222,B_221,B_14] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_222),B_221),B_14) = k7_relat_1(k6_relat_1(B_221),k3_xboole_0(A_222,B_14))
      | ~ v1_relat_1(k6_relat_1(B_221)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4733,c_14])).

tff(c_4995,plain,(
    ! [A_222,B_221,B_14] : k7_relat_1(k7_relat_1(k6_relat_1(A_222),B_221),B_14) = k7_relat_1(k6_relat_1(B_221),k3_xboole_0(A_222,B_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4895])).

tff(c_9134,plain,(
    ! [C_284,A_285,B_286,B_287] :
      ( k7_relat_1(k7_relat_1(C_284,k3_xboole_0(A_285,B_286)),B_287) = k7_relat_1(k7_relat_1(C_284,A_285),k3_xboole_0(B_286,B_287))
      | ~ v1_relat_1(k7_relat_1(C_284,A_285))
      | ~ v1_relat_1(C_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_14])).

tff(c_9401,plain,(
    ! [A_35,B_80,B_287] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_35),A_35),k3_xboole_0(B_80,B_287)) = k7_relat_1(k7_relat_1(k6_relat_1(A_35),B_80),B_287)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_35),A_35))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_9134])).

tff(c_10538,plain,(
    ! [B_301,A_302,B_303] : k7_relat_1(k6_relat_1(B_301),k3_xboole_0(A_302,B_303)) = k7_relat_1(k6_relat_1(A_302),k3_xboole_0(B_301,B_303)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_135,c_4995,c_135,c_9401])).

tff(c_10888,plain,(
    ! [B_301,B_303] : k7_relat_1(k6_relat_1(B_301),k3_xboole_0(k3_xboole_0(B_301,B_303),B_303)) = k6_relat_1(k3_xboole_0(B_301,B_303)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10538,c_135])).

tff(c_11109,plain,(
    ! [B_301,B_303] : k7_relat_1(k6_relat_1(B_301),B_303) = k6_relat_1(k3_xboole_0(B_301,B_303)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2770,c_151,c_10888])).

tff(c_212,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_relat_1(A_61),B_62) = k7_relat_1(B_62,A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_221,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_36])).

tff(c_229,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_221])).

tff(c_11197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11109,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:23:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.11/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.00  
% 9.30/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.00  %$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.30/3.00  
% 9.30/3.00  %Foreground sorts:
% 9.30/3.00  
% 9.30/3.00  
% 9.30/3.00  %Background operators:
% 9.30/3.00  
% 9.30/3.00  
% 9.30/3.00  %Foreground operators:
% 9.30/3.00  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.30/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.30/3.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.30/3.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.30/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.30/3.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.30/3.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.30/3.00  tff('#skF_2', type, '#skF_2': $i).
% 9.30/3.00  tff('#skF_1', type, '#skF_1': $i).
% 9.30/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.30/3.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.30/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.30/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.30/3.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.30/3.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.30/3.00  
% 9.30/3.03  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.30/3.03  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.30/3.03  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 9.30/3.03  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 9.30/3.03  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 9.30/3.03  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 9.30/3.03  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 9.30/3.03  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 9.30/3.03  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.30/3.03  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.30/3.03  tff(f_83, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 9.30/3.03  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 9.30/3.03  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.30/3.03  tff(f_94, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 9.30/3.03  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.30/3.03  tff(c_26, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.30/3.03  tff(c_122, plain, (![A_50]: (k7_relat_1(A_50, k1_relat_1(A_50))=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.30/3.03  tff(c_131, plain, (![A_35]: (k7_relat_1(k6_relat_1(A_35), A_35)=k6_relat_1(A_35) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_122])).
% 9.30/3.03  tff(c_135, plain, (![A_35]: (k7_relat_1(k6_relat_1(A_35), A_35)=k6_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 9.30/3.03  tff(c_347, plain, (![C_78, A_79, B_80]: (k7_relat_1(k7_relat_1(C_78, A_79), B_80)=k7_relat_1(C_78, k3_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.30/3.03  tff(c_382, plain, (![A_35, B_80]: (k7_relat_1(k6_relat_1(A_35), k3_xboole_0(A_35, B_80))=k7_relat_1(k6_relat_1(A_35), B_80) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_347])).
% 9.30/3.03  tff(c_399, plain, (![A_35, B_80]: (k7_relat_1(k6_relat_1(A_35), k3_xboole_0(A_35, B_80))=k7_relat_1(k6_relat_1(A_35), B_80))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_382])).
% 9.30/3.03  tff(c_32, plain, (![A_37, B_38]: (k5_relat_1(k6_relat_1(A_37), B_38)=k7_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.30/3.03  tff(c_240, plain, (![B_65, A_66]: (k5_relat_1(B_65, k6_relat_1(A_66))=k8_relat_1(A_66, B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.30/3.03  tff(c_260, plain, (![A_66, A_37]: (k8_relat_1(A_66, k6_relat_1(A_37))=k7_relat_1(k6_relat_1(A_66), A_37) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_240])).
% 9.30/3.03  tff(c_270, plain, (![A_66, A_37]: (k8_relat_1(A_66, k6_relat_1(A_37))=k7_relat_1(k6_relat_1(A_66), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_260])).
% 9.30/3.03  tff(c_298, plain, (![A_73, C_74, B_75]: (k8_relat_1(A_73, k7_relat_1(C_74, B_75))=k7_relat_1(k8_relat_1(A_73, C_74), B_75) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.30/3.03  tff(c_310, plain, (![A_73, A_35]: (k7_relat_1(k8_relat_1(A_73, k6_relat_1(A_35)), A_35)=k8_relat_1(A_73, k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_298])).
% 9.30/3.03  tff(c_317, plain, (![A_73, A_35]: (k7_relat_1(k7_relat_1(k6_relat_1(A_73), A_35), A_35)=k7_relat_1(k6_relat_1(A_73), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_270, c_270, c_310])).
% 9.30/3.03  tff(c_18, plain, (![B_21, A_20]: (k5_relat_1(B_21, k6_relat_1(A_20))=k8_relat_1(A_20, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.30/3.03  tff(c_608, plain, (![B_90, C_91, A_92]: (k7_relat_1(k5_relat_1(B_90, C_91), A_92)=k5_relat_1(k7_relat_1(B_90, A_92), C_91) | ~v1_relat_1(C_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.03  tff(c_633, plain, (![B_21, A_92, A_20]: (k5_relat_1(k7_relat_1(B_21, A_92), k6_relat_1(A_20))=k7_relat_1(k8_relat_1(A_20, B_21), A_92) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_18, c_608])).
% 9.30/3.03  tff(c_1122, plain, (![B_118, A_119, A_120]: (k5_relat_1(k7_relat_1(B_118, A_119), k6_relat_1(A_120))=k7_relat_1(k8_relat_1(A_120, B_118), A_119) | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_633])).
% 9.30/3.03  tff(c_1165, plain, (![A_120, A_35]: (k7_relat_1(k8_relat_1(A_120, k6_relat_1(A_35)), A_35)=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_120)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1122])).
% 9.30/3.03  tff(c_1184, plain, (![A_35, A_120]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_120))=k7_relat_1(k6_relat_1(A_120), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_317, c_270, c_1165])).
% 9.30/3.03  tff(c_34, plain, (![A_39]: (k7_relat_1(A_39, k1_relat_1(A_39))=A_39 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.30/3.03  tff(c_636, plain, (![A_37, A_92, B_38]: (k5_relat_1(k7_relat_1(k6_relat_1(A_37), A_92), B_38)=k7_relat_1(k7_relat_1(B_38, A_37), A_92) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_32, c_608])).
% 9.30/3.03  tff(c_1321, plain, (![A_127, A_128, B_129]: (k5_relat_1(k7_relat_1(k6_relat_1(A_127), A_128), B_129)=k7_relat_1(k7_relat_1(B_129, A_127), A_128) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_636])).
% 9.30/3.03  tff(c_1376, plain, (![B_129, A_127]: (k7_relat_1(k7_relat_1(B_129, A_127), k1_relat_1(k6_relat_1(A_127)))=k5_relat_1(k6_relat_1(A_127), B_129) | ~v1_relat_1(B_129) | ~v1_relat_1(k6_relat_1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1321])).
% 9.30/3.03  tff(c_1606, plain, (![B_144, A_145]: (k7_relat_1(k7_relat_1(B_144, A_145), A_145)=k5_relat_1(k6_relat_1(A_145), B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_1376])).
% 9.30/3.03  tff(c_1666, plain, (![A_35, B_80]: (k7_relat_1(k7_relat_1(k6_relat_1(A_35), B_80), k3_xboole_0(A_35, B_80))=k5_relat_1(k6_relat_1(k3_xboole_0(A_35, B_80)), k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1606])).
% 9.30/3.03  tff(c_2677, plain, (![A_181, B_182]: (k7_relat_1(k7_relat_1(k6_relat_1(A_181), B_182), k3_xboole_0(A_181, B_182))=k7_relat_1(k6_relat_1(A_181), B_182))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_399, c_1184, c_1666])).
% 9.30/3.03  tff(c_14, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k7_relat_1(C_15, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.30/3.03  tff(c_2707, plain, (![A_181, B_182]: (k7_relat_1(k6_relat_1(A_181), k3_xboole_0(B_182, k3_xboole_0(A_181, B_182)))=k7_relat_1(k6_relat_1(A_181), B_182) | ~v1_relat_1(k6_relat_1(A_181)))), inference(superposition, [status(thm), theory('equality')], [c_2677, c_14])).
% 9.30/3.03  tff(c_2770, plain, (![A_181, B_182]: (k7_relat_1(k6_relat_1(A_181), k3_xboole_0(B_182, k3_xboole_0(A_181, B_182)))=k7_relat_1(k6_relat_1(A_181), B_182))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2707])).
% 9.30/3.03  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.30/3.03  tff(c_107, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.30/3.03  tff(c_145, plain, (![B_52, A_53]: (k1_setfam_1(k2_tarski(B_52, A_53))=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 9.30/3.03  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.30/3.03  tff(c_151, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_145, c_8])).
% 9.30/3.03  tff(c_400, plain, (![A_81, B_82]: (k7_relat_1(k6_relat_1(A_81), k3_xboole_0(A_81, B_82))=k7_relat_1(k6_relat_1(A_81), B_82))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_382])).
% 9.30/3.03  tff(c_426, plain, (![B_52, A_53]: (k7_relat_1(k6_relat_1(B_52), k3_xboole_0(A_53, B_52))=k7_relat_1(k6_relat_1(B_52), A_53))), inference(superposition, [status(thm), theory('equality')], [c_151, c_400])).
% 9.30/3.03  tff(c_30, plain, (![A_36]: (k4_relat_1(k6_relat_1(A_36))=k6_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.30/3.03  tff(c_437, plain, (![B_83, A_84]: (k5_relat_1(k4_relat_1(B_83), k4_relat_1(A_84))=k4_relat_1(k5_relat_1(A_84, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.30/3.03  tff(c_449, plain, (![A_36, A_84]: (k5_relat_1(k6_relat_1(A_36), k4_relat_1(A_84))=k4_relat_1(k5_relat_1(A_84, k6_relat_1(A_36))) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_30, c_437])).
% 9.30/3.03  tff(c_648, plain, (![A_93, A_94]: (k5_relat_1(k6_relat_1(A_93), k4_relat_1(A_94))=k4_relat_1(k5_relat_1(A_94, k6_relat_1(A_93))) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_449])).
% 9.30/3.03  tff(c_670, plain, (![A_36, A_93]: (k4_relat_1(k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_93)))=k5_relat_1(k6_relat_1(A_93), k6_relat_1(A_36)) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_648])).
% 9.30/3.03  tff(c_768, plain, (![A_102, A_103]: (k4_relat_1(k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_103)))=k5_relat_1(k6_relat_1(A_103), k6_relat_1(A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_670])).
% 9.30/3.03  tff(c_790, plain, (![A_20, A_102]: (k5_relat_1(k6_relat_1(A_20), k6_relat_1(A_102))=k4_relat_1(k8_relat_1(A_20, k6_relat_1(A_102))) | ~v1_relat_1(k6_relat_1(A_102)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_768])).
% 9.30/3.03  tff(c_820, plain, (![A_106, A_107]: (k5_relat_1(k6_relat_1(A_106), k6_relat_1(A_107))=k4_relat_1(k7_relat_1(k6_relat_1(A_106), A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_270, c_790])).
% 9.30/3.03  tff(c_852, plain, (![A_37, A_107]: (k4_relat_1(k7_relat_1(k6_relat_1(A_37), A_107))=k7_relat_1(k6_relat_1(A_107), A_37) | ~v1_relat_1(k6_relat_1(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_820])).
% 9.30/3.03  tff(c_870, plain, (![A_37, A_107]: (k4_relat_1(k7_relat_1(k6_relat_1(A_37), A_107))=k7_relat_1(k6_relat_1(A_107), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_852])).
% 9.30/3.03  tff(c_938, plain, (![A_112, A_113]: (k4_relat_1(k7_relat_1(k6_relat_1(A_112), A_113))=k7_relat_1(k6_relat_1(A_113), A_112))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_852])).
% 9.30/3.03  tff(c_968, plain, (![A_35, B_80]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_35, B_80)), A_35)=k4_relat_1(k7_relat_1(k6_relat_1(A_35), B_80)))), inference(superposition, [status(thm), theory('equality')], [c_399, c_938])).
% 9.30/3.03  tff(c_989, plain, (![A_35, B_80]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_35, B_80)), A_35)=k7_relat_1(k6_relat_1(B_80), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_968])).
% 9.30/3.03  tff(c_962, plain, (![A_53, B_52]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_53, B_52)), B_52)=k4_relat_1(k7_relat_1(k6_relat_1(B_52), A_53)))), inference(superposition, [status(thm), theory('equality')], [c_426, c_938])).
% 9.30/3.03  tff(c_987, plain, (![A_53, B_52]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_53, B_52)), B_52)=k7_relat_1(k6_relat_1(A_53), B_52))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_962])).
% 9.30/3.03  tff(c_273, plain, (![A_69, A_70]: (k8_relat_1(A_69, k6_relat_1(A_70))=k7_relat_1(k6_relat_1(A_69), A_70))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_260])).
% 9.30/3.03  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.30/3.03  tff(c_250, plain, (![A_66, B_65]: (v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(B_65) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_240, c_10])).
% 9.30/3.03  tff(c_265, plain, (![A_66, B_65]: (v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_250])).
% 9.30/3.03  tff(c_279, plain, (![A_69, A_70]: (v1_relat_1(k7_relat_1(k6_relat_1(A_69), A_70)) | ~v1_relat_1(k6_relat_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_273, c_265])).
% 9.30/3.03  tff(c_285, plain, (![A_69, A_70]: (v1_relat_1(k7_relat_1(k6_relat_1(A_69), A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_279])).
% 9.30/3.03  tff(c_1676, plain, (![A_35, A_73]: (k5_relat_1(k6_relat_1(A_35), k7_relat_1(k6_relat_1(A_73), A_35))=k7_relat_1(k7_relat_1(k6_relat_1(A_73), A_35), A_35) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_73), A_35)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_1606])).
% 9.30/3.03  tff(c_1904, plain, (![A_156, A_157]: (k5_relat_1(k6_relat_1(A_156), k7_relat_1(k6_relat_1(A_157), A_156))=k7_relat_1(k6_relat_1(A_157), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_317, c_1676])).
% 9.30/3.03  tff(c_1954, plain, (![A_35]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_35))=k7_relat_1(k6_relat_1(A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1904])).
% 9.30/3.03  tff(c_1986, plain, (![A_158]: (k5_relat_1(k6_relat_1(A_158), k6_relat_1(A_158))=k6_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1954])).
% 9.30/3.03  tff(c_16, plain, (![B_17, C_19, A_16]: (k7_relat_1(k5_relat_1(B_17, C_19), A_16)=k5_relat_1(k7_relat_1(B_17, A_16), C_19) | ~v1_relat_1(C_19) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.03  tff(c_2013, plain, (![A_158, A_16]: (k5_relat_1(k7_relat_1(k6_relat_1(A_158), A_16), k6_relat_1(A_158))=k7_relat_1(k6_relat_1(A_158), A_16) | ~v1_relat_1(k6_relat_1(A_158)) | ~v1_relat_1(k6_relat_1(A_158)))), inference(superposition, [status(thm), theory('equality')], [c_1986, c_16])).
% 9.30/3.03  tff(c_2109, plain, (![A_161, A_162]: (k5_relat_1(k7_relat_1(k6_relat_1(A_161), A_162), k6_relat_1(A_161))=k7_relat_1(k6_relat_1(A_161), A_162))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_2013])).
% 9.30/3.03  tff(c_2133, plain, (![A_161, A_162]: (k8_relat_1(A_161, k7_relat_1(k6_relat_1(A_161), A_162))=k7_relat_1(k6_relat_1(A_161), A_162) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_161), A_162)))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_18])).
% 9.30/3.03  tff(c_2208, plain, (![A_163, A_164]: (k8_relat_1(A_163, k7_relat_1(k6_relat_1(A_163), A_164))=k7_relat_1(k6_relat_1(A_163), A_164))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_2133])).
% 9.30/3.03  tff(c_2236, plain, (![A_53, B_52]: (k8_relat_1(k3_xboole_0(A_53, B_52), k7_relat_1(k6_relat_1(A_53), B_52))=k7_relat_1(k6_relat_1(k3_xboole_0(A_53, B_52)), B_52))), inference(superposition, [status(thm), theory('equality')], [c_987, c_2208])).
% 9.30/3.03  tff(c_4366, plain, (![A_215, B_216]: (k8_relat_1(k3_xboole_0(A_215, B_216), k7_relat_1(k6_relat_1(A_215), B_216))=k7_relat_1(k6_relat_1(A_215), B_216))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_2236])).
% 9.30/3.03  tff(c_20, plain, (![A_22, C_24, B_23]: (k8_relat_1(A_22, k7_relat_1(C_24, B_23))=k7_relat_1(k8_relat_1(A_22, C_24), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.30/3.03  tff(c_4390, plain, (![A_215, B_216]: (k7_relat_1(k8_relat_1(k3_xboole_0(A_215, B_216), k6_relat_1(A_215)), B_216)=k7_relat_1(k6_relat_1(A_215), B_216) | ~v1_relat_1(k6_relat_1(A_215)))), inference(superposition, [status(thm), theory('equality')], [c_4366, c_20])).
% 9.30/3.03  tff(c_4573, plain, (![B_219, A_220]: (k7_relat_1(k7_relat_1(k6_relat_1(B_219), A_220), B_219)=k7_relat_1(k6_relat_1(A_220), B_219))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_989, c_270, c_4390])).
% 9.30/3.03  tff(c_4616, plain, (![B_219, A_220]: (k7_relat_1(k6_relat_1(B_219), k3_xboole_0(A_220, B_219))=k7_relat_1(k6_relat_1(A_220), B_219) | ~v1_relat_1(k6_relat_1(B_219)))), inference(superposition, [status(thm), theory('equality')], [c_4573, c_14])).
% 9.30/3.03  tff(c_4733, plain, (![B_221, A_222]: (k7_relat_1(k6_relat_1(B_221), A_222)=k7_relat_1(k6_relat_1(A_222), B_221))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_426, c_4616])).
% 9.30/3.03  tff(c_4895, plain, (![A_222, B_221, B_14]: (k7_relat_1(k7_relat_1(k6_relat_1(A_222), B_221), B_14)=k7_relat_1(k6_relat_1(B_221), k3_xboole_0(A_222, B_14)) | ~v1_relat_1(k6_relat_1(B_221)))), inference(superposition, [status(thm), theory('equality')], [c_4733, c_14])).
% 9.30/3.03  tff(c_4995, plain, (![A_222, B_221, B_14]: (k7_relat_1(k7_relat_1(k6_relat_1(A_222), B_221), B_14)=k7_relat_1(k6_relat_1(B_221), k3_xboole_0(A_222, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4895])).
% 9.30/3.03  tff(c_9134, plain, (![C_284, A_285, B_286, B_287]: (k7_relat_1(k7_relat_1(C_284, k3_xboole_0(A_285, B_286)), B_287)=k7_relat_1(k7_relat_1(C_284, A_285), k3_xboole_0(B_286, B_287)) | ~v1_relat_1(k7_relat_1(C_284, A_285)) | ~v1_relat_1(C_284))), inference(superposition, [status(thm), theory('equality')], [c_347, c_14])).
% 9.30/3.03  tff(c_9401, plain, (![A_35, B_80, B_287]: (k7_relat_1(k7_relat_1(k6_relat_1(A_35), A_35), k3_xboole_0(B_80, B_287))=k7_relat_1(k7_relat_1(k6_relat_1(A_35), B_80), B_287) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_35), A_35)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_399, c_9134])).
% 9.30/3.03  tff(c_10538, plain, (![B_301, A_302, B_303]: (k7_relat_1(k6_relat_1(B_301), k3_xboole_0(A_302, B_303))=k7_relat_1(k6_relat_1(A_302), k3_xboole_0(B_301, B_303)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_135, c_4995, c_135, c_9401])).
% 9.30/3.03  tff(c_10888, plain, (![B_301, B_303]: (k7_relat_1(k6_relat_1(B_301), k3_xboole_0(k3_xboole_0(B_301, B_303), B_303))=k6_relat_1(k3_xboole_0(B_301, B_303)))), inference(superposition, [status(thm), theory('equality')], [c_10538, c_135])).
% 9.30/3.03  tff(c_11109, plain, (![B_301, B_303]: (k7_relat_1(k6_relat_1(B_301), B_303)=k6_relat_1(k3_xboole_0(B_301, B_303)))), inference(demodulation, [status(thm), theory('equality')], [c_2770, c_151, c_10888])).
% 9.30/3.03  tff(c_212, plain, (![A_61, B_62]: (k5_relat_1(k6_relat_1(A_61), B_62)=k7_relat_1(B_62, A_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.30/3.03  tff(c_36, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.30/3.03  tff(c_221, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_36])).
% 9.30/3.03  tff(c_229, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_221])).
% 9.30/3.03  tff(c_11197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11109, c_229])).
% 9.30/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.03  
% 9.30/3.03  Inference rules
% 9.30/3.03  ----------------------
% 9.30/3.03  #Ref     : 0
% 9.30/3.03  #Sup     : 2506
% 9.30/3.03  #Fact    : 0
% 9.30/3.03  #Define  : 0
% 9.30/3.03  #Split   : 0
% 9.30/3.03  #Chain   : 0
% 9.30/3.03  #Close   : 0
% 9.30/3.03  
% 9.30/3.03  Ordering : KBO
% 9.30/3.03  
% 9.30/3.03  Simplification rules
% 9.30/3.03  ----------------------
% 9.30/3.03  #Subsume      : 222
% 9.30/3.03  #Demod        : 4365
% 9.30/3.03  #Tautology    : 1182
% 9.30/3.03  #SimpNegUnit  : 0
% 9.30/3.03  #BackRed      : 60
% 9.30/3.03  
% 9.30/3.03  #Partial instantiations: 0
% 9.30/3.03  #Strategies tried      : 1
% 9.30/3.03  
% 9.30/3.03  Timing (in seconds)
% 9.30/3.03  ----------------------
% 9.30/3.03  Preprocessing        : 0.32
% 9.30/3.03  Parsing              : 0.17
% 9.30/3.03  CNF conversion       : 0.02
% 9.30/3.03  Main loop            : 1.92
% 9.30/3.03  Inferencing          : 0.54
% 9.30/3.03  Reduction            : 0.96
% 9.30/3.03  Demodulation         : 0.82
% 9.30/3.03  BG Simplification    : 0.07
% 9.30/3.03  Subsumption          : 0.26
% 9.30/3.03  Abstraction          : 0.12
% 9.30/3.03  MUC search           : 0.00
% 9.30/3.03  Cooper               : 0.00
% 9.30/3.03  Total                : 2.29
% 9.30/3.03  Index Insertion      : 0.00
% 9.30/3.03  Index Deletion       : 0.00
% 9.30/3.03  Index Matching       : 0.00
% 9.30/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------

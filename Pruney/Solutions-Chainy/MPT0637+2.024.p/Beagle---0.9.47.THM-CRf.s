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
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 10.18s
% Output     : CNFRefutation 10.33s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 157 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  139 ( 232 expanded)
%              Number of equality atoms :   55 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_30,plain,(
    ! [A_33] : k1_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_33] : k2_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_369,plain,(
    ! [A_82,B_83] :
      ( k5_relat_1(k6_relat_1(A_82),B_83) = k7_relat_1(B_83,A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k6_relat_1(k2_relat_1(A_39))) = A_39
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_387,plain,(
    ! [A_82] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_82))),A_82) = k6_relat_1(A_82)
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_82)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_42])).

tff(c_415,plain,(
    ! [A_82] : k7_relat_1(k6_relat_1(A_82),A_82) = k6_relat_1(A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_32,c_387])).

tff(c_818,plain,(
    ! [C_117,A_118,B_119] :
      ( k7_relat_1(k7_relat_1(C_117,A_118),B_119) = k7_relat_1(C_117,k3_xboole_0(A_118,B_119))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_845,plain,(
    ! [A_82,B_119] :
      ( k7_relat_1(k6_relat_1(A_82),k3_xboole_0(A_82,B_119)) = k7_relat_1(k6_relat_1(A_82),B_119)
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_818])).

tff(c_1139,plain,(
    ! [A_143,B_144] : k7_relat_1(k6_relat_1(A_143),k3_xboole_0(A_143,B_144)) = k7_relat_1(k6_relat_1(A_143),B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_845])).

tff(c_38,plain,(
    ! [B_36,A_35] :
      ( r1_tarski(k5_relat_1(B_36,k6_relat_1(A_35)),B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_391,plain,(
    ! [A_35,A_82] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_35),A_82),k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_38])).

tff(c_417,plain,(
    ! [A_35,A_82] : r1_tarski(k7_relat_1(k6_relat_1(A_35),A_82),k6_relat_1(A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_391])).

tff(c_1171,plain,(
    ! [A_143,B_144] : r1_tarski(k7_relat_1(k6_relat_1(A_143),B_144),k6_relat_1(k3_xboole_0(A_143,B_144))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_417])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k7_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [B_23,A_22] :
      ( k5_relat_1(B_23,k6_relat_1(A_22)) = k8_relat_1(A_22,B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_401,plain,(
    ! [A_22,A_82] :
      ( k8_relat_1(A_22,k6_relat_1(A_82)) = k7_relat_1(k6_relat_1(A_22),A_82)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_369])).

tff(c_422,plain,(
    ! [A_22,A_82] : k8_relat_1(A_22,k6_relat_1(A_82)) = k7_relat_1(k6_relat_1(A_22),A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_401])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [B_58,A_59] : k1_setfam_1(k2_tarski(B_58,A_59)) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_58,A_59] : k3_xboole_0(B_58,A_59) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_300,plain,(
    ! [B_74,A_75] :
      ( k5_relat_1(B_74,k6_relat_1(A_75)) = k8_relat_1(A_75,B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_603,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k8_relat_1(A_105,B_106),B_106)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_606,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(k8_relat_1(A_105,B_106),B_106) = k8_relat_1(A_105,B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_603,c_2])).

tff(c_1055,plain,(
    ! [B_135,A_136] :
      ( k3_xboole_0(B_135,k8_relat_1(A_136,B_135)) = k8_relat_1(A_136,B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_606])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1106,plain,(
    ! [A_139,B_140] :
      ( v1_relat_1(k8_relat_1(A_139,B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_14])).

tff(c_1115,plain,(
    ! [A_22,A_82] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_22),A_82))
      | ~ v1_relat_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_1106])).

tff(c_1120,plain,(
    ! [A_22,A_82] : v1_relat_1(k7_relat_1(k6_relat_1(A_22),A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_1115])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1215,plain,(
    ! [B_145,C_146,A_147] :
      ( k7_relat_1(k5_relat_1(B_145,C_146),A_147) = k5_relat_1(k7_relat_1(B_145,A_147),C_146)
      | ~ v1_relat_1(C_146)
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1253,plain,(
    ! [A_40,A_147,B_41] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_40),A_147),B_41) = k7_relat_1(k7_relat_1(B_41,A_40),A_147)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1215])).

tff(c_4114,plain,(
    ! [A_227,A_228,B_229] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_227),A_228),B_229) = k7_relat_1(k7_relat_1(B_229,A_227),A_228)
      | ~ v1_relat_1(B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1253])).

tff(c_4148,plain,(
    ! [A_35,A_227,A_228] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_35),A_227),A_228),k7_relat_1(k6_relat_1(A_227),A_228))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_227),A_228))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4114,c_38])).

tff(c_11365,plain,(
    ! [A_338,A_339,A_340] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_338),A_339),A_340),k7_relat_1(k6_relat_1(A_339),A_340)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1120,c_4148])).

tff(c_11491,plain,(
    ! [A_338,A_15,B_16] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_338),k3_xboole_0(A_15,B_16)),k7_relat_1(k6_relat_1(A_15),B_16))
      | ~ v1_relat_1(k6_relat_1(A_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11365])).

tff(c_12971,plain,(
    ! [A_359,A_360,B_361] : r1_tarski(k7_relat_1(k6_relat_1(A_359),k3_xboole_0(A_360,B_361)),k7_relat_1(k6_relat_1(A_360),B_361)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_11491])).

tff(c_13172,plain,(
    ! [A_362,B_363] : r1_tarski(k6_relat_1(k3_xboole_0(A_362,B_363)),k7_relat_1(k6_relat_1(A_362),B_363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_12971])).

tff(c_459,plain,(
    ! [B_89,A_90] :
      ( k5_relat_1(B_89,k6_relat_1(A_90)) = B_89
      | ~ r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_466,plain,(
    ! [A_33,A_90] :
      ( k5_relat_1(k6_relat_1(A_33),k6_relat_1(A_90)) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_90)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_459])).

tff(c_625,plain,(
    ! [A_107,A_108] :
      ( k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_108)) = k6_relat_1(A_107)
      | ~ r1_tarski(A_107,A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_466])).

tff(c_631,plain,(
    ! [A_108,A_107] :
      ( k7_relat_1(k6_relat_1(A_108),A_107) = k6_relat_1(A_107)
      | ~ v1_relat_1(k6_relat_1(A_108))
      | ~ r1_tarski(A_107,A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_44])).

tff(c_692,plain,(
    ! [A_109,A_110] :
      ( k7_relat_1(k6_relat_1(A_109),A_110) = k6_relat_1(A_110)
      | ~ r1_tarski(A_110,A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_631])).

tff(c_438,plain,(
    ! [B_85,A_86] :
      ( k7_relat_1(B_85,A_86) = B_85
      | ~ r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_445,plain,(
    ! [A_33,A_86] :
      ( k7_relat_1(k6_relat_1(A_33),A_86) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_86)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_438])).

tff(c_448,plain,(
    ! [A_33,A_86] :
      ( k7_relat_1(k6_relat_1(A_33),A_86) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_445])).

tff(c_704,plain,(
    ! [A_110,A_109] :
      ( k6_relat_1(A_110) = k6_relat_1(A_109)
      | ~ r1_tarski(A_109,A_110)
      | ~ r1_tarski(A_110,A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_448])).

tff(c_13183,plain,(
    ! [A_362,B_363] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_362),B_363)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_362,B_363)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_362),B_363),k6_relat_1(k3_xboole_0(A_362,B_363))) ) ),
    inference(resolution,[status(thm)],[c_13172,c_704])).

tff(c_16368,plain,(
    ! [A_395,B_396] : k6_relat_1(k7_relat_1(k6_relat_1(A_395),B_396)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_395,B_396))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_13183])).

tff(c_16714,plain,(
    ! [A_395,B_396] : k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_395,B_396)))) = k7_relat_1(k6_relat_1(A_395),B_396) ),
    inference(superposition,[status(thm),theory(equality)],[c_16368,c_30])).

tff(c_16830,plain,(
    ! [A_395,B_396] : k7_relat_1(k6_relat_1(A_395),B_396) = k6_relat_1(k3_xboole_0(A_395,B_396)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16714])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_394,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_48])).

tff(c_419,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_394])).

tff(c_16938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16830,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.18/3.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.57  
% 10.18/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.57  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.18/3.57  
% 10.18/3.57  %Foreground sorts:
% 10.18/3.57  
% 10.18/3.57  
% 10.18/3.57  %Background operators:
% 10.18/3.57  
% 10.18/3.57  
% 10.18/3.57  %Foreground operators:
% 10.18/3.57  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 10.18/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.18/3.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.18/3.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.18/3.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.18/3.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.18/3.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.18/3.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.18/3.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.18/3.57  tff('#skF_2', type, '#skF_2': $i).
% 10.18/3.57  tff('#skF_1', type, '#skF_1': $i).
% 10.18/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.18/3.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.18/3.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.18/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.18/3.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.18/3.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.18/3.57  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.18/3.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.18/3.57  
% 10.33/3.59  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.33/3.59  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 10.33/3.59  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 10.33/3.59  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 10.33/3.59  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 10.33/3.59  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 10.33/3.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 10.33/3.59  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.33/3.59  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.33/3.59  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.33/3.59  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 10.33/3.59  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 10.33/3.59  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 10.33/3.59  tff(f_112, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 10.33/3.59  tff(f_115, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 10.33/3.59  tff(c_30, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.33/3.59  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.33/3.59  tff(c_32, plain, (![A_33]: (k2_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.33/3.59  tff(c_369, plain, (![A_82, B_83]: (k5_relat_1(k6_relat_1(A_82), B_83)=k7_relat_1(B_83, A_82) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.33/3.59  tff(c_42, plain, (![A_39]: (k5_relat_1(A_39, k6_relat_1(k2_relat_1(A_39)))=A_39 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.33/3.59  tff(c_387, plain, (![A_82]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_82))), A_82)=k6_relat_1(A_82) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_82)))))), inference(superposition, [status(thm), theory('equality')], [c_369, c_42])).
% 10.33/3.59  tff(c_415, plain, (![A_82]: (k7_relat_1(k6_relat_1(A_82), A_82)=k6_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_32, c_387])).
% 10.33/3.59  tff(c_818, plain, (![C_117, A_118, B_119]: (k7_relat_1(k7_relat_1(C_117, A_118), B_119)=k7_relat_1(C_117, k3_xboole_0(A_118, B_119)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.33/3.59  tff(c_845, plain, (![A_82, B_119]: (k7_relat_1(k6_relat_1(A_82), k3_xboole_0(A_82, B_119))=k7_relat_1(k6_relat_1(A_82), B_119) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_415, c_818])).
% 10.33/3.59  tff(c_1139, plain, (![A_143, B_144]: (k7_relat_1(k6_relat_1(A_143), k3_xboole_0(A_143, B_144))=k7_relat_1(k6_relat_1(A_143), B_144))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_845])).
% 10.33/3.59  tff(c_38, plain, (![B_36, A_35]: (r1_tarski(k5_relat_1(B_36, k6_relat_1(A_35)), B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.33/3.59  tff(c_391, plain, (![A_35, A_82]: (r1_tarski(k7_relat_1(k6_relat_1(A_35), A_82), k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_369, c_38])).
% 10.33/3.59  tff(c_417, plain, (![A_35, A_82]: (r1_tarski(k7_relat_1(k6_relat_1(A_35), A_82), k6_relat_1(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_391])).
% 10.33/3.59  tff(c_1171, plain, (![A_143, B_144]: (r1_tarski(k7_relat_1(k6_relat_1(A_143), B_144), k6_relat_1(k3_xboole_0(A_143, B_144))))), inference(superposition, [status(thm), theory('equality')], [c_1139, c_417])).
% 10.33/3.59  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.33/3.59  tff(c_20, plain, (![B_23, A_22]: (k5_relat_1(B_23, k6_relat_1(A_22))=k8_relat_1(A_22, B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.33/3.59  tff(c_401, plain, (![A_22, A_82]: (k8_relat_1(A_22, k6_relat_1(A_82))=k7_relat_1(k6_relat_1(A_22), A_82) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_369])).
% 10.33/3.59  tff(c_422, plain, (![A_22, A_82]: (k8_relat_1(A_22, k6_relat_1(A_82))=k7_relat_1(k6_relat_1(A_22), A_82))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_401])).
% 10.33/3.59  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.33/3.59  tff(c_121, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.33/3.59  tff(c_136, plain, (![B_58, A_59]: (k1_setfam_1(k2_tarski(B_58, A_59))=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_4, c_121])).
% 10.33/3.59  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.33/3.59  tff(c_142, plain, (![B_58, A_59]: (k3_xboole_0(B_58, A_59)=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 10.33/3.59  tff(c_300, plain, (![B_74, A_75]: (k5_relat_1(B_74, k6_relat_1(A_75))=k8_relat_1(A_75, B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.33/3.59  tff(c_603, plain, (![A_105, B_106]: (r1_tarski(k8_relat_1(A_105, B_106), B_106) | ~v1_relat_1(B_106) | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_300, c_38])).
% 10.33/3.59  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.33/3.59  tff(c_606, plain, (![A_105, B_106]: (k3_xboole_0(k8_relat_1(A_105, B_106), B_106)=k8_relat_1(A_105, B_106) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_603, c_2])).
% 10.33/3.59  tff(c_1055, plain, (![B_135, A_136]: (k3_xboole_0(B_135, k8_relat_1(A_136, B_135))=k8_relat_1(A_136, B_135) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_606])).
% 10.33/3.59  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.33/3.59  tff(c_1106, plain, (![A_139, B_140]: (v1_relat_1(k8_relat_1(A_139, B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(B_140))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_14])).
% 10.33/3.59  tff(c_1115, plain, (![A_22, A_82]: (v1_relat_1(k7_relat_1(k6_relat_1(A_22), A_82)) | ~v1_relat_1(k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_422, c_1106])).
% 10.33/3.59  tff(c_1120, plain, (![A_22, A_82]: (v1_relat_1(k7_relat_1(k6_relat_1(A_22), A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_1115])).
% 10.33/3.59  tff(c_44, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.33/3.59  tff(c_1215, plain, (![B_145, C_146, A_147]: (k7_relat_1(k5_relat_1(B_145, C_146), A_147)=k5_relat_1(k7_relat_1(B_145, A_147), C_146) | ~v1_relat_1(C_146) | ~v1_relat_1(B_145))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.33/3.59  tff(c_1253, plain, (![A_40, A_147, B_41]: (k5_relat_1(k7_relat_1(k6_relat_1(A_40), A_147), B_41)=k7_relat_1(k7_relat_1(B_41, A_40), A_147) | ~v1_relat_1(B_41) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1215])).
% 10.33/3.59  tff(c_4114, plain, (![A_227, A_228, B_229]: (k5_relat_1(k7_relat_1(k6_relat_1(A_227), A_228), B_229)=k7_relat_1(k7_relat_1(B_229, A_227), A_228) | ~v1_relat_1(B_229))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1253])).
% 10.33/3.59  tff(c_4148, plain, (![A_35, A_227, A_228]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_35), A_227), A_228), k7_relat_1(k6_relat_1(A_227), A_228)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_227), A_228)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_4114, c_38])).
% 10.33/3.59  tff(c_11365, plain, (![A_338, A_339, A_340]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_338), A_339), A_340), k7_relat_1(k6_relat_1(A_339), A_340)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1120, c_4148])).
% 10.33/3.59  tff(c_11491, plain, (![A_338, A_15, B_16]: (r1_tarski(k7_relat_1(k6_relat_1(A_338), k3_xboole_0(A_15, B_16)), k7_relat_1(k6_relat_1(A_15), B_16)) | ~v1_relat_1(k6_relat_1(A_338)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_11365])).
% 10.33/3.59  tff(c_12971, plain, (![A_359, A_360, B_361]: (r1_tarski(k7_relat_1(k6_relat_1(A_359), k3_xboole_0(A_360, B_361)), k7_relat_1(k6_relat_1(A_360), B_361)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_11491])).
% 10.33/3.59  tff(c_13172, plain, (![A_362, B_363]: (r1_tarski(k6_relat_1(k3_xboole_0(A_362, B_363)), k7_relat_1(k6_relat_1(A_362), B_363)))), inference(superposition, [status(thm), theory('equality')], [c_415, c_12971])).
% 10.33/3.59  tff(c_459, plain, (![B_89, A_90]: (k5_relat_1(B_89, k6_relat_1(A_90))=B_89 | ~r1_tarski(k2_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.33/3.59  tff(c_466, plain, (![A_33, A_90]: (k5_relat_1(k6_relat_1(A_33), k6_relat_1(A_90))=k6_relat_1(A_33) | ~r1_tarski(A_33, A_90) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_459])).
% 10.33/3.59  tff(c_625, plain, (![A_107, A_108]: (k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_108))=k6_relat_1(A_107) | ~r1_tarski(A_107, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_466])).
% 10.33/3.59  tff(c_631, plain, (![A_108, A_107]: (k7_relat_1(k6_relat_1(A_108), A_107)=k6_relat_1(A_107) | ~v1_relat_1(k6_relat_1(A_108)) | ~r1_tarski(A_107, A_108))), inference(superposition, [status(thm), theory('equality')], [c_625, c_44])).
% 10.33/3.59  tff(c_692, plain, (![A_109, A_110]: (k7_relat_1(k6_relat_1(A_109), A_110)=k6_relat_1(A_110) | ~r1_tarski(A_110, A_109))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_631])).
% 10.33/3.59  tff(c_438, plain, (![B_85, A_86]: (k7_relat_1(B_85, A_86)=B_85 | ~r1_tarski(k1_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.33/3.59  tff(c_445, plain, (![A_33, A_86]: (k7_relat_1(k6_relat_1(A_33), A_86)=k6_relat_1(A_33) | ~r1_tarski(A_33, A_86) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_438])).
% 10.33/3.59  tff(c_448, plain, (![A_33, A_86]: (k7_relat_1(k6_relat_1(A_33), A_86)=k6_relat_1(A_33) | ~r1_tarski(A_33, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_445])).
% 10.33/3.59  tff(c_704, plain, (![A_110, A_109]: (k6_relat_1(A_110)=k6_relat_1(A_109) | ~r1_tarski(A_109, A_110) | ~r1_tarski(A_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_692, c_448])).
% 10.33/3.59  tff(c_13183, plain, (![A_362, B_363]: (k6_relat_1(k7_relat_1(k6_relat_1(A_362), B_363))=k6_relat_1(k6_relat_1(k3_xboole_0(A_362, B_363))) | ~r1_tarski(k7_relat_1(k6_relat_1(A_362), B_363), k6_relat_1(k3_xboole_0(A_362, B_363))))), inference(resolution, [status(thm)], [c_13172, c_704])).
% 10.33/3.59  tff(c_16368, plain, (![A_395, B_396]: (k6_relat_1(k7_relat_1(k6_relat_1(A_395), B_396))=k6_relat_1(k6_relat_1(k3_xboole_0(A_395, B_396))))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_13183])).
% 10.33/3.59  tff(c_16714, plain, (![A_395, B_396]: (k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_395, B_396))))=k7_relat_1(k6_relat_1(A_395), B_396))), inference(superposition, [status(thm), theory('equality')], [c_16368, c_30])).
% 10.33/3.59  tff(c_16830, plain, (![A_395, B_396]: (k7_relat_1(k6_relat_1(A_395), B_396)=k6_relat_1(k3_xboole_0(A_395, B_396)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16714])).
% 10.33/3.59  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.33/3.59  tff(c_394, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_48])).
% 10.33/3.59  tff(c_419, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_394])).
% 10.33/3.59  tff(c_16938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16830, c_419])).
% 10.33/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.33/3.59  
% 10.33/3.59  Inference rules
% 10.33/3.59  ----------------------
% 10.33/3.59  #Ref     : 0
% 10.33/3.59  #Sup     : 3997
% 10.33/3.59  #Fact    : 0
% 10.33/3.59  #Define  : 0
% 10.33/3.59  #Split   : 2
% 10.33/3.59  #Chain   : 0
% 10.33/3.59  #Close   : 0
% 10.33/3.59  
% 10.33/3.59  Ordering : KBO
% 10.33/3.59  
% 10.33/3.59  Simplification rules
% 10.33/3.59  ----------------------
% 10.33/3.59  #Subsume      : 533
% 10.33/3.59  #Demod        : 4154
% 10.33/3.59  #Tautology    : 1512
% 10.33/3.59  #SimpNegUnit  : 0
% 10.33/3.59  #BackRed      : 80
% 10.33/3.59  
% 10.33/3.59  #Partial instantiations: 0
% 10.33/3.59  #Strategies tried      : 1
% 10.33/3.59  
% 10.33/3.59  Timing (in seconds)
% 10.33/3.59  ----------------------
% 10.33/3.59  Preprocessing        : 0.35
% 10.33/3.59  Parsing              : 0.19
% 10.33/3.59  CNF conversion       : 0.02
% 10.33/3.59  Main loop            : 2.53
% 10.33/3.59  Inferencing          : 0.66
% 10.33/3.59  Reduction            : 1.12
% 10.33/3.59  Demodulation         : 0.94
% 10.33/3.59  BG Simplification    : 0.11
% 10.33/3.59  Subsumption          : 0.51
% 10.33/3.59  Abstraction          : 0.15
% 10.33/3.59  MUC search           : 0.00
% 10.33/3.59  Cooper               : 0.00
% 10.33/3.59  Total                : 2.92
% 10.33/3.59  Index Insertion      : 0.00
% 10.33/3.59  Index Deletion       : 0.00
% 10.33/3.59  Index Matching       : 0.00
% 10.33/3.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

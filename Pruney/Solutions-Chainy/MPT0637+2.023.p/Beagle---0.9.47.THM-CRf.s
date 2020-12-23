%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 386 expanded)
%              Number of leaves         :   36 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 647 expanded)
%              Number of equality atoms :   59 ( 196 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(B_58,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_132])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [B_58,A_57] : k3_xboole_0(B_58,A_57) = k3_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_10])).

tff(c_32,plain,(
    ! [A_32] : k2_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_109,plain,(
    ! [A_49] :
      ( k7_relat_1(A_49,k1_relat_1(A_49)) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118,plain,(
    ! [A_32] :
      ( k7_relat_1(k6_relat_1(A_32),A_32) = k6_relat_1(A_32)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_109])).

tff(c_122,plain,(
    ! [A_32] : k7_relat_1(k6_relat_1(A_32),A_32) = k6_relat_1(A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_444,plain,(
    ! [C_96,A_97,B_98] :
      ( k7_relat_1(k7_relat_1(C_96,A_97),B_98) = k7_relat_1(C_96,k3_xboole_0(A_97,B_98))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_466,plain,(
    ! [A_32,B_98] :
      ( k7_relat_1(k6_relat_1(A_32),k3_xboole_0(A_32,B_98)) = k7_relat_1(k6_relat_1(A_32),B_98)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_444])).

tff(c_918,plain,(
    ! [A_136,B_137] : k7_relat_1(k6_relat_1(A_136),k3_xboole_0(A_136,B_137)) = k7_relat_1(k6_relat_1(A_136),B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_466])).

tff(c_276,plain,(
    ! [A_74,B_75] :
      ( k5_relat_1(k6_relat_1(A_74),B_75) = k7_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k5_relat_1(B_35,k6_relat_1(A_34)),B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_290,plain,(
    ! [A_34,A_74] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_34),A_74),k6_relat_1(A_74))
      | ~ v1_relat_1(k6_relat_1(A_74))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_38])).

tff(c_305,plain,(
    ! [A_34,A_74] : r1_tarski(k7_relat_1(k6_relat_1(A_34),A_74),k6_relat_1(A_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_290])).

tff(c_944,plain,(
    ! [A_136,B_137] : r1_tarski(k7_relat_1(k6_relat_1(A_136),B_137),k6_relat_1(k3_xboole_0(A_136,B_137))) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_305])).

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

tff(c_300,plain,(
    ! [A_22,A_74] :
      ( k8_relat_1(A_22,k6_relat_1(A_74)) = k7_relat_1(k6_relat_1(A_22),A_74)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_276])).

tff(c_310,plain,(
    ! [A_22,A_74] : k8_relat_1(A_22,k6_relat_1(A_74)) = k7_relat_1(k6_relat_1(A_22),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_300])).

tff(c_397,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(B_88,k2_zfmisc_1(k1_relat_1(B_88),A_89)) = k8_relat_1(A_89,B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_417,plain,(
    ! [A_90,B_91] :
      ( v1_relat_1(k8_relat_1(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_14])).

tff(c_420,plain,(
    ! [A_22,A_74] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_22),A_74))
      | ~ v1_relat_1(k6_relat_1(A_74))
      | ~ v1_relat_1(k6_relat_1(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_417])).

tff(c_422,plain,(
    ! [A_22,A_74] : v1_relat_1(k7_relat_1(k6_relat_1(A_22),A_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_420])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_775,plain,(
    ! [B_127,C_128,A_129] :
      ( k7_relat_1(k5_relat_1(B_127,C_128),A_129) = k5_relat_1(k7_relat_1(B_127,A_129),C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_800,plain,(
    ! [A_36,A_129,B_37] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_36),A_129),B_37) = k7_relat_1(k7_relat_1(B_37,A_36),A_129)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_775])).

tff(c_2253,plain,(
    ! [A_176,A_177,B_178] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_176),A_177),B_178) = k7_relat_1(k7_relat_1(B_178,A_176),A_177)
      | ~ v1_relat_1(B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_800])).

tff(c_2267,plain,(
    ! [A_34,A_176,A_177] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_34),A_176),A_177),k7_relat_1(k6_relat_1(A_176),A_177))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_176),A_177))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2253,c_38])).

tff(c_2941,plain,(
    ! [A_201,A_202,A_203] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_201),A_202),A_203),k7_relat_1(k6_relat_1(A_202),A_203)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_422,c_2267])).

tff(c_2989,plain,(
    ! [A_201,A_15,B_16] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_201),k3_xboole_0(A_15,B_16)),k7_relat_1(k6_relat_1(A_15),B_16))
      | ~ v1_relat_1(k6_relat_1(A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2941])).

tff(c_7907,plain,(
    ! [A_274,A_275,B_276] : r1_tarski(k7_relat_1(k6_relat_1(A_274),k3_xboole_0(A_275,B_276)),k7_relat_1(k6_relat_1(A_275),B_276)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2989])).

tff(c_8097,plain,(
    ! [A_277,B_278] : r1_tarski(k6_relat_1(k3_xboole_0(A_277,B_278)),k7_relat_1(k6_relat_1(A_277),B_278)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_7907])).

tff(c_311,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_314,plain,(
    ! [A_32,A_77] :
      ( k7_relat_1(k6_relat_1(A_32),A_77) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_77)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_311])).

tff(c_478,plain,(
    ! [A_99,A_100] :
      ( k7_relat_1(k6_relat_1(A_99),A_100) = k6_relat_1(A_99)
      | ~ r1_tarski(A_99,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_314])).

tff(c_533,plain,(
    ! [A_101,A_102] :
      ( r1_tarski(k6_relat_1(A_101),k6_relat_1(A_102))
      | ~ r1_tarski(A_101,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_305])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1287,plain,(
    ! [A_146,A_147] :
      ( k3_xboole_0(k6_relat_1(A_146),k6_relat_1(A_147)) = k6_relat_1(A_146)
      | ~ r1_tarski(A_146,A_147) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_1568,plain,(
    ! [A_154,A_155] :
      ( k3_xboole_0(k6_relat_1(A_154),k6_relat_1(A_155)) = k6_relat_1(A_155)
      | ~ r1_tarski(A_155,A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1287])).

tff(c_537,plain,(
    ! [A_101,A_102] :
      ( k3_xboole_0(k6_relat_1(A_101),k6_relat_1(A_102)) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_102) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_1577,plain,(
    ! [A_155,A_154] :
      ( k6_relat_1(A_155) = k6_relat_1(A_154)
      | ~ r1_tarski(A_154,A_155)
      | ~ r1_tarski(A_155,A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_537])).

tff(c_8105,plain,(
    ! [A_277,B_278] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_277),B_278)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_277,B_278)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_277),B_278),k6_relat_1(k3_xboole_0(A_277,B_278))) ) ),
    inference(resolution,[status(thm)],[c_8097,c_1577])).

tff(c_8232,plain,(
    ! [A_277,B_278] : k6_relat_1(k7_relat_1(k6_relat_1(A_277),B_278)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_277,B_278))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_8105])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_34),B_35),B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_286,plain,(
    ! [B_75,A_74] :
      ( r1_tarski(k7_relat_1(B_75,A_74),B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_36])).

tff(c_549,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_relat_1(A_104),k1_relat_1(B_105))
      | ~ r1_tarski(A_104,B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_561,plain,(
    ! [A_104,A_32] :
      ( r1_tarski(k1_relat_1(A_104),A_32)
      | ~ r1_tarski(A_104,k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_549])).

tff(c_729,plain,(
    ! [A_123,A_124] :
      ( r1_tarski(k1_relat_1(A_123),A_124)
      | ~ r1_tarski(A_123,k6_relat_1(A_124))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_561])).

tff(c_42,plain,(
    ! [B_39,A_38] :
      ( k7_relat_1(B_39,A_38) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_834,plain,(
    ! [A_132,A_133] :
      ( k7_relat_1(A_132,A_133) = A_132
      | ~ r1_tarski(A_132,k6_relat_1(A_133))
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_729,c_42])).

tff(c_857,plain,(
    ! [A_133,A_74] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_133),A_74),A_133) = k7_relat_1(k6_relat_1(A_133),A_74)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_133),A_74))
      | ~ v1_relat_1(k6_relat_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_286,c_834])).

tff(c_885,plain,(
    ! [A_133,A_74] : k7_relat_1(k7_relat_1(k6_relat_1(A_133),A_74),A_133) = k7_relat_1(k6_relat_1(A_133),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_422,c_857])).

tff(c_2961,plain,(
    ! [A_133,A_74] : r1_tarski(k7_relat_1(k6_relat_1(A_133),A_74),k7_relat_1(k6_relat_1(A_74),A_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_2941])).

tff(c_3230,plain,(
    ! [A_206,A_207] : r1_tarski(k7_relat_1(k6_relat_1(A_206),A_207),k7_relat_1(k6_relat_1(A_207),A_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_2941])).

tff(c_3232,plain,(
    ! [A_207,A_206] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_207),A_206)) = k6_relat_1(k7_relat_1(k6_relat_1(A_206),A_207))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_207),A_206),k7_relat_1(k6_relat_1(A_206),A_207)) ) ),
    inference(resolution,[status(thm)],[c_3230,c_1577])).

tff(c_3369,plain,(
    ! [A_211,A_210] : k6_relat_1(k7_relat_1(k6_relat_1(A_211),A_210)) = k6_relat_1(k7_relat_1(k6_relat_1(A_210),A_211)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2961,c_3232])).

tff(c_3719,plain,(
    ! [A_210,A_211] : k2_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_210),A_211))) = k7_relat_1(k6_relat_1(A_211),A_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_3369,c_32])).

tff(c_10032,plain,(
    ! [A_210,A_211] : k2_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_210,A_211)))) = k7_relat_1(k6_relat_1(A_211),A_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8232,c_3719])).

tff(c_10035,plain,(
    ! [A_211,A_210] : k7_relat_1(k6_relat_1(A_211),A_210) = k6_relat_1(k3_xboole_0(A_210,A_211)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10032])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_293,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_46])).

tff(c_307,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_10522,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10035,c_307])).

tff(c_10543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_10522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:04:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.83/2.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.72  
% 7.83/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.73  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.83/2.73  
% 7.83/2.73  %Foreground sorts:
% 7.83/2.73  
% 7.83/2.73  
% 7.83/2.73  %Background operators:
% 7.83/2.73  
% 7.83/2.73  
% 7.83/2.73  %Foreground operators:
% 7.83/2.73  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.83/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.83/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.83/2.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.83/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.83/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.83/2.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.83/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.83/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.83/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.83/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.83/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.83/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.83/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.83/2.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.83/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.83/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.83/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.83/2.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.83/2.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.83/2.73  
% 7.95/2.75  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.95/2.75  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.95/2.75  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.95/2.75  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.95/2.75  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 7.95/2.75  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 7.95/2.75  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.95/2.75  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 7.95/2.75  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 7.95/2.75  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 7.95/2.75  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 7.95/2.75  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 7.95/2.75  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.95/2.75  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.95/2.75  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 7.95/2.75  tff(f_109, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 7.95/2.75  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.95/2.75  tff(c_132, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.95/2.75  tff(c_157, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_4, c_132])).
% 7.95/2.75  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.95/2.75  tff(c_163, plain, (![B_58, A_57]: (k3_xboole_0(B_58, A_57)=k3_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_157, c_10])).
% 7.95/2.75  tff(c_32, plain, (![A_32]: (k2_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.95/2.75  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.95/2.75  tff(c_30, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.95/2.75  tff(c_109, plain, (![A_49]: (k7_relat_1(A_49, k1_relat_1(A_49))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.95/2.75  tff(c_118, plain, (![A_32]: (k7_relat_1(k6_relat_1(A_32), A_32)=k6_relat_1(A_32) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_109])).
% 7.95/2.75  tff(c_122, plain, (![A_32]: (k7_relat_1(k6_relat_1(A_32), A_32)=k6_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 7.95/2.75  tff(c_444, plain, (![C_96, A_97, B_98]: (k7_relat_1(k7_relat_1(C_96, A_97), B_98)=k7_relat_1(C_96, k3_xboole_0(A_97, B_98)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.95/2.75  tff(c_466, plain, (![A_32, B_98]: (k7_relat_1(k6_relat_1(A_32), k3_xboole_0(A_32, B_98))=k7_relat_1(k6_relat_1(A_32), B_98) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_444])).
% 7.95/2.75  tff(c_918, plain, (![A_136, B_137]: (k7_relat_1(k6_relat_1(A_136), k3_xboole_0(A_136, B_137))=k7_relat_1(k6_relat_1(A_136), B_137))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_466])).
% 7.95/2.75  tff(c_276, plain, (![A_74, B_75]: (k5_relat_1(k6_relat_1(A_74), B_75)=k7_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.95/2.75  tff(c_38, plain, (![B_35, A_34]: (r1_tarski(k5_relat_1(B_35, k6_relat_1(A_34)), B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.95/2.75  tff(c_290, plain, (![A_34, A_74]: (r1_tarski(k7_relat_1(k6_relat_1(A_34), A_74), k6_relat_1(A_74)) | ~v1_relat_1(k6_relat_1(A_74)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_38])).
% 7.95/2.75  tff(c_305, plain, (![A_34, A_74]: (r1_tarski(k7_relat_1(k6_relat_1(A_34), A_74), k6_relat_1(A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_290])).
% 7.95/2.75  tff(c_944, plain, (![A_136, B_137]: (r1_tarski(k7_relat_1(k6_relat_1(A_136), B_137), k6_relat_1(k3_xboole_0(A_136, B_137))))), inference(superposition, [status(thm), theory('equality')], [c_918, c_305])).
% 7.95/2.75  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.95/2.75  tff(c_20, plain, (![B_23, A_22]: (k5_relat_1(B_23, k6_relat_1(A_22))=k8_relat_1(A_22, B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.95/2.75  tff(c_300, plain, (![A_22, A_74]: (k8_relat_1(A_22, k6_relat_1(A_74))=k7_relat_1(k6_relat_1(A_22), A_74) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_276])).
% 7.95/2.75  tff(c_310, plain, (![A_22, A_74]: (k8_relat_1(A_22, k6_relat_1(A_74))=k7_relat_1(k6_relat_1(A_22), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_300])).
% 7.95/2.75  tff(c_397, plain, (![B_88, A_89]: (k3_xboole_0(B_88, k2_zfmisc_1(k1_relat_1(B_88), A_89))=k8_relat_1(A_89, B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.95/2.75  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.95/2.75  tff(c_417, plain, (![A_90, B_91]: (v1_relat_1(k8_relat_1(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(B_91))), inference(superposition, [status(thm), theory('equality')], [c_397, c_14])).
% 7.95/2.75  tff(c_420, plain, (![A_22, A_74]: (v1_relat_1(k7_relat_1(k6_relat_1(A_22), A_74)) | ~v1_relat_1(k6_relat_1(A_74)) | ~v1_relat_1(k6_relat_1(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_417])).
% 7.95/2.75  tff(c_422, plain, (![A_22, A_74]: (v1_relat_1(k7_relat_1(k6_relat_1(A_22), A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_420])).
% 7.95/2.75  tff(c_40, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.95/2.75  tff(c_775, plain, (![B_127, C_128, A_129]: (k7_relat_1(k5_relat_1(B_127, C_128), A_129)=k5_relat_1(k7_relat_1(B_127, A_129), C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.95/2.75  tff(c_800, plain, (![A_36, A_129, B_37]: (k5_relat_1(k7_relat_1(k6_relat_1(A_36), A_129), B_37)=k7_relat_1(k7_relat_1(B_37, A_36), A_129) | ~v1_relat_1(B_37) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_40, c_775])).
% 7.95/2.75  tff(c_2253, plain, (![A_176, A_177, B_178]: (k5_relat_1(k7_relat_1(k6_relat_1(A_176), A_177), B_178)=k7_relat_1(k7_relat_1(B_178, A_176), A_177) | ~v1_relat_1(B_178))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_800])).
% 7.95/2.75  tff(c_2267, plain, (![A_34, A_176, A_177]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_34), A_176), A_177), k7_relat_1(k6_relat_1(A_176), A_177)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_176), A_177)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_2253, c_38])).
% 7.95/2.75  tff(c_2941, plain, (![A_201, A_202, A_203]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_201), A_202), A_203), k7_relat_1(k6_relat_1(A_202), A_203)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_422, c_2267])).
% 7.95/2.75  tff(c_2989, plain, (![A_201, A_15, B_16]: (r1_tarski(k7_relat_1(k6_relat_1(A_201), k3_xboole_0(A_15, B_16)), k7_relat_1(k6_relat_1(A_15), B_16)) | ~v1_relat_1(k6_relat_1(A_201)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2941])).
% 7.95/2.75  tff(c_7907, plain, (![A_274, A_275, B_276]: (r1_tarski(k7_relat_1(k6_relat_1(A_274), k3_xboole_0(A_275, B_276)), k7_relat_1(k6_relat_1(A_275), B_276)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2989])).
% 7.95/2.75  tff(c_8097, plain, (![A_277, B_278]: (r1_tarski(k6_relat_1(k3_xboole_0(A_277, B_278)), k7_relat_1(k6_relat_1(A_277), B_278)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_7907])).
% 7.95/2.75  tff(c_311, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.95/2.75  tff(c_314, plain, (![A_32, A_77]: (k7_relat_1(k6_relat_1(A_32), A_77)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_77) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_311])).
% 7.95/2.75  tff(c_478, plain, (![A_99, A_100]: (k7_relat_1(k6_relat_1(A_99), A_100)=k6_relat_1(A_99) | ~r1_tarski(A_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_314])).
% 7.95/2.75  tff(c_533, plain, (![A_101, A_102]: (r1_tarski(k6_relat_1(A_101), k6_relat_1(A_102)) | ~r1_tarski(A_101, A_102))), inference(superposition, [status(thm), theory('equality')], [c_478, c_305])).
% 7.95/2.75  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.95/2.75  tff(c_1287, plain, (![A_146, A_147]: (k3_xboole_0(k6_relat_1(A_146), k6_relat_1(A_147))=k6_relat_1(A_146) | ~r1_tarski(A_146, A_147))), inference(resolution, [status(thm)], [c_533, c_2])).
% 7.95/2.75  tff(c_1568, plain, (![A_154, A_155]: (k3_xboole_0(k6_relat_1(A_154), k6_relat_1(A_155))=k6_relat_1(A_155) | ~r1_tarski(A_155, A_154))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1287])).
% 7.95/2.75  tff(c_537, plain, (![A_101, A_102]: (k3_xboole_0(k6_relat_1(A_101), k6_relat_1(A_102))=k6_relat_1(A_101) | ~r1_tarski(A_101, A_102))), inference(resolution, [status(thm)], [c_533, c_2])).
% 7.95/2.75  tff(c_1577, plain, (![A_155, A_154]: (k6_relat_1(A_155)=k6_relat_1(A_154) | ~r1_tarski(A_154, A_155) | ~r1_tarski(A_155, A_154))), inference(superposition, [status(thm), theory('equality')], [c_1568, c_537])).
% 7.95/2.75  tff(c_8105, plain, (![A_277, B_278]: (k6_relat_1(k7_relat_1(k6_relat_1(A_277), B_278))=k6_relat_1(k6_relat_1(k3_xboole_0(A_277, B_278))) | ~r1_tarski(k7_relat_1(k6_relat_1(A_277), B_278), k6_relat_1(k3_xboole_0(A_277, B_278))))), inference(resolution, [status(thm)], [c_8097, c_1577])).
% 7.95/2.75  tff(c_8232, plain, (![A_277, B_278]: (k6_relat_1(k7_relat_1(k6_relat_1(A_277), B_278))=k6_relat_1(k6_relat_1(k3_xboole_0(A_277, B_278))))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_8105])).
% 7.95/2.75  tff(c_36, plain, (![A_34, B_35]: (r1_tarski(k5_relat_1(k6_relat_1(A_34), B_35), B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.95/2.75  tff(c_286, plain, (![B_75, A_74]: (r1_tarski(k7_relat_1(B_75, A_74), B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_276, c_36])).
% 7.95/2.75  tff(c_549, plain, (![A_104, B_105]: (r1_tarski(k1_relat_1(A_104), k1_relat_1(B_105)) | ~r1_tarski(A_104, B_105) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.95/2.75  tff(c_561, plain, (![A_104, A_32]: (r1_tarski(k1_relat_1(A_104), A_32) | ~r1_tarski(A_104, k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_30, c_549])).
% 7.95/2.75  tff(c_729, plain, (![A_123, A_124]: (r1_tarski(k1_relat_1(A_123), A_124) | ~r1_tarski(A_123, k6_relat_1(A_124)) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_561])).
% 7.95/2.75  tff(c_42, plain, (![B_39, A_38]: (k7_relat_1(B_39, A_38)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.95/2.75  tff(c_834, plain, (![A_132, A_133]: (k7_relat_1(A_132, A_133)=A_132 | ~r1_tarski(A_132, k6_relat_1(A_133)) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_729, c_42])).
% 7.95/2.75  tff(c_857, plain, (![A_133, A_74]: (k7_relat_1(k7_relat_1(k6_relat_1(A_133), A_74), A_133)=k7_relat_1(k6_relat_1(A_133), A_74) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_133), A_74)) | ~v1_relat_1(k6_relat_1(A_133)))), inference(resolution, [status(thm)], [c_286, c_834])).
% 7.95/2.75  tff(c_885, plain, (![A_133, A_74]: (k7_relat_1(k7_relat_1(k6_relat_1(A_133), A_74), A_133)=k7_relat_1(k6_relat_1(A_133), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_422, c_857])).
% 7.95/2.75  tff(c_2961, plain, (![A_133, A_74]: (r1_tarski(k7_relat_1(k6_relat_1(A_133), A_74), k7_relat_1(k6_relat_1(A_74), A_133)))), inference(superposition, [status(thm), theory('equality')], [c_885, c_2941])).
% 7.95/2.75  tff(c_3230, plain, (![A_206, A_207]: (r1_tarski(k7_relat_1(k6_relat_1(A_206), A_207), k7_relat_1(k6_relat_1(A_207), A_206)))), inference(superposition, [status(thm), theory('equality')], [c_885, c_2941])).
% 7.95/2.75  tff(c_3232, plain, (![A_207, A_206]: (k6_relat_1(k7_relat_1(k6_relat_1(A_207), A_206))=k6_relat_1(k7_relat_1(k6_relat_1(A_206), A_207)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_207), A_206), k7_relat_1(k6_relat_1(A_206), A_207)))), inference(resolution, [status(thm)], [c_3230, c_1577])).
% 7.95/2.75  tff(c_3369, plain, (![A_211, A_210]: (k6_relat_1(k7_relat_1(k6_relat_1(A_211), A_210))=k6_relat_1(k7_relat_1(k6_relat_1(A_210), A_211)))), inference(demodulation, [status(thm), theory('equality')], [c_2961, c_3232])).
% 7.95/2.75  tff(c_3719, plain, (![A_210, A_211]: (k2_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_210), A_211)))=k7_relat_1(k6_relat_1(A_211), A_210))), inference(superposition, [status(thm), theory('equality')], [c_3369, c_32])).
% 7.95/2.75  tff(c_10032, plain, (![A_210, A_211]: (k2_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_210, A_211))))=k7_relat_1(k6_relat_1(A_211), A_210))), inference(demodulation, [status(thm), theory('equality')], [c_8232, c_3719])).
% 7.95/2.75  tff(c_10035, plain, (![A_211, A_210]: (k7_relat_1(k6_relat_1(A_211), A_210)=k6_relat_1(k3_xboole_0(A_210, A_211)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10032])).
% 7.95/2.75  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.95/2.75  tff(c_293, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_46])).
% 7.95/2.75  tff(c_307, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_293])).
% 7.95/2.75  tff(c_10522, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10035, c_307])).
% 7.95/2.75  tff(c_10543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_10522])).
% 7.95/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/2.75  
% 7.95/2.75  Inference rules
% 7.95/2.75  ----------------------
% 7.95/2.75  #Ref     : 0
% 7.95/2.75  #Sup     : 2487
% 7.95/2.75  #Fact    : 0
% 7.95/2.75  #Define  : 0
% 7.95/2.75  #Split   : 2
% 7.95/2.75  #Chain   : 0
% 7.95/2.75  #Close   : 0
% 7.95/2.75  
% 7.95/2.75  Ordering : KBO
% 7.95/2.75  
% 7.95/2.75  Simplification rules
% 7.95/2.75  ----------------------
% 7.95/2.75  #Subsume      : 300
% 7.95/2.75  #Demod        : 2427
% 7.95/2.75  #Tautology    : 906
% 7.95/2.75  #SimpNegUnit  : 0
% 7.95/2.75  #BackRed      : 57
% 7.95/2.75  
% 7.95/2.75  #Partial instantiations: 0
% 7.95/2.75  #Strategies tried      : 1
% 7.95/2.75  
% 7.95/2.75  Timing (in seconds)
% 7.95/2.75  ----------------------
% 7.95/2.75  Preprocessing        : 0.33
% 7.95/2.75  Parsing              : 0.18
% 7.95/2.75  CNF conversion       : 0.02
% 7.95/2.75  Main loop            : 1.65
% 7.95/2.75  Inferencing          : 0.47
% 7.95/2.75  Reduction            : 0.72
% 7.95/2.75  Demodulation         : 0.59
% 7.95/2.75  BG Simplification    : 0.07
% 7.95/2.75  Subsumption          : 0.29
% 7.95/2.75  Abstraction          : 0.09
% 7.95/2.75  MUC search           : 0.00
% 7.95/2.75  Cooper               : 0.00
% 7.95/2.75  Total                : 2.02
% 7.95/2.75  Index Insertion      : 0.00
% 7.95/2.75  Index Deletion       : 0.00
% 7.95/2.75  Index Matching       : 0.00
% 7.95/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

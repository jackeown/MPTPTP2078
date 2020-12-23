%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  122 (1135 expanded)
%              Number of leaves         :   38 ( 418 expanded)
%              Depth                    :   20
%              Number of atoms          :  176 (1855 expanded)
%              Number of equality atoms :   75 ( 687 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_94,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_102,plain,(
    ! [A_53] :
      ( k7_relat_1(A_53,k1_relat_1(A_53)) = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,(
    ! [A_39] :
      ( k7_relat_1(k6_relat_1(A_39),A_39) = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_115,plain,(
    ! [A_39] : k7_relat_1(k6_relat_1(A_39),A_39) = k6_relat_1(A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_571,plain,(
    ! [C_120,A_121,B_122] :
      ( k7_relat_1(k7_relat_1(C_120,A_121),B_122) = k7_relat_1(C_120,k3_xboole_0(A_121,B_122))
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_599,plain,(
    ! [A_39,B_122] :
      ( k7_relat_1(k6_relat_1(A_39),k3_xboole_0(A_39,B_122)) = k7_relat_1(k6_relat_1(A_39),B_122)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_571])).

tff(c_612,plain,(
    ! [A_39,B_122] : k7_relat_1(k6_relat_1(A_39),k3_xboole_0(A_39,B_122)) = k7_relat_1(k6_relat_1(A_39),B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_599])).

tff(c_216,plain,(
    ! [A_84,B_85] :
      ( k5_relat_1(k6_relat_1(A_84),B_85) = k7_relat_1(B_85,A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [B_30,A_29] :
      ( k5_relat_1(B_30,k6_relat_1(A_29)) = k8_relat_1(A_29,B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_230,plain,(
    ! [A_29,A_84] :
      ( k8_relat_1(A_29,k6_relat_1(A_84)) = k7_relat_1(k6_relat_1(A_29),A_84)
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_26])).

tff(c_252,plain,(
    ! [A_29,A_84] : k8_relat_1(A_29,k6_relat_1(A_84)) = k7_relat_1(k6_relat_1(A_29),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_230])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k5_relat_1(B_42,k6_relat_1(A_41)),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_178,plain,(
    ! [A_69,B_70] :
      ( v1_relat_1(A_69)
      | ~ v1_relat_1(B_70)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_185,plain,(
    ! [B_42,A_41] :
      ( v1_relat_1(k5_relat_1(B_42,k6_relat_1(A_41)))
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_226,plain,(
    ! [A_41,A_84] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_84))
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_185])).

tff(c_250,plain,(
    ! [A_41,A_84] : v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_226])).

tff(c_38,plain,(
    ! [A_39] : k2_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_260,plain,(
    ! [B_86,A_87] :
      ( k3_xboole_0(k2_relat_1(B_86),A_87) = k2_relat_1(k8_relat_1(A_87,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_269,plain,(
    ! [A_87,A_39] :
      ( k2_relat_1(k8_relat_1(A_87,k6_relat_1(A_39))) = k3_xboole_0(A_39,A_87)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_260])).

tff(c_273,plain,(
    ! [A_87,A_39] : k2_relat_1(k8_relat_1(A_87,k6_relat_1(A_39))) = k3_xboole_0(A_39,A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_269])).

tff(c_343,plain,(
    ! [A_87,A_39] : k2_relat_1(k7_relat_1(k6_relat_1(A_87),A_39)) = k3_xboole_0(A_39,A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_273])).

tff(c_46,plain,(
    ! [A_43,B_44] :
      ( k5_relat_1(k6_relat_1(A_43),B_44) = k7_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    ! [A_40] : k4_relat_1(k6_relat_1(A_40)) = k6_relat_1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_801,plain,(
    ! [B_133,A_134] :
      ( k5_relat_1(k4_relat_1(B_133),k4_relat_1(A_134)) = k4_relat_1(k5_relat_1(A_134,B_133))
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_816,plain,(
    ! [A_40,A_134] :
      ( k5_relat_1(k6_relat_1(A_40),k4_relat_1(A_134)) = k4_relat_1(k5_relat_1(A_134,k6_relat_1(A_40)))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_801])).

tff(c_1635,plain,(
    ! [A_177,A_178] :
      ( k5_relat_1(k6_relat_1(A_177),k4_relat_1(A_178)) = k4_relat_1(k5_relat_1(A_178,k6_relat_1(A_177)))
      | ~ v1_relat_1(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_816])).

tff(c_1660,plain,(
    ! [A_40,A_177] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_40),k6_relat_1(A_177))) = k5_relat_1(k6_relat_1(A_177),k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1635])).

tff(c_2342,plain,(
    ! [A_199,A_200] : k4_relat_1(k5_relat_1(k6_relat_1(A_199),k6_relat_1(A_200))) = k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_199)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1660])).

tff(c_2367,plain,(
    ! [A_200,A_43] :
      ( k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_43)) = k4_relat_1(k7_relat_1(k6_relat_1(A_200),A_43))
      | ~ v1_relat_1(k6_relat_1(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2342])).

tff(c_2381,plain,(
    ! [A_201,A_202] : k5_relat_1(k6_relat_1(A_201),k6_relat_1(A_202)) = k4_relat_1(k7_relat_1(k6_relat_1(A_201),A_202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2367])).

tff(c_2419,plain,(
    ! [A_201,A_29] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_201),A_29)) = k8_relat_1(A_29,k6_relat_1(A_201))
      | ~ v1_relat_1(k6_relat_1(A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2381])).

tff(c_2441,plain,(
    ! [A_201,A_29] : k4_relat_1(k7_relat_1(k6_relat_1(A_201),A_29)) = k7_relat_1(k6_relat_1(A_29),A_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_252,c_2419])).

tff(c_2564,plain,(
    ! [A_209,A_210] : k4_relat_1(k7_relat_1(k6_relat_1(A_209),A_210)) = k7_relat_1(k6_relat_1(A_210),A_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_252,c_2419])).

tff(c_2592,plain,(
    ! [A_39,B_122] : k7_relat_1(k6_relat_1(k3_xboole_0(A_39,B_122)),A_39) = k4_relat_1(k7_relat_1(k6_relat_1(A_39),B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_2564])).

tff(c_3002,plain,(
    ! [A_221,B_222] : k7_relat_1(k6_relat_1(k3_xboole_0(A_221,B_222)),A_221) = k7_relat_1(k6_relat_1(B_222),A_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_2592])).

tff(c_3041,plain,(
    ! [A_221,B_222] : k3_xboole_0(A_221,k3_xboole_0(A_221,B_222)) = k2_relat_1(k7_relat_1(k6_relat_1(B_222),A_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3002,c_343])).

tff(c_3115,plain,(
    ! [A_221,B_222] : k3_xboole_0(A_221,k3_xboole_0(A_221,B_222)) = k3_xboole_0(A_221,B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_3041])).

tff(c_868,plain,(
    ! [A_141,B_142] : k7_relat_1(k6_relat_1(A_141),k3_xboole_0(A_141,B_142)) = k7_relat_1(k6_relat_1(A_141),B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_599])).

tff(c_886,plain,(
    ! [A_141,B_142] : k3_xboole_0(k3_xboole_0(A_141,B_142),A_141) = k2_relat_1(k7_relat_1(k6_relat_1(A_141),B_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_343])).

tff(c_915,plain,(
    ! [A_141,B_142] : k3_xboole_0(k3_xboole_0(A_141,B_142),A_141) = k3_xboole_0(B_142,A_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_886])).

tff(c_234,plain,(
    ! [A_41,A_84] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_41),A_84),k6_relat_1(A_84))
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_44])).

tff(c_254,plain,(
    ! [A_41,A_84] : r1_tarski(k7_relat_1(k6_relat_1(A_41),A_84),k6_relat_1(A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_234])).

tff(c_537,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k2_relat_1(A_118),k2_relat_1(B_119))
      | ~ r1_tarski(A_118,B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_558,plain,(
    ! [A_118,A_39] :
      ( r1_tarski(k2_relat_1(A_118),A_39)
      | ~ r1_tarski(A_118,k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_537])).

tff(c_671,plain,(
    ! [A_125,A_126] :
      ( r1_tarski(k2_relat_1(A_125),A_126)
      | ~ r1_tarski(A_125,k6_relat_1(A_126))
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_558])).

tff(c_28,plain,(
    ! [A_31,B_32] :
      ( k8_relat_1(A_31,B_32) = B_32
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_991,plain,(
    ! [A_152,A_153] :
      ( k8_relat_1(A_152,A_153) = A_153
      | ~ r1_tarski(A_153,k6_relat_1(A_152))
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_671,c_28])).

tff(c_1023,plain,(
    ! [A_84,A_41] :
      ( k8_relat_1(A_84,k7_relat_1(k6_relat_1(A_41),A_84)) = k7_relat_1(k6_relat_1(A_41),A_84)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_84)) ) ),
    inference(resolution,[status(thm)],[c_254,c_991])).

tff(c_1054,plain,(
    ! [A_84,A_41] : k8_relat_1(A_84,k7_relat_1(k6_relat_1(A_41),A_84)) = k7_relat_1(k6_relat_1(A_41),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1023])).

tff(c_24,plain,(
    ! [B_28,A_27] :
      ( k3_xboole_0(k2_relat_1(B_28),A_27) = k2_relat_1(k8_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_344,plain,(
    ! [A_97,A_98] : k2_relat_1(k7_relat_1(k6_relat_1(A_97),A_98)) = k3_xboole_0(A_98,A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_273])).

tff(c_356,plain,(
    ! [A_39] : k3_xboole_0(A_39,A_39) = k2_relat_1(k6_relat_1(A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_344])).

tff(c_365,plain,(
    ! [A_39] : k3_xboole_0(A_39,A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_356])).

tff(c_155,plain,(
    ! [B_67,A_68] :
      ( k5_relat_1(B_67,k6_relat_1(A_68)) = k8_relat_1(A_68,B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_41),B_42),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_165,plain,(
    ! [A_68,A_41] :
      ( r1_tarski(k8_relat_1(A_68,k6_relat_1(A_41)),k6_relat_1(A_68))
      | ~ v1_relat_1(k6_relat_1(A_68))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_42])).

tff(c_174,plain,(
    ! [A_68,A_41] : r1_tarski(k8_relat_1(A_68,k6_relat_1(A_41)),k6_relat_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_165])).

tff(c_310,plain,(
    ! [A_68,A_41] : r1_tarski(k7_relat_1(k6_relat_1(A_68),A_41),k6_relat_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_174])).

tff(c_1020,plain,(
    ! [A_68,A_41] :
      ( k8_relat_1(A_68,k7_relat_1(k6_relat_1(A_68),A_41)) = k7_relat_1(k6_relat_1(A_68),A_41)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)) ) ),
    inference(resolution,[status(thm)],[c_310,c_991])).

tff(c_1051,plain,(
    ! [A_68,A_41] : k8_relat_1(A_68,k7_relat_1(k6_relat_1(A_68),A_41)) = k7_relat_1(k6_relat_1(A_68),A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1020])).

tff(c_920,plain,(
    ! [A_143,B_144] : k3_xboole_0(k3_xboole_0(A_143,B_144),A_143) = k3_xboole_0(B_144,A_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_886])).

tff(c_7988,plain,(
    ! [A_328,B_329] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_328,B_329)),k2_relat_1(B_329)) = k3_xboole_0(A_328,k2_relat_1(B_329))
      | ~ v1_relat_1(B_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_920])).

tff(c_8097,plain,(
    ! [A_68,A_41] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)),k2_relat_1(k7_relat_1(k6_relat_1(A_68),A_41))) = k3_xboole_0(A_68,k2_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_7988])).

tff(c_8146,plain,(
    ! [A_330,A_331] : k3_xboole_0(A_330,k3_xboole_0(A_331,A_330)) = k3_xboole_0(A_331,A_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_365,c_343,c_343,c_343,c_8097])).

tff(c_8894,plain,(
    ! [A_344,B_345] :
      ( k3_xboole_0(A_344,k2_relat_1(k8_relat_1(A_344,B_345))) = k3_xboole_0(k2_relat_1(B_345),A_344)
      | ~ v1_relat_1(B_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8146])).

tff(c_9017,plain,(
    ! [A_41,A_84] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_41),A_84)),A_84) = k3_xboole_0(A_84,k2_relat_1(k7_relat_1(k6_relat_1(A_41),A_84)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_8894])).

tff(c_9042,plain,(
    ! [A_84,A_41] : k3_xboole_0(A_84,A_41) = k3_xboole_0(A_41,A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_3115,c_915,c_343,c_343,c_9017])).

tff(c_8131,plain,(
    ! [A_68,A_41] : k3_xboole_0(A_68,k3_xboole_0(A_41,A_68)) = k3_xboole_0(A_41,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_365,c_343,c_343,c_343,c_8097])).

tff(c_9011,plain,(
    ! [A_68,A_41] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)),A_68) = k3_xboole_0(A_68,k2_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_68),A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_8894])).

tff(c_9398,plain,(
    ! [A_348,A_349] : k3_xboole_0(k3_xboole_0(A_348,A_349),A_349) = k3_xboole_0(A_348,A_349) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_8131,c_343,c_343,c_9011])).

tff(c_9497,plain,(
    ! [A_348,A_349] : k7_relat_1(k6_relat_1(k3_xboole_0(A_348,A_349)),k3_xboole_0(A_348,A_349)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_348,A_349)),A_349) ),
    inference(superposition,[status(thm),theory(equality)],[c_9398,c_612])).

tff(c_10263,plain,(
    ! [A_356,A_357] : k7_relat_1(k6_relat_1(k3_xboole_0(A_356,A_357)),A_357) = k6_relat_1(k3_xboole_0(A_356,A_357)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_9497])).

tff(c_10793,plain,(
    ! [A_361,A_362] : r1_tarski(k6_relat_1(k3_xboole_0(A_361,A_362)),k6_relat_1(A_362)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10263,c_254])).

tff(c_11254,plain,(
    ! [A_369,A_370] : r1_tarski(k6_relat_1(k3_xboole_0(A_369,A_370)),k6_relat_1(A_369)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9042,c_10793])).

tff(c_691,plain,(
    ! [A_126,A_125] :
      ( k8_relat_1(A_126,A_125) = A_125
      | ~ r1_tarski(A_125,k6_relat_1(A_126))
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_671,c_28])).

tff(c_11277,plain,(
    ! [A_369,A_370] :
      ( k8_relat_1(A_369,k6_relat_1(k3_xboole_0(A_369,A_370))) = k6_relat_1(k3_xboole_0(A_369,A_370))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_369,A_370))) ) ),
    inference(resolution,[status(thm)],[c_11254,c_691])).

tff(c_11379,plain,(
    ! [A_369,A_370] : k7_relat_1(k6_relat_1(A_369),A_370) = k6_relat_1(k3_xboole_0(A_369,A_370)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_612,c_252,c_11277])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_240,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_50])).

tff(c_256,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_240])).

tff(c_11960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11379,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.73  
% 7.69/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.73  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.69/2.73  
% 7.69/2.73  %Foreground sorts:
% 7.69/2.73  
% 7.69/2.73  
% 7.69/2.73  %Background operators:
% 7.69/2.73  
% 7.69/2.73  
% 7.69/2.73  %Foreground operators:
% 7.69/2.73  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.69/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.69/2.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.69/2.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.69/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.69/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.69/2.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.69/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.69/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.69/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.69/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.69/2.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.69/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.69/2.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.69/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.69/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.69/2.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.69/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.69/2.73  
% 7.69/2.75  tff(f_48, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.69/2.75  tff(f_92, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.69/2.75  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.69/2.75  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 7.69/2.75  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.69/2.75  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 7.69/2.75  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 7.69/2.75  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.69/2.75  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.69/2.75  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 7.69/2.75  tff(f_94, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 7.69/2.75  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 7.69/2.75  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 7.69/2.75  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 7.69/2.75  tff(f_111, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 7.69/2.75  tff(c_18, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.69/2.75  tff(c_36, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.69/2.75  tff(c_102, plain, (![A_53]: (k7_relat_1(A_53, k1_relat_1(A_53))=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.69/2.75  tff(c_111, plain, (![A_39]: (k7_relat_1(k6_relat_1(A_39), A_39)=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_102])).
% 7.69/2.75  tff(c_115, plain, (![A_39]: (k7_relat_1(k6_relat_1(A_39), A_39)=k6_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_111])).
% 7.69/2.75  tff(c_571, plain, (![C_120, A_121, B_122]: (k7_relat_1(k7_relat_1(C_120, A_121), B_122)=k7_relat_1(C_120, k3_xboole_0(A_121, B_122)) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.69/2.75  tff(c_599, plain, (![A_39, B_122]: (k7_relat_1(k6_relat_1(A_39), k3_xboole_0(A_39, B_122))=k7_relat_1(k6_relat_1(A_39), B_122) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_571])).
% 7.69/2.75  tff(c_612, plain, (![A_39, B_122]: (k7_relat_1(k6_relat_1(A_39), k3_xboole_0(A_39, B_122))=k7_relat_1(k6_relat_1(A_39), B_122))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_599])).
% 7.69/2.75  tff(c_216, plain, (![A_84, B_85]: (k5_relat_1(k6_relat_1(A_84), B_85)=k7_relat_1(B_85, A_84) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.69/2.75  tff(c_26, plain, (![B_30, A_29]: (k5_relat_1(B_30, k6_relat_1(A_29))=k8_relat_1(A_29, B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.69/2.75  tff(c_230, plain, (![A_29, A_84]: (k8_relat_1(A_29, k6_relat_1(A_84))=k7_relat_1(k6_relat_1(A_29), A_84) | ~v1_relat_1(k6_relat_1(A_84)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_26])).
% 7.69/2.75  tff(c_252, plain, (![A_29, A_84]: (k8_relat_1(A_29, k6_relat_1(A_84))=k7_relat_1(k6_relat_1(A_29), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_230])).
% 7.69/2.75  tff(c_44, plain, (![B_42, A_41]: (r1_tarski(k5_relat_1(B_42, k6_relat_1(A_41)), B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.69/2.75  tff(c_14, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.69/2.75  tff(c_150, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.69/2.75  tff(c_178, plain, (![A_69, B_70]: (v1_relat_1(A_69) | ~v1_relat_1(B_70) | ~r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_14, c_150])).
% 7.69/2.75  tff(c_185, plain, (![B_42, A_41]: (v1_relat_1(k5_relat_1(B_42, k6_relat_1(A_41))) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_44, c_178])).
% 7.69/2.75  tff(c_226, plain, (![A_41, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_84)) | ~v1_relat_1(k6_relat_1(A_84)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_185])).
% 7.69/2.75  tff(c_250, plain, (![A_41, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_226])).
% 7.69/2.75  tff(c_38, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.69/2.75  tff(c_260, plain, (![B_86, A_87]: (k3_xboole_0(k2_relat_1(B_86), A_87)=k2_relat_1(k8_relat_1(A_87, B_86)) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.69/2.75  tff(c_269, plain, (![A_87, A_39]: (k2_relat_1(k8_relat_1(A_87, k6_relat_1(A_39)))=k3_xboole_0(A_39, A_87) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_260])).
% 7.69/2.75  tff(c_273, plain, (![A_87, A_39]: (k2_relat_1(k8_relat_1(A_87, k6_relat_1(A_39)))=k3_xboole_0(A_39, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_269])).
% 7.69/2.75  tff(c_343, plain, (![A_87, A_39]: (k2_relat_1(k7_relat_1(k6_relat_1(A_87), A_39))=k3_xboole_0(A_39, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_273])).
% 7.69/2.75  tff(c_46, plain, (![A_43, B_44]: (k5_relat_1(k6_relat_1(A_43), B_44)=k7_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.69/2.75  tff(c_40, plain, (![A_40]: (k4_relat_1(k6_relat_1(A_40))=k6_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.69/2.75  tff(c_801, plain, (![B_133, A_134]: (k5_relat_1(k4_relat_1(B_133), k4_relat_1(A_134))=k4_relat_1(k5_relat_1(A_134, B_133)) | ~v1_relat_1(B_133) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.75  tff(c_816, plain, (![A_40, A_134]: (k5_relat_1(k6_relat_1(A_40), k4_relat_1(A_134))=k4_relat_1(k5_relat_1(A_134, k6_relat_1(A_40))) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_40, c_801])).
% 7.69/2.75  tff(c_1635, plain, (![A_177, A_178]: (k5_relat_1(k6_relat_1(A_177), k4_relat_1(A_178))=k4_relat_1(k5_relat_1(A_178, k6_relat_1(A_177))) | ~v1_relat_1(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_816])).
% 7.69/2.75  tff(c_1660, plain, (![A_40, A_177]: (k4_relat_1(k5_relat_1(k6_relat_1(A_40), k6_relat_1(A_177)))=k5_relat_1(k6_relat_1(A_177), k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1635])).
% 7.69/2.75  tff(c_2342, plain, (![A_199, A_200]: (k4_relat_1(k5_relat_1(k6_relat_1(A_199), k6_relat_1(A_200)))=k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_199)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1660])).
% 7.69/2.75  tff(c_2367, plain, (![A_200, A_43]: (k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_43))=k4_relat_1(k7_relat_1(k6_relat_1(A_200), A_43)) | ~v1_relat_1(k6_relat_1(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2342])).
% 7.69/2.75  tff(c_2381, plain, (![A_201, A_202]: (k5_relat_1(k6_relat_1(A_201), k6_relat_1(A_202))=k4_relat_1(k7_relat_1(k6_relat_1(A_201), A_202)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2367])).
% 7.69/2.75  tff(c_2419, plain, (![A_201, A_29]: (k4_relat_1(k7_relat_1(k6_relat_1(A_201), A_29))=k8_relat_1(A_29, k6_relat_1(A_201)) | ~v1_relat_1(k6_relat_1(A_201)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2381])).
% 7.69/2.75  tff(c_2441, plain, (![A_201, A_29]: (k4_relat_1(k7_relat_1(k6_relat_1(A_201), A_29))=k7_relat_1(k6_relat_1(A_29), A_201))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_252, c_2419])).
% 7.69/2.75  tff(c_2564, plain, (![A_209, A_210]: (k4_relat_1(k7_relat_1(k6_relat_1(A_209), A_210))=k7_relat_1(k6_relat_1(A_210), A_209))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_252, c_2419])).
% 7.69/2.75  tff(c_2592, plain, (![A_39, B_122]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_39, B_122)), A_39)=k4_relat_1(k7_relat_1(k6_relat_1(A_39), B_122)))), inference(superposition, [status(thm), theory('equality')], [c_612, c_2564])).
% 7.69/2.75  tff(c_3002, plain, (![A_221, B_222]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_221, B_222)), A_221)=k7_relat_1(k6_relat_1(B_222), A_221))), inference(demodulation, [status(thm), theory('equality')], [c_2441, c_2592])).
% 7.69/2.75  tff(c_3041, plain, (![A_221, B_222]: (k3_xboole_0(A_221, k3_xboole_0(A_221, B_222))=k2_relat_1(k7_relat_1(k6_relat_1(B_222), A_221)))), inference(superposition, [status(thm), theory('equality')], [c_3002, c_343])).
% 7.69/2.75  tff(c_3115, plain, (![A_221, B_222]: (k3_xboole_0(A_221, k3_xboole_0(A_221, B_222))=k3_xboole_0(A_221, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_3041])).
% 7.69/2.75  tff(c_868, plain, (![A_141, B_142]: (k7_relat_1(k6_relat_1(A_141), k3_xboole_0(A_141, B_142))=k7_relat_1(k6_relat_1(A_141), B_142))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_599])).
% 7.69/2.75  tff(c_886, plain, (![A_141, B_142]: (k3_xboole_0(k3_xboole_0(A_141, B_142), A_141)=k2_relat_1(k7_relat_1(k6_relat_1(A_141), B_142)))), inference(superposition, [status(thm), theory('equality')], [c_868, c_343])).
% 7.69/2.75  tff(c_915, plain, (![A_141, B_142]: (k3_xboole_0(k3_xboole_0(A_141, B_142), A_141)=k3_xboole_0(B_142, A_141))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_886])).
% 7.69/2.75  tff(c_234, plain, (![A_41, A_84]: (r1_tarski(k7_relat_1(k6_relat_1(A_41), A_84), k6_relat_1(A_84)) | ~v1_relat_1(k6_relat_1(A_84)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_44])).
% 7.69/2.75  tff(c_254, plain, (![A_41, A_84]: (r1_tarski(k7_relat_1(k6_relat_1(A_41), A_84), k6_relat_1(A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_234])).
% 7.69/2.75  tff(c_537, plain, (![A_118, B_119]: (r1_tarski(k2_relat_1(A_118), k2_relat_1(B_119)) | ~r1_tarski(A_118, B_119) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.69/2.75  tff(c_558, plain, (![A_118, A_39]: (r1_tarski(k2_relat_1(A_118), A_39) | ~r1_tarski(A_118, k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_38, c_537])).
% 7.69/2.75  tff(c_671, plain, (![A_125, A_126]: (r1_tarski(k2_relat_1(A_125), A_126) | ~r1_tarski(A_125, k6_relat_1(A_126)) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_558])).
% 7.69/2.75  tff(c_28, plain, (![A_31, B_32]: (k8_relat_1(A_31, B_32)=B_32 | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.69/2.75  tff(c_991, plain, (![A_152, A_153]: (k8_relat_1(A_152, A_153)=A_153 | ~r1_tarski(A_153, k6_relat_1(A_152)) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_671, c_28])).
% 7.69/2.75  tff(c_1023, plain, (![A_84, A_41]: (k8_relat_1(A_84, k7_relat_1(k6_relat_1(A_41), A_84))=k7_relat_1(k6_relat_1(A_41), A_84) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_84)))), inference(resolution, [status(thm)], [c_254, c_991])).
% 7.69/2.75  tff(c_1054, plain, (![A_84, A_41]: (k8_relat_1(A_84, k7_relat_1(k6_relat_1(A_41), A_84))=k7_relat_1(k6_relat_1(A_41), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_1023])).
% 7.69/2.75  tff(c_24, plain, (![B_28, A_27]: (k3_xboole_0(k2_relat_1(B_28), A_27)=k2_relat_1(k8_relat_1(A_27, B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.69/2.75  tff(c_344, plain, (![A_97, A_98]: (k2_relat_1(k7_relat_1(k6_relat_1(A_97), A_98))=k3_xboole_0(A_98, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_273])).
% 7.69/2.75  tff(c_356, plain, (![A_39]: (k3_xboole_0(A_39, A_39)=k2_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_344])).
% 7.69/2.75  tff(c_365, plain, (![A_39]: (k3_xboole_0(A_39, A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_356])).
% 7.69/2.75  tff(c_155, plain, (![B_67, A_68]: (k5_relat_1(B_67, k6_relat_1(A_68))=k8_relat_1(A_68, B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.69/2.75  tff(c_42, plain, (![A_41, B_42]: (r1_tarski(k5_relat_1(k6_relat_1(A_41), B_42), B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.69/2.75  tff(c_165, plain, (![A_68, A_41]: (r1_tarski(k8_relat_1(A_68, k6_relat_1(A_41)), k6_relat_1(A_68)) | ~v1_relat_1(k6_relat_1(A_68)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_42])).
% 7.69/2.75  tff(c_174, plain, (![A_68, A_41]: (r1_tarski(k8_relat_1(A_68, k6_relat_1(A_41)), k6_relat_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_165])).
% 7.69/2.75  tff(c_310, plain, (![A_68, A_41]: (r1_tarski(k7_relat_1(k6_relat_1(A_68), A_41), k6_relat_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_174])).
% 7.69/2.75  tff(c_1020, plain, (![A_68, A_41]: (k8_relat_1(A_68, k7_relat_1(k6_relat_1(A_68), A_41))=k7_relat_1(k6_relat_1(A_68), A_41) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)))), inference(resolution, [status(thm)], [c_310, c_991])).
% 7.69/2.75  tff(c_1051, plain, (![A_68, A_41]: (k8_relat_1(A_68, k7_relat_1(k6_relat_1(A_68), A_41))=k7_relat_1(k6_relat_1(A_68), A_41))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_1020])).
% 7.69/2.75  tff(c_920, plain, (![A_143, B_144]: (k3_xboole_0(k3_xboole_0(A_143, B_144), A_143)=k3_xboole_0(B_144, A_143))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_886])).
% 7.69/2.75  tff(c_7988, plain, (![A_328, B_329]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_328, B_329)), k2_relat_1(B_329))=k3_xboole_0(A_328, k2_relat_1(B_329)) | ~v1_relat_1(B_329))), inference(superposition, [status(thm), theory('equality')], [c_24, c_920])).
% 7.69/2.75  tff(c_8097, plain, (![A_68, A_41]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)), k2_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)))=k3_xboole_0(A_68, k2_relat_1(k7_relat_1(k6_relat_1(A_68), A_41))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_7988])).
% 7.69/2.75  tff(c_8146, plain, (![A_330, A_331]: (k3_xboole_0(A_330, k3_xboole_0(A_331, A_330))=k3_xboole_0(A_331, A_330))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_365, c_343, c_343, c_343, c_8097])).
% 7.69/2.75  tff(c_8894, plain, (![A_344, B_345]: (k3_xboole_0(A_344, k2_relat_1(k8_relat_1(A_344, B_345)))=k3_xboole_0(k2_relat_1(B_345), A_344) | ~v1_relat_1(B_345))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8146])).
% 7.69/2.75  tff(c_9017, plain, (![A_41, A_84]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_41), A_84)), A_84)=k3_xboole_0(A_84, k2_relat_1(k7_relat_1(k6_relat_1(A_41), A_84))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_84)))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_8894])).
% 7.69/2.75  tff(c_9042, plain, (![A_84, A_41]: (k3_xboole_0(A_84, A_41)=k3_xboole_0(A_41, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_3115, c_915, c_343, c_343, c_9017])).
% 7.69/2.75  tff(c_8131, plain, (![A_68, A_41]: (k3_xboole_0(A_68, k3_xboole_0(A_41, A_68))=k3_xboole_0(A_41, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_365, c_343, c_343, c_343, c_8097])).
% 7.69/2.75  tff(c_9011, plain, (![A_68, A_41]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)), A_68)=k3_xboole_0(A_68, k2_relat_1(k7_relat_1(k6_relat_1(A_68), A_41))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_68), A_41)))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_8894])).
% 7.69/2.75  tff(c_9398, plain, (![A_348, A_349]: (k3_xboole_0(k3_xboole_0(A_348, A_349), A_349)=k3_xboole_0(A_348, A_349))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_8131, c_343, c_343, c_9011])).
% 7.69/2.75  tff(c_9497, plain, (![A_348, A_349]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_348, A_349)), k3_xboole_0(A_348, A_349))=k7_relat_1(k6_relat_1(k3_xboole_0(A_348, A_349)), A_349))), inference(superposition, [status(thm), theory('equality')], [c_9398, c_612])).
% 7.69/2.75  tff(c_10263, plain, (![A_356, A_357]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_356, A_357)), A_357)=k6_relat_1(k3_xboole_0(A_356, A_357)))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_9497])).
% 7.69/2.75  tff(c_10793, plain, (![A_361, A_362]: (r1_tarski(k6_relat_1(k3_xboole_0(A_361, A_362)), k6_relat_1(A_362)))), inference(superposition, [status(thm), theory('equality')], [c_10263, c_254])).
% 7.69/2.75  tff(c_11254, plain, (![A_369, A_370]: (r1_tarski(k6_relat_1(k3_xboole_0(A_369, A_370)), k6_relat_1(A_369)))), inference(superposition, [status(thm), theory('equality')], [c_9042, c_10793])).
% 7.69/2.75  tff(c_691, plain, (![A_126, A_125]: (k8_relat_1(A_126, A_125)=A_125 | ~r1_tarski(A_125, k6_relat_1(A_126)) | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_671, c_28])).
% 7.69/2.75  tff(c_11277, plain, (![A_369, A_370]: (k8_relat_1(A_369, k6_relat_1(k3_xboole_0(A_369, A_370)))=k6_relat_1(k3_xboole_0(A_369, A_370)) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_369, A_370))))), inference(resolution, [status(thm)], [c_11254, c_691])).
% 7.69/2.75  tff(c_11379, plain, (![A_369, A_370]: (k7_relat_1(k6_relat_1(A_369), A_370)=k6_relat_1(k3_xboole_0(A_369, A_370)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_612, c_252, c_11277])).
% 7.69/2.75  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.69/2.75  tff(c_240, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_50])).
% 7.69/2.75  tff(c_256, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_240])).
% 7.69/2.75  tff(c_11960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11379, c_256])).
% 7.69/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.75  
% 7.69/2.75  Inference rules
% 7.69/2.75  ----------------------
% 7.69/2.75  #Ref     : 0
% 7.69/2.75  #Sup     : 2864
% 7.69/2.75  #Fact    : 0
% 7.69/2.75  #Define  : 0
% 7.69/2.75  #Split   : 2
% 7.69/2.75  #Chain   : 0
% 7.69/2.75  #Close   : 0
% 7.69/2.75  
% 7.69/2.75  Ordering : KBO
% 7.69/2.75  
% 7.69/2.75  Simplification rules
% 7.69/2.75  ----------------------
% 7.69/2.75  #Subsume      : 515
% 7.69/2.75  #Demod        : 2942
% 7.69/2.75  #Tautology    : 1297
% 7.69/2.75  #SimpNegUnit  : 0
% 7.69/2.75  #BackRed      : 59
% 7.69/2.75  
% 7.69/2.75  #Partial instantiations: 0
% 7.69/2.75  #Strategies tried      : 1
% 7.69/2.75  
% 7.69/2.75  Timing (in seconds)
% 7.69/2.75  ----------------------
% 7.69/2.75  Preprocessing        : 0.38
% 7.69/2.75  Parsing              : 0.20
% 7.69/2.75  CNF conversion       : 0.02
% 7.69/2.75  Main loop            : 1.54
% 7.69/2.76  Inferencing          : 0.50
% 7.69/2.76  Reduction            : 0.58
% 7.69/2.76  Demodulation         : 0.46
% 7.69/2.76  BG Simplification    : 0.06
% 7.69/2.76  Subsumption          : 0.30
% 7.69/2.76  Abstraction          : 0.09
% 7.69/2.76  MUC search           : 0.00
% 7.69/2.76  Cooper               : 0.00
% 7.69/2.76  Total                : 1.95
% 7.69/2.76  Index Insertion      : 0.00
% 7.69/2.76  Index Deletion       : 0.00
% 7.69/2.76  Index Matching       : 0.00
% 7.69/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------

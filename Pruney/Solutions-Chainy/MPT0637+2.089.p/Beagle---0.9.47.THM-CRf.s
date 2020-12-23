%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 8.60s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 718 expanded)
%              Number of leaves         :   36 ( 273 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 (1290 expanded)
%              Number of equality atoms :   68 ( 406 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_88,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_28,plain,(
    ! [A_34] : k2_relat_1(k6_relat_1(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_152,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_relat_1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k5_relat_1(B_14,k6_relat_1(A_13)) = k8_relat_1(A_13,B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [A_13,A_66] :
      ( k8_relat_1(A_13,k6_relat_1(A_66)) = k7_relat_1(k6_relat_1(A_13),A_66)
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_12])).

tff(c_179,plain,(
    ! [A_13,A_66] : k8_relat_1(A_13,k6_relat_1(A_66)) = k7_relat_1(k6_relat_1(A_13),A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_159])).

tff(c_30,plain,(
    ! [A_35] : k4_relat_1(k6_relat_1(A_35)) = k6_relat_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_686,plain,(
    ! [B_116,A_117] :
      ( k5_relat_1(k4_relat_1(B_116),k4_relat_1(A_117)) = k4_relat_1(k5_relat_1(A_117,B_116))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_695,plain,(
    ! [A_35,A_117] :
      ( k5_relat_1(k6_relat_1(A_35),k4_relat_1(A_117)) = k4_relat_1(k5_relat_1(A_117,k6_relat_1(A_35)))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_686])).

tff(c_1161,plain,(
    ! [A_141,A_142] :
      ( k5_relat_1(k6_relat_1(A_141),k4_relat_1(A_142)) = k4_relat_1(k5_relat_1(A_142,k6_relat_1(A_141)))
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_695])).

tff(c_1186,plain,(
    ! [A_35,A_141] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_141))) = k5_relat_1(k6_relat_1(A_141),k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1161])).

tff(c_1320,plain,(
    ! [A_146,A_147] : k4_relat_1(k5_relat_1(k6_relat_1(A_146),k6_relat_1(A_147))) = k5_relat_1(k6_relat_1(A_147),k6_relat_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1186])).

tff(c_1360,plain,(
    ! [A_13,A_146] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_146)) = k4_relat_1(k8_relat_1(A_13,k6_relat_1(A_146)))
      | ~ v1_relat_1(k6_relat_1(A_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1320])).

tff(c_1697,plain,(
    ! [A_155,A_156] : k5_relat_1(k6_relat_1(A_155),k6_relat_1(A_156)) = k4_relat_1(k7_relat_1(k6_relat_1(A_155),A_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_179,c_1360])).

tff(c_1762,plain,(
    ! [A_40,A_156] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_40),A_156)) = k7_relat_1(k6_relat_1(A_156),A_40)
      | ~ v1_relat_1(k6_relat_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1697])).

tff(c_1796,plain,(
    ! [A_40,A_156] : k4_relat_1(k7_relat_1(k6_relat_1(A_40),A_156)) = k7_relat_1(k6_relat_1(A_156),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1762])).

tff(c_26,plain,(
    ! [A_34] : k1_relat_1(k6_relat_1(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    ! [A_55] :
      ( k7_relat_1(A_55,k1_relat_1(A_55)) = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_104,plain,(
    ! [A_34] :
      ( k7_relat_1(k6_relat_1(A_34),A_34) = k6_relat_1(A_34)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_95])).

tff(c_108,plain,(
    ! [A_34] : k7_relat_1(k6_relat_1(A_34),A_34) = k6_relat_1(A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_104])).

tff(c_376,plain,(
    ! [C_96,A_97,B_98] :
      ( k7_relat_1(k7_relat_1(C_96,A_97),B_98) = k7_relat_1(C_96,k3_xboole_0(A_97,B_98))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_401,plain,(
    ! [A_34,B_98] :
      ( k7_relat_1(k6_relat_1(A_34),k3_xboole_0(A_34,B_98)) = k7_relat_1(k6_relat_1(A_34),B_98)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_376])).

tff(c_414,plain,(
    ! [A_34,B_98] : k7_relat_1(k6_relat_1(A_34),k3_xboole_0(A_34,B_98)) = k7_relat_1(k6_relat_1(A_34),B_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_401])).

tff(c_32,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_36),B_37),B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1735,plain,(
    ! [A_155,A_156] :
      ( r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_155),A_156)),k6_relat_1(A_156))
      | ~ v1_relat_1(k6_relat_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_32])).

tff(c_1799,plain,(
    ! [A_157,A_158] : r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_157),A_158)),k6_relat_1(A_158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1735])).

tff(c_1811,plain,(
    ! [A_34,B_98] : r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_34),B_98)),k6_relat_1(k3_xboole_0(A_34,B_98))) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_1799])).

tff(c_2560,plain,(
    ! [B_98,A_34] : r1_tarski(k7_relat_1(k6_relat_1(B_98),A_34),k6_relat_1(k3_xboole_0(A_34,B_98))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_1811])).

tff(c_1998,plain,(
    ! [A_163,A_164] : k4_relat_1(k7_relat_1(k6_relat_1(A_163),A_164)) = k7_relat_1(k6_relat_1(A_164),A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1762])).

tff(c_2025,plain,(
    ! [A_34,B_98] : k7_relat_1(k6_relat_1(k3_xboole_0(A_34,B_98)),A_34) = k4_relat_1(k7_relat_1(k6_relat_1(A_34),B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_1998])).

tff(c_2048,plain,(
    ! [A_34,B_98] : k7_relat_1(k6_relat_1(k3_xboole_0(A_34,B_98)),A_34) = k7_relat_1(k6_relat_1(B_98),A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_2025])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k7_relat_1(C_12,k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    ! [B_84,A_85] :
      ( k3_xboole_0(B_84,k2_zfmisc_1(k1_relat_1(B_84),A_85)) = k8_relat_1(A_85,B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_267,plain,(
    ! [A_86,B_87] :
      ( v1_relat_1(k8_relat_1(A_86,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_8])).

tff(c_270,plain,(
    ! [A_13,A_66] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_13),A_66))
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_267])).

tff(c_272,plain,(
    ! [A_13,A_66] : v1_relat_1(k7_relat_1(k6_relat_1(A_13),A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_270])).

tff(c_763,plain,(
    ! [A_121,B_122,C_123] :
      ( k8_relat_1(A_121,k5_relat_1(B_122,C_123)) = k5_relat_1(B_122,k8_relat_1(A_121,C_123))
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_801,plain,(
    ! [B_14,A_121,A_13] :
      ( k5_relat_1(B_14,k8_relat_1(A_121,k6_relat_1(A_13))) = k8_relat_1(A_121,k8_relat_1(A_13,B_14))
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_763])).

tff(c_2284,plain,(
    ! [B_169,A_170,A_171] :
      ( k5_relat_1(B_169,k7_relat_1(k6_relat_1(A_170),A_171)) = k8_relat_1(A_170,k8_relat_1(A_171,B_169))
      | ~ v1_relat_1(B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_179,c_801])).

tff(c_2301,plain,(
    ! [A_170,A_171,A_40] :
      ( k8_relat_1(A_170,k8_relat_1(A_171,k6_relat_1(A_40))) = k7_relat_1(k7_relat_1(k6_relat_1(A_170),A_171),A_40)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_170),A_171))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2284,c_38])).

tff(c_2347,plain,(
    ! [A_170,A_171,A_40] : k8_relat_1(A_170,k7_relat_1(k6_relat_1(A_171),A_40)) = k7_relat_1(k7_relat_1(k6_relat_1(A_170),A_171),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_272,c_179,c_2301])).

tff(c_2305,plain,(
    ! [A_170,A_171,A_36] :
      ( r1_tarski(k8_relat_1(A_170,k8_relat_1(A_171,k6_relat_1(A_36))),k7_relat_1(k6_relat_1(A_170),A_171))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_170),A_171))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2284,c_32])).

tff(c_2349,plain,(
    ! [A_170,A_171,A_36] : r1_tarski(k8_relat_1(A_170,k7_relat_1(k6_relat_1(A_171),A_36)),k7_relat_1(k6_relat_1(A_170),A_171)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_272,c_179,c_2305])).

tff(c_11717,plain,(
    ! [A_338,A_339,A_340] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_338),A_339),A_340),k7_relat_1(k6_relat_1(A_338),A_339)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_2349])).

tff(c_11847,plain,(
    ! [A_338,A_10,B_11] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_338),k3_xboole_0(A_10,B_11)),k7_relat_1(k6_relat_1(A_338),A_10))
      | ~ v1_relat_1(k6_relat_1(A_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11717])).

tff(c_12102,plain,(
    ! [A_344,A_345,B_346] : r1_tarski(k7_relat_1(k6_relat_1(A_344),k3_xboole_0(A_345,B_346)),k7_relat_1(k6_relat_1(A_344),A_345)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_11847])).

tff(c_12230,plain,(
    ! [A_345,B_346] : r1_tarski(k6_relat_1(k3_xboole_0(A_345,B_346)),k7_relat_1(k6_relat_1(k3_xboole_0(A_345,B_346)),A_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_12102])).

tff(c_12261,plain,(
    ! [A_347,B_348] : r1_tarski(k6_relat_1(k3_xboole_0(A_347,B_348)),k7_relat_1(k6_relat_1(B_348),A_347)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_12230])).

tff(c_223,plain,(
    ! [B_77,A_78] :
      ( k5_relat_1(B_77,k6_relat_1(A_78)) = B_77
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_226,plain,(
    ! [A_34,A_78] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_78)) = k6_relat_1(A_34)
      | ~ r1_tarski(A_34,A_78)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_223])).

tff(c_228,plain,(
    ! [A_34,A_78] :
      ( k5_relat_1(k6_relat_1(A_34),k6_relat_1(A_78)) = k6_relat_1(A_34)
      | ~ r1_tarski(A_34,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_226])).

tff(c_1352,plain,(
    ! [A_78,A_34] :
      ( k5_relat_1(k6_relat_1(A_78),k6_relat_1(A_34)) = k4_relat_1(k6_relat_1(A_34))
      | ~ r1_tarski(A_34,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_1320])).

tff(c_1436,plain,(
    ! [A_149,A_150] :
      ( k5_relat_1(k6_relat_1(A_149),k6_relat_1(A_150)) = k6_relat_1(A_150)
      | ~ r1_tarski(A_150,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1352])).

tff(c_1509,plain,(
    ! [A_78,A_34] :
      ( k6_relat_1(A_78) = k6_relat_1(A_34)
      | ~ r1_tarski(A_78,A_34)
      | ~ r1_tarski(A_34,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_1436])).

tff(c_12263,plain,(
    ! [B_348,A_347] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(B_348),A_347)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_347,B_348)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_348),A_347),k6_relat_1(k3_xboole_0(A_347,B_348))) ) ),
    inference(resolution,[status(thm)],[c_12261,c_1509])).

tff(c_12341,plain,(
    ! [B_348,A_347] : k6_relat_1(k7_relat_1(k6_relat_1(B_348),A_347)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_347,B_348))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_12263])).

tff(c_129,plain,(
    ! [B_64,A_65] :
      ( k5_relat_1(B_64,k6_relat_1(A_65)) = k8_relat_1(A_65,B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k5_relat_1(B_37,k6_relat_1(A_36)),B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_139,plain,(
    ! [A_65,B_64] :
      ( r1_tarski(k8_relat_1(A_65,B_64),B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_34])).

tff(c_533,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k2_relat_1(A_110),k2_relat_1(B_111))
      | ~ r1_tarski(A_110,B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_542,plain,(
    ! [A_110,A_34] :
      ( r1_tarski(k2_relat_1(A_110),A_34)
      | ~ r1_tarski(A_110,k6_relat_1(A_34))
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_533])).

tff(c_836,plain,(
    ! [A_128,A_129] :
      ( r1_tarski(k2_relat_1(A_128),A_129)
      | ~ r1_tarski(A_128,k6_relat_1(A_129))
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_542])).

tff(c_36,plain,(
    ! [B_39,A_38] :
      ( k5_relat_1(B_39,k6_relat_1(A_38)) = B_39
      | ~ r1_tarski(k2_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_967,plain,(
    ! [A_137,A_138] :
      ( k5_relat_1(A_137,k6_relat_1(A_138)) = A_137
      | ~ r1_tarski(A_137,k6_relat_1(A_138))
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_836,c_36])).

tff(c_995,plain,(
    ! [A_65,A_138] :
      ( k5_relat_1(k8_relat_1(A_65,k6_relat_1(A_138)),k6_relat_1(A_138)) = k8_relat_1(A_65,k6_relat_1(A_138))
      | ~ v1_relat_1(k8_relat_1(A_65,k6_relat_1(A_138)))
      | ~ v1_relat_1(k6_relat_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_139,c_967])).

tff(c_3560,plain,(
    ! [A_210,A_211] : k5_relat_1(k7_relat_1(k6_relat_1(A_210),A_211),k6_relat_1(A_211)) = k7_relat_1(k6_relat_1(A_210),A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_272,c_179,c_179,c_179,c_995])).

tff(c_3586,plain,(
    ! [A_211,A_210] :
      ( k8_relat_1(A_211,k7_relat_1(k6_relat_1(A_210),A_211)) = k7_relat_1(k6_relat_1(A_210),A_211)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_210),A_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3560,c_12])).

tff(c_3677,plain,(
    ! [A_212,A_213] : k8_relat_1(A_212,k7_relat_1(k6_relat_1(A_213),A_212)) = k7_relat_1(k6_relat_1(A_213),A_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_3586])).

tff(c_3683,plain,(
    ! [A_213,A_212] : r1_tarski(k7_relat_1(k6_relat_1(A_213),A_212),k7_relat_1(k6_relat_1(A_212),A_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_2349])).

tff(c_3805,plain,(
    ! [A_215,A_216] : r1_tarski(k7_relat_1(k6_relat_1(A_215),A_216),k7_relat_1(k6_relat_1(A_216),A_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_2349])).

tff(c_3807,plain,(
    ! [A_216,A_215] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_216),A_215)) = k6_relat_1(k7_relat_1(k6_relat_1(A_215),A_216))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_216),A_215),k7_relat_1(k6_relat_1(A_215),A_216)) ) ),
    inference(resolution,[status(thm)],[c_3805,c_1509])).

tff(c_4042,plain,(
    ! [A_221,A_220] : k6_relat_1(k7_relat_1(k6_relat_1(A_221),A_220)) = k6_relat_1(k7_relat_1(k6_relat_1(A_220),A_221)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3683,c_3807])).

tff(c_4420,plain,(
    ! [A_220,A_221] : k2_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_220),A_221))) = k7_relat_1(k6_relat_1(A_221),A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_4042,c_28])).

tff(c_13156,plain,(
    ! [A_221,A_220] : k2_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_221,A_220)))) = k7_relat_1(k6_relat_1(A_221),A_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12341,c_4420])).

tff(c_13159,plain,(
    ! [A_221,A_220] : k7_relat_1(k6_relat_1(A_221),A_220) = k6_relat_1(k3_xboole_0(A_221,A_220)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_13156])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_169,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_46])).

tff(c_183,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169])).

tff(c_13667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13159,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.60/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.00  
% 8.60/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.00  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.60/3.00  
% 8.60/3.00  %Foreground sorts:
% 8.60/3.00  
% 8.60/3.00  
% 8.60/3.00  %Background operators:
% 8.60/3.00  
% 8.60/3.00  
% 8.60/3.00  %Foreground operators:
% 8.60/3.00  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.60/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.60/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.60/3.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.60/3.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.60/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.60/3.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.60/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.60/3.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.60/3.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.60/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.60/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.60/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.60/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.60/3.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.60/3.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.60/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.60/3.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.60/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.60/3.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.60/3.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.60/3.00  
% 8.60/3.02  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.60/3.02  tff(f_112, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.60/3.02  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 8.60/3.02  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 8.60/3.02  tff(f_88, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 8.60/3.02  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 8.60/3.02  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 8.60/3.02  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 8.60/3.02  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 8.60/3.02  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 8.60/3.02  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 8.60/3.02  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 8.60/3.02  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 8.60/3.02  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 8.60/3.02  tff(f_115, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 8.60/3.02  tff(c_28, plain, (![A_34]: (k2_relat_1(k6_relat_1(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.60/3.02  tff(c_42, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.60/3.02  tff(c_38, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.60/3.02  tff(c_152, plain, (![A_66, B_67]: (k5_relat_1(k6_relat_1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.60/3.02  tff(c_12, plain, (![B_14, A_13]: (k5_relat_1(B_14, k6_relat_1(A_13))=k8_relat_1(A_13, B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.02  tff(c_159, plain, (![A_13, A_66]: (k8_relat_1(A_13, k6_relat_1(A_66))=k7_relat_1(k6_relat_1(A_13), A_66) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_12])).
% 8.60/3.02  tff(c_179, plain, (![A_13, A_66]: (k8_relat_1(A_13, k6_relat_1(A_66))=k7_relat_1(k6_relat_1(A_13), A_66))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_159])).
% 8.60/3.02  tff(c_30, plain, (![A_35]: (k4_relat_1(k6_relat_1(A_35))=k6_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.60/3.02  tff(c_686, plain, (![B_116, A_117]: (k5_relat_1(k4_relat_1(B_116), k4_relat_1(A_117))=k4_relat_1(k5_relat_1(A_117, B_116)) | ~v1_relat_1(B_116) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.60/3.02  tff(c_695, plain, (![A_35, A_117]: (k5_relat_1(k6_relat_1(A_35), k4_relat_1(A_117))=k4_relat_1(k5_relat_1(A_117, k6_relat_1(A_35))) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_30, c_686])).
% 8.60/3.02  tff(c_1161, plain, (![A_141, A_142]: (k5_relat_1(k6_relat_1(A_141), k4_relat_1(A_142))=k4_relat_1(k5_relat_1(A_142, k6_relat_1(A_141))) | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_695])).
% 8.60/3.02  tff(c_1186, plain, (![A_35, A_141]: (k4_relat_1(k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_141)))=k5_relat_1(k6_relat_1(A_141), k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1161])).
% 8.60/3.02  tff(c_1320, plain, (![A_146, A_147]: (k4_relat_1(k5_relat_1(k6_relat_1(A_146), k6_relat_1(A_147)))=k5_relat_1(k6_relat_1(A_147), k6_relat_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1186])).
% 8.60/3.02  tff(c_1360, plain, (![A_13, A_146]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_146))=k4_relat_1(k8_relat_1(A_13, k6_relat_1(A_146))) | ~v1_relat_1(k6_relat_1(A_146)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1320])).
% 8.60/3.02  tff(c_1697, plain, (![A_155, A_156]: (k5_relat_1(k6_relat_1(A_155), k6_relat_1(A_156))=k4_relat_1(k7_relat_1(k6_relat_1(A_155), A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_179, c_1360])).
% 8.60/3.02  tff(c_1762, plain, (![A_40, A_156]: (k4_relat_1(k7_relat_1(k6_relat_1(A_40), A_156))=k7_relat_1(k6_relat_1(A_156), A_40) | ~v1_relat_1(k6_relat_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1697])).
% 8.60/3.02  tff(c_1796, plain, (![A_40, A_156]: (k4_relat_1(k7_relat_1(k6_relat_1(A_40), A_156))=k7_relat_1(k6_relat_1(A_156), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1762])).
% 8.60/3.02  tff(c_26, plain, (![A_34]: (k1_relat_1(k6_relat_1(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.60/3.02  tff(c_95, plain, (![A_55]: (k7_relat_1(A_55, k1_relat_1(A_55))=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.60/3.02  tff(c_104, plain, (![A_34]: (k7_relat_1(k6_relat_1(A_34), A_34)=k6_relat_1(A_34) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_95])).
% 8.60/3.02  tff(c_108, plain, (![A_34]: (k7_relat_1(k6_relat_1(A_34), A_34)=k6_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_104])).
% 8.60/3.02  tff(c_376, plain, (![C_96, A_97, B_98]: (k7_relat_1(k7_relat_1(C_96, A_97), B_98)=k7_relat_1(C_96, k3_xboole_0(A_97, B_98)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.60/3.02  tff(c_401, plain, (![A_34, B_98]: (k7_relat_1(k6_relat_1(A_34), k3_xboole_0(A_34, B_98))=k7_relat_1(k6_relat_1(A_34), B_98) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_376])).
% 8.60/3.02  tff(c_414, plain, (![A_34, B_98]: (k7_relat_1(k6_relat_1(A_34), k3_xboole_0(A_34, B_98))=k7_relat_1(k6_relat_1(A_34), B_98))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_401])).
% 8.60/3.02  tff(c_32, plain, (![A_36, B_37]: (r1_tarski(k5_relat_1(k6_relat_1(A_36), B_37), B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.60/3.02  tff(c_1735, plain, (![A_155, A_156]: (r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_155), A_156)), k6_relat_1(A_156)) | ~v1_relat_1(k6_relat_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_1697, c_32])).
% 8.60/3.02  tff(c_1799, plain, (![A_157, A_158]: (r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_157), A_158)), k6_relat_1(A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1735])).
% 8.60/3.02  tff(c_1811, plain, (![A_34, B_98]: (r1_tarski(k4_relat_1(k7_relat_1(k6_relat_1(A_34), B_98)), k6_relat_1(k3_xboole_0(A_34, B_98))))), inference(superposition, [status(thm), theory('equality')], [c_414, c_1799])).
% 8.60/3.02  tff(c_2560, plain, (![B_98, A_34]: (r1_tarski(k7_relat_1(k6_relat_1(B_98), A_34), k6_relat_1(k3_xboole_0(A_34, B_98))))), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_1811])).
% 8.60/3.02  tff(c_1998, plain, (![A_163, A_164]: (k4_relat_1(k7_relat_1(k6_relat_1(A_163), A_164))=k7_relat_1(k6_relat_1(A_164), A_163))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1762])).
% 8.60/3.02  tff(c_2025, plain, (![A_34, B_98]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_34, B_98)), A_34)=k4_relat_1(k7_relat_1(k6_relat_1(A_34), B_98)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_1998])).
% 8.60/3.02  tff(c_2048, plain, (![A_34, B_98]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_34, B_98)), A_34)=k7_relat_1(k6_relat_1(B_98), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_2025])).
% 8.60/3.02  tff(c_10, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k7_relat_1(C_12, k3_xboole_0(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.60/3.02  tff(c_250, plain, (![B_84, A_85]: (k3_xboole_0(B_84, k2_zfmisc_1(k1_relat_1(B_84), A_85))=k8_relat_1(A_85, B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.60/3.02  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.60/3.02  tff(c_267, plain, (![A_86, B_87]: (v1_relat_1(k8_relat_1(A_86, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_250, c_8])).
% 8.60/3.02  tff(c_270, plain, (![A_13, A_66]: (v1_relat_1(k7_relat_1(k6_relat_1(A_13), A_66)) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_267])).
% 8.60/3.02  tff(c_272, plain, (![A_13, A_66]: (v1_relat_1(k7_relat_1(k6_relat_1(A_13), A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_270])).
% 8.60/3.02  tff(c_763, plain, (![A_121, B_122, C_123]: (k8_relat_1(A_121, k5_relat_1(B_122, C_123))=k5_relat_1(B_122, k8_relat_1(A_121, C_123)) | ~v1_relat_1(C_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.60/3.02  tff(c_801, plain, (![B_14, A_121, A_13]: (k5_relat_1(B_14, k8_relat_1(A_121, k6_relat_1(A_13)))=k8_relat_1(A_121, k8_relat_1(A_13, B_14)) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(B_14) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_12, c_763])).
% 8.60/3.02  tff(c_2284, plain, (![B_169, A_170, A_171]: (k5_relat_1(B_169, k7_relat_1(k6_relat_1(A_170), A_171))=k8_relat_1(A_170, k8_relat_1(A_171, B_169)) | ~v1_relat_1(B_169))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_179, c_801])).
% 8.60/3.02  tff(c_2301, plain, (![A_170, A_171, A_40]: (k8_relat_1(A_170, k8_relat_1(A_171, k6_relat_1(A_40)))=k7_relat_1(k7_relat_1(k6_relat_1(A_170), A_171), A_40) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_170), A_171)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_2284, c_38])).
% 8.60/3.02  tff(c_2347, plain, (![A_170, A_171, A_40]: (k8_relat_1(A_170, k7_relat_1(k6_relat_1(A_171), A_40))=k7_relat_1(k7_relat_1(k6_relat_1(A_170), A_171), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_272, c_179, c_2301])).
% 8.60/3.02  tff(c_2305, plain, (![A_170, A_171, A_36]: (r1_tarski(k8_relat_1(A_170, k8_relat_1(A_171, k6_relat_1(A_36))), k7_relat_1(k6_relat_1(A_170), A_171)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_170), A_171)) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_2284, c_32])).
% 8.60/3.02  tff(c_2349, plain, (![A_170, A_171, A_36]: (r1_tarski(k8_relat_1(A_170, k7_relat_1(k6_relat_1(A_171), A_36)), k7_relat_1(k6_relat_1(A_170), A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_272, c_179, c_2305])).
% 8.60/3.02  tff(c_11717, plain, (![A_338, A_339, A_340]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_338), A_339), A_340), k7_relat_1(k6_relat_1(A_338), A_339)))), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_2349])).
% 8.60/3.02  tff(c_11847, plain, (![A_338, A_10, B_11]: (r1_tarski(k7_relat_1(k6_relat_1(A_338), k3_xboole_0(A_10, B_11)), k7_relat_1(k6_relat_1(A_338), A_10)) | ~v1_relat_1(k6_relat_1(A_338)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11717])).
% 8.60/3.02  tff(c_12102, plain, (![A_344, A_345, B_346]: (r1_tarski(k7_relat_1(k6_relat_1(A_344), k3_xboole_0(A_345, B_346)), k7_relat_1(k6_relat_1(A_344), A_345)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_11847])).
% 8.60/3.02  tff(c_12230, plain, (![A_345, B_346]: (r1_tarski(k6_relat_1(k3_xboole_0(A_345, B_346)), k7_relat_1(k6_relat_1(k3_xboole_0(A_345, B_346)), A_345)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_12102])).
% 8.60/3.02  tff(c_12261, plain, (![A_347, B_348]: (r1_tarski(k6_relat_1(k3_xboole_0(A_347, B_348)), k7_relat_1(k6_relat_1(B_348), A_347)))), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_12230])).
% 8.60/3.02  tff(c_223, plain, (![B_77, A_78]: (k5_relat_1(B_77, k6_relat_1(A_78))=B_77 | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.60/3.02  tff(c_226, plain, (![A_34, A_78]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_78))=k6_relat_1(A_34) | ~r1_tarski(A_34, A_78) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_223])).
% 8.60/3.02  tff(c_228, plain, (![A_34, A_78]: (k5_relat_1(k6_relat_1(A_34), k6_relat_1(A_78))=k6_relat_1(A_34) | ~r1_tarski(A_34, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_226])).
% 8.60/3.02  tff(c_1352, plain, (![A_78, A_34]: (k5_relat_1(k6_relat_1(A_78), k6_relat_1(A_34))=k4_relat_1(k6_relat_1(A_34)) | ~r1_tarski(A_34, A_78))), inference(superposition, [status(thm), theory('equality')], [c_228, c_1320])).
% 8.60/3.02  tff(c_1436, plain, (![A_149, A_150]: (k5_relat_1(k6_relat_1(A_149), k6_relat_1(A_150))=k6_relat_1(A_150) | ~r1_tarski(A_150, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1352])).
% 8.60/3.02  tff(c_1509, plain, (![A_78, A_34]: (k6_relat_1(A_78)=k6_relat_1(A_34) | ~r1_tarski(A_78, A_34) | ~r1_tarski(A_34, A_78))), inference(superposition, [status(thm), theory('equality')], [c_228, c_1436])).
% 8.60/3.02  tff(c_12263, plain, (![B_348, A_347]: (k6_relat_1(k7_relat_1(k6_relat_1(B_348), A_347))=k6_relat_1(k6_relat_1(k3_xboole_0(A_347, B_348))) | ~r1_tarski(k7_relat_1(k6_relat_1(B_348), A_347), k6_relat_1(k3_xboole_0(A_347, B_348))))), inference(resolution, [status(thm)], [c_12261, c_1509])).
% 8.60/3.02  tff(c_12341, plain, (![B_348, A_347]: (k6_relat_1(k7_relat_1(k6_relat_1(B_348), A_347))=k6_relat_1(k6_relat_1(k3_xboole_0(A_347, B_348))))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_12263])).
% 8.60/3.02  tff(c_129, plain, (![B_64, A_65]: (k5_relat_1(B_64, k6_relat_1(A_65))=k8_relat_1(A_65, B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.02  tff(c_34, plain, (![B_37, A_36]: (r1_tarski(k5_relat_1(B_37, k6_relat_1(A_36)), B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.60/3.02  tff(c_139, plain, (![A_65, B_64]: (r1_tarski(k8_relat_1(A_65, B_64), B_64) | ~v1_relat_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_129, c_34])).
% 8.60/3.02  tff(c_533, plain, (![A_110, B_111]: (r1_tarski(k2_relat_1(A_110), k2_relat_1(B_111)) | ~r1_tarski(A_110, B_111) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.60/3.02  tff(c_542, plain, (![A_110, A_34]: (r1_tarski(k2_relat_1(A_110), A_34) | ~r1_tarski(A_110, k6_relat_1(A_34)) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_28, c_533])).
% 8.60/3.02  tff(c_836, plain, (![A_128, A_129]: (r1_tarski(k2_relat_1(A_128), A_129) | ~r1_tarski(A_128, k6_relat_1(A_129)) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_542])).
% 8.60/3.02  tff(c_36, plain, (![B_39, A_38]: (k5_relat_1(B_39, k6_relat_1(A_38))=B_39 | ~r1_tarski(k2_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.60/3.02  tff(c_967, plain, (![A_137, A_138]: (k5_relat_1(A_137, k6_relat_1(A_138))=A_137 | ~r1_tarski(A_137, k6_relat_1(A_138)) | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_836, c_36])).
% 8.60/3.02  tff(c_995, plain, (![A_65, A_138]: (k5_relat_1(k8_relat_1(A_65, k6_relat_1(A_138)), k6_relat_1(A_138))=k8_relat_1(A_65, k6_relat_1(A_138)) | ~v1_relat_1(k8_relat_1(A_65, k6_relat_1(A_138))) | ~v1_relat_1(k6_relat_1(A_138)))), inference(resolution, [status(thm)], [c_139, c_967])).
% 8.60/3.02  tff(c_3560, plain, (![A_210, A_211]: (k5_relat_1(k7_relat_1(k6_relat_1(A_210), A_211), k6_relat_1(A_211))=k7_relat_1(k6_relat_1(A_210), A_211))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_272, c_179, c_179, c_179, c_995])).
% 8.60/3.02  tff(c_3586, plain, (![A_211, A_210]: (k8_relat_1(A_211, k7_relat_1(k6_relat_1(A_210), A_211))=k7_relat_1(k6_relat_1(A_210), A_211) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_210), A_211)))), inference(superposition, [status(thm), theory('equality')], [c_3560, c_12])).
% 8.60/3.02  tff(c_3677, plain, (![A_212, A_213]: (k8_relat_1(A_212, k7_relat_1(k6_relat_1(A_213), A_212))=k7_relat_1(k6_relat_1(A_213), A_212))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_3586])).
% 8.60/3.02  tff(c_3683, plain, (![A_213, A_212]: (r1_tarski(k7_relat_1(k6_relat_1(A_213), A_212), k7_relat_1(k6_relat_1(A_212), A_213)))), inference(superposition, [status(thm), theory('equality')], [c_3677, c_2349])).
% 8.60/3.02  tff(c_3805, plain, (![A_215, A_216]: (r1_tarski(k7_relat_1(k6_relat_1(A_215), A_216), k7_relat_1(k6_relat_1(A_216), A_215)))), inference(superposition, [status(thm), theory('equality')], [c_3677, c_2349])).
% 8.60/3.02  tff(c_3807, plain, (![A_216, A_215]: (k6_relat_1(k7_relat_1(k6_relat_1(A_216), A_215))=k6_relat_1(k7_relat_1(k6_relat_1(A_215), A_216)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_216), A_215), k7_relat_1(k6_relat_1(A_215), A_216)))), inference(resolution, [status(thm)], [c_3805, c_1509])).
% 8.60/3.02  tff(c_4042, plain, (![A_221, A_220]: (k6_relat_1(k7_relat_1(k6_relat_1(A_221), A_220))=k6_relat_1(k7_relat_1(k6_relat_1(A_220), A_221)))), inference(demodulation, [status(thm), theory('equality')], [c_3683, c_3807])).
% 8.60/3.02  tff(c_4420, plain, (![A_220, A_221]: (k2_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_220), A_221)))=k7_relat_1(k6_relat_1(A_221), A_220))), inference(superposition, [status(thm), theory('equality')], [c_4042, c_28])).
% 8.60/3.02  tff(c_13156, plain, (![A_221, A_220]: (k2_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_221, A_220))))=k7_relat_1(k6_relat_1(A_221), A_220))), inference(demodulation, [status(thm), theory('equality')], [c_12341, c_4420])).
% 8.60/3.02  tff(c_13159, plain, (![A_221, A_220]: (k7_relat_1(k6_relat_1(A_221), A_220)=k6_relat_1(k3_xboole_0(A_221, A_220)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_13156])).
% 8.60/3.02  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.60/3.02  tff(c_169, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_46])).
% 8.60/3.02  tff(c_183, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_169])).
% 8.60/3.02  tff(c_13667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13159, c_183])).
% 8.60/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.02  
% 8.60/3.02  Inference rules
% 8.60/3.02  ----------------------
% 8.60/3.02  #Ref     : 0
% 8.60/3.02  #Sup     : 3230
% 8.60/3.02  #Fact    : 0
% 8.60/3.02  #Define  : 0
% 8.60/3.02  #Split   : 2
% 8.60/3.02  #Chain   : 0
% 8.60/3.02  #Close   : 0
% 8.60/3.02  
% 8.60/3.02  Ordering : KBO
% 8.60/3.02  
% 8.60/3.02  Simplification rules
% 8.60/3.02  ----------------------
% 8.60/3.02  #Subsume      : 284
% 8.60/3.02  #Demod        : 3889
% 8.60/3.02  #Tautology    : 1135
% 8.60/3.02  #SimpNegUnit  : 0
% 8.60/3.02  #BackRed      : 94
% 8.60/3.02  
% 8.60/3.02  #Partial instantiations: 0
% 8.60/3.02  #Strategies tried      : 1
% 8.60/3.02  
% 8.60/3.02  Timing (in seconds)
% 8.60/3.02  ----------------------
% 8.60/3.02  Preprocessing        : 0.33
% 8.60/3.02  Parsing              : 0.18
% 8.60/3.02  CNF conversion       : 0.02
% 8.60/3.02  Main loop            : 1.87
% 8.60/3.02  Inferencing          : 0.52
% 8.60/3.02  Reduction            : 0.85
% 8.60/3.02  Demodulation         : 0.70
% 8.60/3.02  BG Simplification    : 0.08
% 8.60/3.02  Subsumption          : 0.31
% 8.60/3.02  Abstraction          : 0.11
% 8.60/3.02  MUC search           : 0.00
% 8.60/3.02  Cooper               : 0.00
% 8.60/3.02  Total                : 2.24
% 8.60/3.02  Index Insertion      : 0.00
% 8.60/3.02  Index Deletion       : 0.00
% 8.60/3.02  Index Matching       : 0.00
% 8.60/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
